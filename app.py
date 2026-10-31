"""Azzi Soft - local billing software (Sales: SO -> DN -> Invoice, Purchase: PO -> GRN -> Purchase Invoice).

Run:  python app.py   then open http://127.0.0.1:5000
Default login: admin / admin123  (change it after first login)
"""
import csv
import io
import json
import os
import re
import secrets
import sqlite3
from datetime import datetime, date, timedelta
from decimal import Decimal, ROUND_HALF_UP
from functools import wraps
from urllib.parse import parse_qs

import qrcode
import qrcode.image.svg
from flask import (Flask, Response, abort, flash, g, jsonify, redirect, render_template,
                   request, session, url_for)
from markupsafe import Markup
from werkzeug.middleware.proxy_fix import ProxyFix
from werkzeug.security import check_password_hash, generate_password_hash
from werkzeug.utils import secure_filename

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DB_PATH = os.path.join(BASE_DIR, "billing.db")
UPLOAD_DIR = os.path.join(BASE_DIR, "static", "uploads")
ENTITY_DIR = os.path.join(BASE_DIR, "entities")  # one database per business entity (the first one is billing.db)
KEY_FILE = os.path.join(BASE_DIR, ".secret_key")

DOC_TYPES = {"SO": "Sales Order", "DN": "Delivery Note", "INV": "Tax Invoice", "SR": "Credit Note",
             "PO": "Purchase Order", "GRN": "Goods Received Note", "PI": "Purchase Invoice", "PR": "Debit Note"}
SALES_FLOW = ("SO", "DN", "INV", "SR")
PURCHASE_FLOW = ("PO", "GRN", "PI", "PR")
UNPRICED = {"DN", "GRN"}  # quantity-only documents
# Units of measure offered in the item list; any other unit can still be typed.
UNITS = ["Nos", "Pcs", "Roll", "Ltr", "Box", "Kg", "g", "Ton", "Mtr", "cm", "mm", "Ft", "Inch", "Sqm", "Sqft",
         "Cbm", "ml", "Gallon", "Set", "Pair", "Dozen", "Pack", "Carton", "Bag", "Bundle", "Bottle", "Can",
         "Drum", "Pallet", "Reel", "Ream", "Sheet", "Each", "Unit", "Lot", "Lump Sum", "Hour", "Day", "Month", "Trip"]
# Workflow: each submitted document enables the next one in its flow.
NEXT_TYPE = {"SO": "DN", "DN": "INV", "INV": "SR", "PO": "GRN", "GRN": "PI", "PI": "PR"}
PREV_TYPE = {v: k for k, v in NEXT_TYPE.items()}
# GRNs / Delivery Notes can be made several times from one PO / SO, each for the quantity still pending
PARTIAL = {"DN", "GRN"}
# Credit Notes (sales returns) / Debit Notes (purchase returns) are made against an invoice, several times if needed, for the quantity not yet returned
RETURNS = {"SR", "PR"}
OPEN_TYPES = PARTIAL | RETURNS  # documents that take only the open (pending / returnable) quantity
# Posted (submitted) financial documents are final: never edited or deleted, corrected only by a Credit / Debit Note
# Documents that must state their payment terms (the rest copy them from their source)
TERMS_REQUIRED = {"SO", "PO", "INV", "PI"}
FINAL_TYPES = {"INV", "PI", "SR", "PR"}
# Party accounts: (debit doc type, credit doc type) - a customer owes for invoices less credit notes,
# a supplier is owed for purchase invoices less debit notes
ACCOUNT_DOCS = {"customer": ("INV", "SR"), "supplier": ("PR", "PI")}


def flow_of(doc_type):
    return PURCHASE_FLOW if doc_type in PURCHASE_FLOW else SALES_FLOW


def party_kind(doc_type):
    """Sales documents are made for customers, purchase documents for suppliers."""
    return "supplier" if doc_type in PURCHASE_FLOW else "customer"

DEFAULT_SETTINGS = {
    "company_name": "Smart Arabia Labels Technologies FZE LLC",
    "company_name_ar": "سمارت أرابيا ليبلز تكنولوجيز م.م.ح ذ.م.م",
    "address_lines": "SPC Free Zone.\nArea: Al Zahia ,Opp:Sheikh Mohammed Bin Zayed Rd\nP.O Box:73111\nEntrance No. 2 - Business Centre- Sharjah-UAE",
    "trn": "104813194800003",
    "bank_iban": "AE810860000009837041473",
    "bank_bic": "WIOBAEADXXX",
    "bank_name": "WIO Bank, Etihad Branch",
    "footer_note": "Label Quantity Tolerance:Due to thee nature of manufacturing process, we reserve the right to delivery and invoice .+-10% of the ordered quantity depending on customer final confimation",
    "footer_address": "P.O Box:73111\nSharjah Public City\nFree Zone, Al Zaiha\nArea",
    "email": "enquiry@arablabells.com",
    "website": "www.arablabelscom",
    "phone": "+971 68862776",
    "mobile": "+971 524253977",
    "currency": "AED",
    "vat_rate": "5",
    "so_prefix": "SALT-SO",
    "so_next": "1",
    "dn_prefix": "SALT",
    "dn_next": "677",
    "inv_prefix": "SALT-INV",
    "inv_next": "1",
    "item_prefix": "ITM",
    "item_next": "1",
    "po_prefix": "SALT-PO",
    "po_next": "1",
    "grn_prefix": "SALT-GRN",
    "grn_next": "1",
    "pi_prefix": "SALT-PI",
    "pi_next": "1",
    "sr_prefix": "SALT-CN",
    "sr_next": "1",
    "pr_prefix": "SALT-DBN",
    "pr_next": "1",
    "rv_prefix": "SALT-RV",
    "rv_next": "1",
    "pv_prefix": "SALT-PV",
    "pv_next": "1",
    "jv_prefix": "SALT-JV",
    "jv_next": "1",
    "se_prefix": "SALT-SE",
    "se_next": "1",
    "default_payment_terms": "Payment upon delivery",
    "default_payment_resp": "Payment responsibility with sales team",
    "default_dispatch": "Road",
    "logo": "",
    "stamp": "",
}

app = Flask(__name__)
if not os.path.exists(KEY_FILE):
    with open(KEY_FILE, "w") as f:
        f.write(secrets.token_hex(32))
with open(KEY_FILE) as f:
    app.secret_key = f.read().strip()
app.config["MAX_CONTENT_LENGTH"] = 5 * 1024 * 1024
if os.environ.get("BILLING_PROXY"):
    # on a server behind nginx: take the user's IP address and http / https from its X-Forwarded-* headers
    app.wsgi_app = ProxyFix(app.wsgi_app, x_for=1, x_proto=1, x_host=1)
if os.environ.get("BILLING_HTTPS"):
    app.config.update(SESSION_COOKIE_SECURE=True, SESSION_COOKIE_HTTPONLY=True, SESSION_COOKIE_SAMESITE="Lax")


# ---------------------------------------------------------------- database

def get_db():
    """The database of the business entity being worked in (chosen per request in load_user)."""
    if "db" not in g:
        g.db = sqlite3.connect(g.get("db_path") or DB_PATH, timeout=15)
        g.db.row_factory = sqlite3.Row
        # WAL (set in init_db) lets readers work while someone saves; these keep each connection quick
        g.db.executescript("""PRAGMA foreign_keys = ON; PRAGMA synchronous = NORMAL; PRAGMA cache_size = -32000;
                              PRAGMA temp_store = MEMORY; PRAGMA busy_timeout = 15000;""")
    return g.db


def main_db():
    """billing.db: logins, the business entities and who may open them. Commit right after writing here, since
    billing.db is also the first entity's database and get_db() may have it open too."""
    if "mdb" not in g:
        g.mdb = sqlite3.connect(DB_PATH, timeout=15)
        g.mdb.row_factory = sqlite3.Row
        g.mdb.execute("PRAGMA busy_timeout = 15000")
    return g.mdb


@app.teardown_appcontext
def close_db(_exc):
    for key in ("db", "mdb"):
        db = g.pop(key, None)
        if db is not None:
            db.close()


# ---------------------------------------------------------------- business entities
#
# Each business entity keeps everything in its own database: documents, numbering, stock, ledger and trial balance,
# chart of accounts, masters and settings. Nothing is shared, so entries can never mix. Users log in once (users
# live in billing.db, copied into every entity so names show on documents) and switch between the entities they
# are allowed to open.

USER_COLS = ("id", "username", "full_name", "password_hash", "role", "active", "created_at")

# ---------------------------------------------------------------- user setup: permissions, roles, password rules
#
# Access is a matrix: every function below has a level per role / user - 0 no access, 1 view only, 2 full (create,
# edit, post, cancel). A role gives its matrix to the users who get it; a user's own matrix can then be changed.
# An Administrator role has full access to everything, System administration included. need_for() decides what a
# page needs, and is used both to refuse requests and (url_ok) to hide links and buttons the user can't use.

MODULES = [("sales", "Sales"), ("purchase", "Procurement and sourcing"), ("accounts", "Accounts receivable and payable"),
           ("ledger", "General ledger"), ("inventory", "Inventory management"), ("reports", "Reports and logs")]
MODULE_KEYS = [k for k, _ in MODULES]
NO, VIEW, FULL = 0, 1, 2
# function key, module, name, has a full level (False: a report, view only)
FEATURES = [
    ("so", "sales", "Sales orders", True), ("dn", "sales", "Delivery notes", True), ("inv", "sales", "Tax invoices", True),
    ("sr", "sales", "Credit notes", True), ("customers", "sales", "Customer master", True),
    ("payment_terms", "sales", "Payment terms", True),
    ("po", "purchase", "Purchase orders", True), ("grn", "purchase", "Goods received notes (GRN)", True),
    ("pi", "purchase", "Purchase invoices", True), ("pr", "purchase", "Debit notes", True),
    ("vendors", "purchase", "Vendor master", True),
    ("receipt", "accounts", "Receipts", True), ("payment", "accounts", "Payments", True),
    ("balances", "accounts", "Customer / vendor balances, statements, aging", False),
    ("coa", "ledger", "Chart of accounts", True), ("jv", "ledger", "Journal vouchers", True),
    ("gl_reports", "ledger", "Journal, trial balance, profit and loss, ledgers", False),
    ("currencies", "ledger", "Currencies", True),
    ("fiscal", "ledger", "Fiscal calendar and period control", True),
    ("products", "inventory", "Products", True), ("stock", "inventory", "Stock summary, stock ledger, inventory transactions", False),
    ("stock_entries", "inventory", "Stock in / out and adjustments", True), ("warehouses", "inventory", "Warehouses", True),
    ("all_docs", "reports", "All documents", False), ("logs", "reports", "Transaction log", False),
]
FEATURE_KEYS = [f[0] for f in FEATURES]
PW_MIN = 8                 # minimum length of a new password
MAX_FAILED_LOGINS = 5      # wrong passwords in a row before the account locks
LOCK_MINUTES = 15          # a locked account opens again by itself after this, or when an admin unlocks it


def perms_from_modules(modules):
    """Full access to every function of the given modules (how roles / users made before the matrix are read)."""
    mods = set((modules or "").split(","))
    return {k: (FULL if full else VIEW) if m in mods else NO for k, m, _, full in FEATURES}


def perms_from_form(form):
    """The matrix as posted from a permission grid (select named perm_<function>)."""
    out = {}
    for k, _, _, full in FEATURES:
        v = form.get("perm_" + k, type=int) or NO
        out[k] = min(v, FULL if full else VIEW) if v in (NO, VIEW, FULL) else NO
    return out


def user_perms(user):
    if user["role"] == "admin":
        return {k: FULL for k in FEATURE_KEYS}
    try:
        saved = json.loads(user["perms"] or "{}")
    except ValueError:
        saved = {}
    return {k: int(saved.get(k, NO)) for k in FEATURE_KEYS}


def user_modules(user):
    perms = user_perms(user)
    return {m for k, m, _, _ in FEATURES if perms[k]}


def _doc_type_of(doc_id):
    cache = g.setdefault("doc_types", {})
    if doc_id not in cache:
        row = get_db().execute("SELECT doc_type FROM documents WHERE id = ?", (doc_id,)).fetchone()
        cache[doc_id] = row["doc_type"] if row else None
    return cache[doc_id]


def need_for(ep, va, args, method):
    """What a page needs: a list of (function, level), any one of them is enough; None if every user may open it."""
    write = method == "POST"
    lvl = FULL if write else VIEW
    va = va or {}
    doc_type = va.get("doc_type") or args.get("type")
    if va.get("doc_id"):
        doc_type = _doc_type_of(va["doc_id"])
    dt = (doc_type or "").lower()
    if ep in ("doc_view", "doc_print") and dt:
        return [(dt, VIEW)]
    if ep in ("doc_form", "doc_submit", "doc_delete", "invoice_select", "return_select", "note_request") and dt:
        return [(dt, FULL)]
    if ep == "documents":
        if doc_type in DOC_TYPES:
            return [(dt, FULL if args.get("new") else VIEW)]
        return [("all_docs", VIEW)]
    if ep in ("po_approvals", "po_approve", "po_reject"):
        return [("po", VIEW)]          # who may approve is decided by the approval workflow
    if ep == "po_recall":
        return [("po", FULL)]
    if ep == "customers":
        return [("customers", lvl)]
    if ep == "suppliers":
        return [("vendors", lvl)]
    if ep == "customer_delete":
        row = get_db().execute("SELECT kind FROM customers WHERE id = ?", (va.get("cid"),)).fetchone()
        return [("vendors" if row and row["kind"] == "supplier" else "customers", FULL)]
    if ep == "payments":
        return [("receipt" if va.get("kind") == "receipt" else "payment", VIEW)]
    if ep == "payment_new":
        return [("receipt" if va.get("kind") == "receipt" else "payment", FULL)]
    if ep in ("voucher", "voucher_cancel"):
        row = get_db().execute("SELECT kind FROM payments WHERE id = ?", (va.get("vid"),)).fetchone()
        return [("receipt" if row and row["kind"] == "receipt" else "payment", FULL if ep == "voucher_cancel" else VIEW)]
    simple = {
        "accounts": ("balances", VIEW), "aging_report": ("balances", VIEW), "statement": ("balances", VIEW),
        "payment_terms_page": ("payment_terms", lvl), "api_payment_term_add": ("payment_terms", FULL),
        "coa": ("coa", lvl), "currencies_page": ("currencies", lvl), "fiscal_calendar": ("fiscal", lvl),
        "journal": ("gl_reports", VIEW), "trial_balance": ("gl_reports", VIEW), "profit_loss": ("gl_reports", VIEW),
        "account_ledger": ("gl_reports", VIEW), "jv_new": ("jv", FULL), "jv_cancel": ("jv", FULL),
        "inventory": ("stock", VIEW), "stock_ledger": ("stock", VIEW), "inventory_transactions": ("stock", VIEW), "stock_adjust": ("stock_entries", FULL),
        "stock_move_delete": ("stock_entries", FULL), "stock_entries": ("stock_entries", VIEW),
        "stock_entry_view": ("stock_entries", VIEW), "stock_entry_new": ("stock_entries", FULL),
        "stock_entry_cancel": ("stock_entries", FULL), "products": ("products", lvl), "product_delete": ("products", FULL),
        "warehouses_page": ("warehouses", lvl), "billing_log": ("logs", VIEW),
    }
    if ep in simple:
        return [simple[ep]]
    if ep == "my_requests":
        return [("sr", VIEW), ("pr", VIEW)]
    if ep == "jv_view":
        return [("jv", VIEW), ("gl_reports", VIEW)]
    return None


def allowed(need, user=None):
    if need is None:
        return True
    perms = user_perms(user or g.user)
    return any(perms[f] >= l for f, l in need)


def url_ok(url, method="GET"):
    """May the current user use this link (or, with method POST, this form)?"""
    if not g.get("user"):
        return False
    path, _, query = url.partition("?")
    try:
        ep, va = app.url_map.bind("").match(path, method=method)
    except Exception:
        return True
    if getattr(app.view_functions[ep], "admin_only", False) and g.user["role"] != "admin":
        return False
    args = {k: v[0] for k, v in parse_qs(query).items()}
    return allowed(need_for(ep, va, args, method))


app.add_template_test(url_ok, "url_ok")


# ---------------------------------------------------------------- fiscal periods
#
# Every entry is checked against the period its date falls in: it can only be saved, posted, approved, cancelled or
# deleted while that period is Open and its module is not on hold. On hold can be lifted; Closed is permanent.
# Once an entity has a fiscal calendar, a date outside it is refused too.

PERIOD_MODULES = [("sales", "Sales"), ("purchase", "Procurement"), ("accounts", "AR / AP"), ("ledger", "General ledger"),
                  ("inventory", "Inventory")]
PERIOD_STATUSES = ("Open", "On hold", "Closed")


def add_months(d, n):
    y, m = divmod(d.month - 1 + n, 12)
    return date(d.year + y, m + 1, 1)


def add_fiscal_year(db, name, start, user_id):
    """A fiscal year of 12 monthly periods from start (the 1st of a month). Returns its id."""
    end = add_months(start, 12) - timedelta(days=1)
    yid = db.execute("INSERT INTO fiscal_years(name, start_date, end_date, created_by, created_at) VALUES (?,?,?,?,?)",
                     (name, start.isoformat(), end.isoformat(), user_id, now())).lastrowid
    for i in range(12):
        a = add_months(start, i)
        db.execute("""INSERT INTO fiscal_periods(year_id, seq, name, start_date, end_date) VALUES (?,?,?,?,?)""",
                   (yid, i + 1, f"P{i + 1:02d} · {a.strftime('%b %Y')}", a.isoformat(),
                    (add_months(a, 1) - timedelta(days=1)).isoformat()))
    return yid


def period_error(day, module):
    """Why an entry dated day can't be made in module now, or None."""
    db = get_db()
    if not day or not db.execute("SELECT 1 FROM fiscal_years").fetchone():
        return None
    p = db.execute("SELECT * FROM fiscal_periods WHERE ? BETWEEN start_date AND end_date", (day,)).fetchone()
    shown = ddmmyyyy(day)
    if p is None:
        return f"{shown} is outside the fiscal calendar. Create its fiscal year first (General ledger → Fiscal calendar)."
    if p["status"] != "Open":
        return f"Period {p['name']} is {p['status'].lower()}: no entries dated {shown} can be made."
    if p["hold_" + module]:
        return f"Period {p['name']} is on hold for {dict(PERIOD_MODULES)[module]}: no entries dated {shown} can be made."
    return None


def entry_period():
    """For a request that makes / changes an entry: (module, [dates it touches]); None for any other request."""
    ep, va, f, db = request.endpoint, request.view_args or {}, request.form, get_db()
    today = date.today().isoformat()

    def doc(doc_id):
        return db.execute("SELECT * FROM documents WHERE id = ?", (doc_id,)).fetchone()

    def doc_module(doc_type):
        return "purchase" if doc_type in PURCHASE_FLOW else "sales"

    def grn_dates(pi_id=None):  # landed cost goes onto the GRNs' stock cost, in their periods
        ids = [int(x) for v in request.values.getlist("from") for x in str(v).split(",") if x.strip().isdigit()]
        if pi_id:
            ids += [r[0] for r in db.execute("SELECT source_id FROM doc_sources WHERE doc_id = ?", (pi_id,))]
        return [r[0] for r in db.execute(f"SELECT doc_date FROM documents WHERE id IN ({','.join('?' * len(ids)) or 'NULL'})", ids)]

    if ep == "doc_form":
        old = doc(va["doc_id"]) if va.get("doc_id") else None
        doc_type = old["doc_type"] if old else va.get("doc_type")
        dates = [f.get("doc_date") or today] + ([old["doc_date"]] if old else [])
        if doc_type == "PI" and any(to_float(a) for a in f.getlist("lc_amount")):
            dates += grn_dates(old["id"] if old else None)
        return doc_module(doc_type), dates
    if ep in ("doc_submit", "doc_delete", "po_approve") and va.get("doc_id"):
        d = doc(va["doc_id"])
        if d is None:
            return None
        dates = [d["doc_date"]] + (grn_dates(d["id"]) if ep == "doc_submit" and d["doc_type"] == "PI" and d["landed_amount"] else [])
        return doc_module(d["doc_type"]), dates
    if ep == "payment_new":
        return "accounts", [f.get("pay_date") or today]
    if ep == "voucher_cancel":
        r = db.execute("SELECT pay_date FROM payments WHERE id = ?", (va.get("vid"),)).fetchone()
        return ("accounts", [r[0]]) if r else None
    if ep == "jv_new":
        return "ledger", [f.get("jv_date") or today]
    if ep == "jv_cancel":
        r = db.execute("SELECT jv_date FROM journals WHERE id = ?", (va.get("jid"),)).fetchone()
        return ("ledger", [r[0]]) if r else None
    if ep == "stock_entry_new":
        return "inventory", [f.get("se_date") or today]
    if ep == "stock_entry_cancel":
        r = db.execute("SELECT se_date FROM stock_entries WHERE id = ?", (va.get("eid"),)).fetchone()
        return ("inventory", [r[0]]) if r else None
    if ep == "stock_adjust":
        return "inventory", [f.get("move_date") or today]
    if ep == "stock_move_delete":
        r = db.execute("SELECT move_date FROM stock_moves WHERE id = ?", (va.get("mid"),)).fetchone()
        return ("inventory", [r[0]]) if r else None
    return None


def perm_summary(perms):
    """Per module with any access: (module name, 'full' / 'view' / 'partly')."""
    out = []
    for m, title in MODULES:
        lv = [perms[k] for k, fm, _, full in FEATURES if fm == m]
        tops = [FULL if full else VIEW for _, fm, _, full in FEATURES if fm == m]
        if max(lv):
            out.append((title, "full" if lv == tops else "view" if max(lv) == VIEW and all(lv) else "partly"))
    return out


def perms_text(perms):
    """Short description of a matrix for the activity log."""
    names = {k: n for k, _, n, _ in FEATURES}
    full = [names[k] for k in FEATURE_KEYS if perms[k] == FULL]
    view = [names[k] for k in FEATURE_KEYS if perms[k] == VIEW]
    return "; ".join(x for x in (f"full: {', '.join(full)}" if full else "", f"view only: {', '.join(view)}" if view else "") if x) \
        or "none"


def password_problem(pw):
    if len(pw) < PW_MIN:
        return f"The password must be at least {PW_MIN} characters."
    if pw.isalpha() or pw.isdigit():
        return "The password must mix letters with digits or symbols."
    return None


def save_user_photo(file, uid):
    ext = os.path.splitext(secure_filename(file.filename))[1].lower()
    if ext not in (".png", ".jpg", ".jpeg", ".gif", ".webp"):
        return None
    os.makedirs(os.path.join(UPLOAD_DIR, "users"), exist_ok=True)
    name = f"users/user_{uid}{ext}"
    file.save(os.path.join(UPLOAD_DIR, name))
    return f"{name}?v={int(datetime.now().timestamp())}"


def entity_path(ent):
    return os.path.join(BASE_DIR, ent["db_file"])


def all_entities(active_only=False):
    return main_db().execute("SELECT * FROM entities" + (" WHERE active = 1" if active_only else "") + " ORDER BY id").fetchall()


def user_entities(user):
    """The active entities a user may open: every one for an admin, the assigned ones for others."""
    if user["role"] == "admin":
        return all_entities(active_only=True)
    return main_db().execute("""SELECT e.* FROM entities e JOIN user_entities u ON u.entity_id = e.id
                                WHERE u.user_id = ? AND e.active = 1 ORDER BY e.id""", (user["id"],)).fetchall()


def use_entity(ent):
    """Work in this entity for the rest of the request."""
    old = g.pop("db", None)
    if old is not None:
        old.close()
    for key in ("settings", "currencies"):
        g.pop(key, None)
    g.entity, g.db_path = ent, entity_path(ent)
    session["entity"] = ent["id"]


def sync_users():
    """Copy the logins from billing.db into every other entity's database."""
    users = [tuple(r) for r in main_db().execute(f"SELECT {', '.join(USER_COLS)} FROM users")]
    for ent in all_entities():
        if os.path.abspath(entity_path(ent)) == os.path.abspath(DB_PATH) or not os.path.exists(entity_path(ent)):
            continue
        db = sqlite3.connect(entity_path(ent), timeout=15)
        db.execute("DELETE FROM users")
        db.executemany(f"INSERT INTO users({', '.join(USER_COLS)}) VALUES ({', '.join('?' * len(USER_COLS))})", users)
        db.commit()
        db.close()


def copy_table(db, table, where=""):
    """Replace a table of db with the attached source database's rows (columns both have)."""
    mine = [r[1] for r in db.execute(f"PRAGMA table_info({table})")]
    theirs = {r[1] for r in db.execute(f"PRAGMA src.table_info({table})")}
    cols = ", ".join(c for c in mine if c in theirs)
    db.execute(f"DELETE FROM {table}")
    db.execute(f"INSERT INTO {table}({cols}) SELECT {cols} FROM src.{table} {where}")


DOC_PREFIX_SUFFIX = {"so": "SO", "dn": "DN", "inv": "INV", "po": "PO", "grn": "GRN", "pi": "PI", "sr": "CN",
                     "pr": "DBN", "rv": "RV", "pv": "PV", "jv": "JV", "se": "SE"}


def create_entity(code, profile, currency, source, copy):
    """Make a new entity's database, starting from the source entity's settings and (optionally) its masters."""
    os.makedirs(ENTITY_DIR, exist_ok=True)
    db_file = f"entities/{code.lower()}.db"
    path = os.path.join(BASE_DIR, db_file)
    src_settings = {r["key"]: r["value"] for r in get_db().execute("SELECT key, value FROM settings")}
    seed = {k: v for k, v in src_settings.items() if k not in ("gl_version", "default_warehouse", "logo", "stamp")}
    seed.update({k: "1" for k in seed if k.endswith("_next")})
    seed.update({f"{k}_prefix": f"{code}-{v}" for k, v in DOC_PREFIX_SUFFIX.items()})
    seed.update({k: profile.get(k, "") for k in PROFILE_KEYS}, currency=currency)
    db = sqlite3.connect(path)
    db.execute("CREATE TABLE IF NOT EXISTS settings (key TEXT PRIMARY KEY, value TEXT)")
    db.executemany("INSERT OR REPLACE INTO settings(key, value) VALUES (?, ?)", seed.items())
    db.commit()
    db.close()
    init_db(path)
    if copy:
        db = sqlite3.connect(path)
        db.execute("ATTACH DATABASE ? AS src", (entity_path(source),))
        if "coa" in copy:
            copy_table(db, "coa")
        if "products" in copy:
            copy_table(db, "warehouses")
            copy_table(db, "products")
            db.execute("UPDATE products SET stock_qty = 0, avg_cost = 0")  # no stock yet in the new entity
            db.execute("UPDATE settings SET value = ? WHERE key = 'default_warehouse'", (src_settings.get("default_warehouse"),))
            db.execute("UPDATE settings SET value = ? WHERE key = 'item_next'", (src_settings.get("item_next", "1"),))
        if "parties" in copy:
            copy_table(db, "customers")
        if "terms" in copy:
            copy_table(db, "payment_terms")
            if currency == src_settings.get("currency"):  # rates are against the base currency
                copy_table(db, "currencies")
        db.commit()
        db.execute("DETACH DATABASE src")
        db.close()
    mdb = main_db()
    eid = mdb.execute("INSERT INTO entities(code, name, db_file, active, created_at) VALUES (?,?,?,1,?)",
                      (code, profile["company_name"], db_file, now())).lastrowid
    mdb.commit()
    sync_users()
    return eid


def now():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def init_db(path=DB_PATH):
    db = sqlite3.connect(path)
    db.executescript("""
    CREATE TABLE IF NOT EXISTS users (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        username TEXT UNIQUE NOT NULL,
        full_name TEXT NOT NULL DEFAULT '',
        password_hash TEXT NOT NULL,
        role TEXT NOT NULL DEFAULT 'user',
        active INTEGER NOT NULL DEFAULT 1,
        created_at TEXT NOT NULL
    );
    CREATE TABLE IF NOT EXISTS settings (key TEXT PRIMARY KEY, value TEXT);
    CREATE TABLE IF NOT EXISTS customers (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        name TEXT NOT NULL, area TEXT DEFAULT '', po_box TEXT DEFAULT '',
        contact TEXT DEFAULT '', trn TEXT DEFAULT '', attention TEXT DEFAULT '',
        kind TEXT NOT NULL DEFAULT 'customer', created_at TEXT NOT NULL
    );
    CREATE TABLE IF NOT EXISTS documents (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        doc_type TEXT NOT NULL, doc_no TEXT UNIQUE NOT NULL, doc_date TEXT NOT NULL,
        customer_id INTEGER, cust_name TEXT, cust_area TEXT, cust_po_box TEXT,
        cust_contact TEXT, cust_trn TEXT, buyer TEXT, attention TEXT, lpo_no TEXT,
        delivery_location TEXT, payment_terms TEXT, payment_resp TEXT,
        dispatch_mode TEXT, goods_desc TEXT, notes TEXT,
        vat_rate REAL DEFAULT 0, subtotal REAL DEFAULT 0, vat_amount REAL DEFAULT 0,
        total REAL DEFAULT 0, total_qty REAL DEFAULT 0,
        discount_type TEXT DEFAULT 'amount', discount_value REAL DEFAULT 0, discount_amount REAL DEFAULT 0,
        supplier_do_no TEXT DEFAULT '', supplier_do_date TEXT DEFAULT '',
        status TEXT NOT NULL DEFAULT 'Draft', parent_id INTEGER REFERENCES documents(id),
        submitted_by INTEGER, submitted_at TEXT,
        created_by INTEGER, created_at TEXT, updated_by INTEGER, updated_at TEXT
    );
    CREATE TABLE IF NOT EXISTS items (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        document_id INTEGER NOT NULL REFERENCES documents(id) ON DELETE CASCADE,
        sl INTEGER, title TEXT, details TEXT, rolls REAL, per_roll REAL,
        qty REAL, unit TEXT DEFAULT '', rate REAL, amount REAL, vat REAL DEFAULT 0, line_total REAL DEFAULT 0
    );
    CREATE TABLE IF NOT EXISTS products (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        code TEXT UNIQUE NOT NULL, name TEXT NOT NULL, details TEXT DEFAULT '', unit TEXT DEFAULT '',
        sale_price REAL DEFAULT 0, purchase_price REAL DEFAULT 0, active INTEGER NOT NULL DEFAULT 1,
        created_by INTEGER, created_at TEXT
    );
    CREATE TABLE IF NOT EXISTS gl_lines (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        dt TEXT NOT NULL, seq TEXT, src TEXT NOT NULL, rk TEXT NOT NULL, rid INTEGER NOT NULL, no TEXT, narration TEXT,
        account_id INTEGER NOT NULL, debit REAL DEFAULT 0, credit REAL DEFAULT 0, party_id INTEGER, link_id INTEGER
    );
    CREATE TABLE IF NOT EXISTS coa (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        code TEXT UNIQUE NOT NULL, name TEXT NOT NULL, type TEXT NOT NULL, parent_id INTEGER,
        is_group INTEGER NOT NULL DEFAULT 0, system_key TEXT UNIQUE, active INTEGER NOT NULL DEFAULT 1, created_at TEXT
    );
    CREATE TABLE IF NOT EXISTS journals (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        jv_no TEXT UNIQUE NOT NULL, jv_date TEXT NOT NULL, narration TEXT NOT NULL, status TEXT NOT NULL DEFAULT 'Posted',
        cancel_reason TEXT DEFAULT '', cancelled_by INTEGER, cancelled_at TEXT, created_by INTEGER, created_at TEXT
    );
    CREATE TABLE IF NOT EXISTS journal_lines (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        journal_id INTEGER NOT NULL, account_id INTEGER NOT NULL, debit REAL DEFAULT 0, credit REAL DEFAULT 0,
        narration TEXT DEFAULT '', party_id INTEGER
    );
    CREATE TABLE IF NOT EXISTS payments (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        kind TEXT NOT NULL, voucher_no TEXT UNIQUE NOT NULL, party_id INTEGER NOT NULL, pay_date TEXT NOT NULL,
        amount REAL NOT NULL, mode TEXT DEFAULT 'Cash', reference TEXT DEFAULT '', bank TEXT DEFAULT '',
        cheque_date TEXT DEFAULT '', notes TEXT DEFAULT '', status TEXT NOT NULL DEFAULT 'Posted',
        cancel_reason TEXT DEFAULT '', cancelled_by INTEGER, cancelled_at TEXT,
        created_by INTEGER, created_at TEXT NOT NULL
    );
    CREATE TABLE IF NOT EXISTS payment_allocations (
        payment_id INTEGER NOT NULL, document_id INTEGER NOT NULL, amount REAL NOT NULL
    );
    CREATE TABLE IF NOT EXISTS note_requests (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        doc_type TEXT NOT NULL, invoice_id INTEGER NOT NULL, user_id INTEGER NOT NULL, reason TEXT NOT NULL,
        status TEXT NOT NULL DEFAULT 'Pending', admin_id INTEGER, admin_remark TEXT DEFAULT '', decided_at TEXT,
        note_id INTEGER, created_at TEXT NOT NULL
    );
    CREATE TABLE IF NOT EXISTS po_wf_steps (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        seq INTEGER NOT NULL, name TEXT NOT NULL, min_amount REAL NOT NULL DEFAULT 0, approvers TEXT NOT NULL DEFAULT ''
    );
    CREATE TABLE IF NOT EXISTS po_workflow (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        doc_id INTEGER NOT NULL, action TEXT NOT NULL, step_name TEXT DEFAULT '', user_id INTEGER, remark TEXT DEFAULT '',
        at TEXT NOT NULL
    );
    CREATE TABLE IF NOT EXISTS doc_sources (
        doc_id INTEGER NOT NULL, source_id INTEGER NOT NULL, PRIMARY KEY (doc_id, source_id)
    );
    CREATE TABLE IF NOT EXISTS stock_moves (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        product_id INTEGER NOT NULL, document_id INTEGER, move_date TEXT NOT NULL,
        kind TEXT NOT NULL, ref TEXT DEFAULT '', note TEXT DEFAULT '',
        qty REAL NOT NULL, unit_cost REAL DEFAULT 0, value REAL DEFAULT 0,
        balance_qty REAL DEFAULT 0, avg_cost REAL DEFAULT 0, fixed_cost INTEGER DEFAULT 0,
        created_by INTEGER, created_at TEXT
    );
    CREATE INDEX IF NOT EXISTS idx_moves_product ON stock_moves(product_id, move_date, id);
    CREATE TABLE IF NOT EXISTS logs (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER, username TEXT, action TEXT, details TEXT,
        ip TEXT, created_at TEXT
    );
    """)
    # Upgrade databases created before per-line VAT existed
    cols = {r[1] for r in db.execute("PRAGMA table_info(items)")}
    for col in ("vat", "line_total"):
        if col not in cols:
            db.execute(f"ALTER TABLE items ADD COLUMN {col} REAL DEFAULT 0")
    for col in ("product_id INTEGER", "code TEXT DEFAULT ''"):
        if col.split()[0] not in cols:
            db.execute(f"ALTER TABLE items ADD COLUMN {col}")
    if "source_item_id" not in cols:
        db.execute("ALTER TABLE items ADD COLUMN source_item_id INTEGER")
        # documents made before this existed copied their parent's lines in order: link them by line number
        db.execute("""UPDATE items SET source_item_id = (
                          SELECT pi.id FROM items pi JOIN documents c ON c.id = items.document_id
                          WHERE pi.document_id = c.parent_id AND pi.sl = items.sl)
                      WHERE document_id IN (SELECT id FROM documents WHERE parent_id IS NOT NULL)""")
    for col in ("disc_pct", "disc_amt"):  # line discount: percent, and amount off each unit's price
        if col not in cols:
            db.execute(f"ALTER TABLE items ADD COLUMN {col} REAL DEFAULT 0")
    if "unit" not in cols:  # items saved before units existed were counted in pieces
        db.execute("ALTER TABLE items ADD COLUMN unit TEXT DEFAULT ''")
        db.execute("UPDATE items SET unit = 'Pcs'")
    db.execute("UPDATE items SET vat = ROUND(amount * (SELECT vat_rate FROM documents d WHERE d.id = document_id) / 100, 2), "
               "line_total = amount + ROUND(amount * (SELECT vat_rate FROM documents d WHERE d.id = document_id) / 100, 2) "
               "WHERE line_total = 0 AND amount > 0")
    db.execute("""INSERT OR IGNORE INTO doc_sources(doc_id, source_id)
                  SELECT id, parent_id FROM documents WHERE doc_type IN ('INV', 'PI') AND parent_id IS NOT NULL""")
    prod_cols = {r[1] for r in db.execute("PRAGMA table_info(products)")}
    if "fixed_cost" not in {r[1] for r in db.execute("PRAGMA table_info(stock_moves)")}:
        db.execute("ALTER TABLE stock_moves ADD COLUMN fixed_cost INTEGER DEFAULT 0")
    for col in ("stock_qty", "avg_cost"):
        if col not in prod_cols:
            db.execute(f"ALTER TABLE products ADD COLUMN {col} REAL DEFAULT 0")
    if "kind" not in {r[1] for r in db.execute("PRAGMA table_info(customers)")}:
        db.execute("ALTER TABLE customers ADD COLUMN kind TEXT NOT NULL DEFAULT 'customer'")
    party_cols = {r[1] for r in db.execute("PRAGMA table_info(customers)")}
    for col in ("entity_code", "account_no", "country", "contact_name", "email"):
        if col not in party_cols:
            db.execute(f"ALTER TABLE customers ADD COLUMN {col} TEXT DEFAULT ''")
    for pid, kind in db.execute("SELECT id, kind FROM customers WHERE COALESCE(account_no, '') = '' ORDER BY id").fetchall():
        db.execute("UPDATE customers SET account_no = ? WHERE id = ?", (next_account_no(db, kind), pid))
    db.execute("""UPDATE documents SET customer_id = (SELECT c.id FROM customers c WHERE lower(c.name) = lower(documents.cust_name)
                      AND c.kind = CASE WHEN documents.doc_type IN ('PO', 'GRN', 'PI', 'PR') THEN 'supplier' ELSE 'customer' END)
                  WHERE customer_id IS NULL"""),
    doc_cols = {r[1] for r in db.execute("PRAGMA table_info(documents)")}
    for col, decl in (("discount_type", "TEXT DEFAULT 'amount'"), ("discount_value", "REAL DEFAULT 0"),
                      ("discount_amount", "REAL DEFAULT 0"), ("supplier_do_no", "TEXT DEFAULT ''"),
                      ("supplier_do_date", "TEXT DEFAULT ''"), ("supplier_inv_no", "TEXT DEFAULT ''"),
                      ("supplier_inv_date", "TEXT DEFAULT ''")):
        if col not in doc_cols:
            db.execute(f"ALTER TABLE documents ADD COLUMN {col} {decl}")
    db.execute("""CREATE TABLE IF NOT EXISTS warehouses (
                      id INTEGER PRIMARY KEY AUTOINCREMENT, code TEXT UNIQUE NOT NULL, name TEXT NOT NULL,
                      location TEXT DEFAULT '', active INTEGER NOT NULL DEFAULT 1, created_at TEXT)""")
    if not db.execute("SELECT 1 FROM warehouses").fetchone():
        db.execute("INSERT INTO warehouses(code, name, created_at) VALUES ('MAIN', 'Main Warehouse', ?)", (now(),))
    db.execute("""INSERT OR IGNORE INTO settings(key, value)
                  SELECT 'default_warehouse', CAST(MIN(id) AS TEXT) FROM warehouses""")
    main_wh = int(db.execute("SELECT value FROM settings WHERE key = 'default_warehouse'").fetchone()[0])
    for table in ("documents", "stock_moves"):
        if "warehouse_id" not in {r[1] for r in db.execute(f"PRAGMA table_info({table})")}:
            db.execute(f"ALTER TABLE {table} ADD COLUMN warehouse_id INTEGER")
        db.execute(f"UPDATE {table} SET warehouse_id = ? WHERE warehouse_id IS NULL", (main_wh,))
    if "warehouse_id" not in {r[1] for r in db.execute("PRAGMA table_info(items)")}:
        db.execute("ALTER TABLE items ADD COLUMN warehouse_id INTEGER")
    db.execute("""UPDATE items SET warehouse_id = (SELECT d.warehouse_id FROM documents d WHERE d.id = items.document_id)
                  WHERE warehouse_id IS NULL""")
    db.execute("CREATE INDEX IF NOT EXISTS idx_moves_wh ON stock_moves(warehouse_id, product_id)")
    # stock entries: Stock In / Stock Out vouchers with their own journal against a chosen account
    db.executescript("""
    CREATE TABLE IF NOT EXISTS stock_entries (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        se_no TEXT UNIQUE NOT NULL, se_date TEXT NOT NULL, kind TEXT NOT NULL, warehouse_id INTEGER NOT NULL,
        account_id INTEGER NOT NULL, narration TEXT NOT NULL, status TEXT NOT NULL DEFAULT 'Posted',
        cancel_reason TEXT DEFAULT '', cancelled_by INTEGER, cancelled_at TEXT, created_by INTEGER, created_at TEXT
    );
    CREATE TABLE IF NOT EXISTS stock_entry_lines (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        entry_id INTEGER NOT NULL, product_id INTEGER NOT NULL, qty REAL NOT NULL, unit_cost REAL, note TEXT DEFAULT '',
        move_id INTEGER
    );""")
    if "entry_id" not in {r[1] for r in db.execute("PRAGMA table_info(stock_moves)")}:
        db.execute("ALTER TABLE stock_moves ADD COLUMN entry_id INTEGER")
    db.execute("CREATE INDEX IF NOT EXISTS idx_moves_entry ON stock_moves(entry_id)")
    # each document move knows its line (inventory transactions show it line by line, with that line's invoice)
    if "item_id" not in {r[1] for r in db.execute("PRAGMA table_info(stock_moves)")}:
        db.execute("ALTER TABLE stock_moves ADD COLUMN item_id INTEGER")
        # moves were written one per line in line order: pair them up the same way
        for (doc_id,) in db.execute("SELECT DISTINCT document_id FROM stock_moves WHERE document_id IS NOT NULL").fetchall():
            moves = db.execute("SELECT id, product_id FROM stock_moves WHERE document_id = ? ORDER BY id", (doc_id,)).fetchall()
            lines = db.execute("""SELECT id, product_id FROM items WHERE document_id = ? AND product_id IS NOT NULL AND qty != 0
                                  ORDER BY id""", (doc_id,)).fetchall()
            for (mid, mp), (iid, ip) in zip(moves, lines):
                if mp == ip:
                    db.execute("UPDATE stock_moves SET item_id = ? WHERE id = ?", (iid, mid))
    db.execute("CREATE INDEX IF NOT EXISTS idx_moves_item ON stock_moves(item_id)")
    # fiscal calendar: years split into periods, each Open / On hold / Closed, with a hold per module
    db.executescript("""
    CREATE TABLE IF NOT EXISTS fiscal_years (
        id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT UNIQUE NOT NULL, start_date TEXT NOT NULL, end_date TEXT NOT NULL,
        created_by INTEGER, created_at TEXT);
    CREATE TABLE IF NOT EXISTS fiscal_periods (
        id INTEGER PRIMARY KEY AUTOINCREMENT, year_id INTEGER NOT NULL, seq INTEGER NOT NULL, name TEXT NOT NULL,
        start_date TEXT NOT NULL, end_date TEXT NOT NULL, status TEXT NOT NULL DEFAULT 'Open',
        hold_sales INTEGER DEFAULT 0, hold_purchase INTEGER DEFAULT 0, hold_accounts INTEGER DEFAULT 0,
        hold_ledger INTEGER DEFAULT 0, hold_inventory INTEGER DEFAULT 0, updated_by INTEGER, updated_at TEXT);
    CREATE INDEX IF NOT EXISTS idx_fp_dates ON fiscal_periods(start_date, end_date);""")
    if not db.execute("SELECT 1 FROM fiscal_years").fetchone():
        # control starts with calendar years covering every existing entry and this year, all open
        first = db.execute("""SELECT MIN(d) FROM (SELECT MIN(doc_date) AS d FROM documents UNION ALL SELECT MIN(pay_date) FROM payments
                              UNION ALL SELECT MIN(jv_date) FROM journals UNION ALL SELECT MIN(move_date) FROM stock_moves
                              UNION ALL SELECT MIN(se_date) FROM stock_entries)""").fetchone()[0]
        for year in range(int((first or date.today().isoformat())[:4]), date.today().year + 1):
            add_fiscal_year(db, f"FY{year}", date(year, 1, 1), None)
    # currencies: documents keep their own currency and rate, plus their total and VAT in the base currency
    base_cur = db.execute("SELECT value FROM settings WHERE key = 'currency'").fetchone()
    base_cur = (base_cur[0] if base_cur else "AED") or "AED"
    db.execute("""CREATE TABLE IF NOT EXISTS currencies (code TEXT PRIMARY KEY, name TEXT NOT NULL,
                  rate REAL NOT NULL DEFAULT 1, active INTEGER NOT NULL DEFAULT 1, updated_at TEXT)""")
    db.execute("INSERT OR IGNORE INTO currencies(code, name, rate, updated_at) VALUES (?, ?, 1, ?)",
               (base_cur, "UAE Dirham" if base_cur == "AED" else base_cur, now()))
    if base_cur == "AED":  # the dirham is pegged to the US dollar
        db.execute("INSERT OR IGNORE INTO currencies(code, name, rate, updated_at) VALUES ('USD', 'US Dollar', 3.6725, ?)",
                   (now(),))
    doc_cols = {r[1] for r in db.execute("PRAGMA table_info(documents)")}
    for col, decl in (("currency", "TEXT"), ("exchange_rate", "REAL DEFAULT 1"), ("base_total", "REAL"), ("base_vat", "REAL")):
        if col not in doc_cols:
            db.execute(f"ALTER TABLE documents ADD COLUMN {col} {decl}")
    db.execute("""UPDATE documents SET currency = COALESCE(currency, ?), exchange_rate = COALESCE(exchange_rate, 1),
                  base_total = COALESCE(base_total, total), base_vat = COALESCE(base_vat, vat_amount)
                  WHERE currency IS NULL OR base_total IS NULL OR base_vat IS NULL""", (base_cur,))
    if "currency" not in {r[1] for r in db.execute("PRAGMA table_info(customers)")}:
        db.execute("ALTER TABLE customers ADD COLUMN currency TEXT DEFAULT ''")
    db.execute("UPDATE customers SET currency = ? WHERE COALESCE(currency, '') = ''", (base_cur,))
    if "receipt_date" not in {r[1] for r in db.execute("PRAGMA table_info(documents)")}:
        db.execute("ALTER TABLE documents ADD COLUMN receipt_date TEXT DEFAULT ''")  # PO: requested receipt date
    if "wf_step" not in {r[1] for r in db.execute("PRAGMA table_info(documents)")}:
        db.execute("ALTER TABLE documents ADD COLUMN wf_step INTEGER")  # PO approval step it is waiting at
    # landed cost: extra charges (freight, customs...) on a Purchase Invoice, billed by the vendor without VAT and
    # added to the stock cost of the received goods, an equal share per invoice line
    if "landed_amount" not in {r[1] for r in db.execute("PRAGMA table_info(documents)")}:
        db.execute("ALTER TABLE documents ADD COLUMN landed_amount REAL DEFAULT 0")  # document currency
    if "landed" not in {r[1] for r in db.execute("PRAGMA table_info(items)")}:
        db.execute("ALTER TABLE items ADD COLUMN landed REAL DEFAULT 0")  # this line's share, in base currency
    db.execute("""CREATE TABLE IF NOT EXISTS landed_costs (
                      id INTEGER PRIMARY KEY AUTOINCREMENT, doc_id INTEGER NOT NULL REFERENCES documents(id) ON DELETE CASCADE,
                      description TEXT NOT NULL DEFAULT '', amount REAL NOT NULL DEFAULT 0)""")
    lc_cols = {r[1] for r in db.execute("PRAGMA table_info(landed_costs)")}
    for col, decl in (("currency", "TEXT DEFAULT ''"), ("rate", "REAL DEFAULT 1"), ("base_amount", "REAL DEFAULT 0")):
        if col not in lc_cols:  # each charge in its own currency (amount), and in base currency
            db.execute(f"ALTER TABLE landed_costs ADD COLUMN {col} {decl}")
    # payment terms master: documents pick their payment terms from this list (stored on the document as text)
    db.execute("""CREATE TABLE IF NOT EXISTS payment_terms (
                      id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT UNIQUE NOT NULL, days INTEGER NOT NULL DEFAULT 0,
                      active INTEGER NOT NULL DEFAULT 1, created_at TEXT)""")
    if not db.execute("SELECT 1 FROM payment_terms").fetchone():
        start = [("Cash", 0), ("CDC", 0), ("Payment upon delivery", 0), ("60 Days PDC", 60), ("Net 90 Days", 90)]
        default = (db.execute("SELECT value FROM settings WHERE key = 'default_payment_terms'").fetchone() or [""])[0]
        used = [r[0] for r in db.execute("SELECT DISTINCT TRIM(payment_terms) FROM documents WHERE TRIM(COALESCE(payment_terms, '')) != ''")]
        for name in [default] + used:  # keep what is already in use
            if name and name.lower() not in {n.lower() for n, _ in start}:
                start.append((name, 0))
        db.executemany("INSERT INTO payment_terms(name, days, created_at) VALUES (?, ?, ?)", [(n, d, now()) for n, d in start])
    seed_coa(db)
    # Indexes for every column the screens search, join or sort on, so pages stay fast as data grows
    db.executescript("""
    CREATE INDEX IF NOT EXISTS idx_docs_type ON documents(doc_type, status, doc_date);
    CREATE INDEX IF NOT EXISTS idx_docs_party ON documents(customer_id, status, doc_type);
    CREATE INDEX IF NOT EXISTS idx_docs_parent ON documents(parent_id);
    CREATE INDEX IF NOT EXISTS idx_docs_date ON documents(doc_date);
    CREATE INDEX IF NOT EXISTS idx_items_doc ON items(document_id, sl);
    CREATE INDEX IF NOT EXISTS idx_items_source ON items(source_item_id);
    CREATE INDEX IF NOT EXISTS idx_items_product ON items(product_id);
    CREATE INDEX IF NOT EXISTS idx_moves_doc ON stock_moves(document_id);
    CREATE INDEX IF NOT EXISTS idx_moves_kind ON stock_moves(kind);
    CREATE INDEX IF NOT EXISTS idx_sources_source ON doc_sources(source_id);
    CREATE INDEX IF NOT EXISTS idx_pay_party ON payments(party_id, status);
    CREATE INDEX IF NOT EXISTS idx_pay_kind ON payments(kind, status, pay_date);
    CREATE INDEX IF NOT EXISTS idx_alloc_doc ON payment_allocations(document_id);
    CREATE INDEX IF NOT EXISTS idx_alloc_pay ON payment_allocations(payment_id);
    CREATE INDEX IF NOT EXISTS idx_req_user ON note_requests(user_id, status);
    CREATE INDEX IF NOT EXISTS idx_req_inv ON note_requests(invoice_id, doc_type);
    CREATE INDEX IF NOT EXISTS idx_req_status ON note_requests(status);
    CREATE INDEX IF NOT EXISTS idx_powf_doc ON po_workflow(doc_id, id);
    CREATE INDEX IF NOT EXISTS idx_jl_journal ON journal_lines(journal_id);
    CREATE INDEX IF NOT EXISTS idx_logs_user ON logs(username, id);
    CREATE INDEX IF NOT EXISTS idx_logs_time ON logs(created_at);
    CREATE INDEX IF NOT EXISTS idx_cust_kind ON customers(kind, name);
    CREATE INDEX IF NOT EXISTS idx_cust_lname ON customers(lower(name), kind);
    CREATE INDEX IF NOT EXISTS idx_prod_lname ON products(lower(name));
    CREATE INDEX IF NOT EXISTS idx_gl_account ON gl_lines(account_id, dt, seq, id);
    CREATE INDEX IF NOT EXISTS idx_gl_date ON gl_lines(dt, seq);
    CREATE INDEX IF NOT EXISTS idx_gl_ref ON gl_lines(rk, rid);
    CREATE INDEX IF NOT EXISTS idx_gl_src ON gl_lines(src, dt);
    """)
    for k, v in DEFAULT_SETTINGS.items():
        db.execute("INSERT OR IGNORE INTO settings(key, value) VALUES (?, ?)", (k, v))
    if not db.execute("SELECT 1 FROM users LIMIT 1").fetchone():
        db.execute(
            "INSERT INTO users(username, full_name, password_hash, role, created_at) VALUES (?,?,?,?,?)",
            ("admin", "Administrator", generate_password_hash("admin123"), "admin", now()))
    db.row_factory = sqlite3.Row
    if (db.execute("SELECT value FROM settings WHERE key = 'gl_version'").fetchone() or [None])[0] != GL_VERSION:
        gl_rebuild(db)  # first run of this version: write the ledger from all posted data
        db.execute("INSERT OR REPLACE INTO settings(key, value) VALUES ('gl_version', ?)", (GL_VERSION,))
    db.commit()
    db.execute("PRAGMA journal_mode = WAL")
    db.execute("PRAGMA optimize")
    db.close()


def init_all():
    """Upgrade every entity's database; billing.db also holds the entity list and who may open which."""
    init_db(DB_PATH)
    db = sqlite3.connect(DB_PATH)
    db.row_factory = sqlite3.Row
    db.executescript("""
    CREATE TABLE IF NOT EXISTS entities (
        id INTEGER PRIMARY KEY AUTOINCREMENT, code TEXT UNIQUE NOT NULL, name TEXT NOT NULL,
        db_file TEXT UNIQUE NOT NULL, active INTEGER NOT NULL DEFAULT 1, created_at TEXT);
    CREATE TABLE IF NOT EXISTS user_entities (user_id INTEGER NOT NULL, entity_id INTEGER NOT NULL,
        PRIMARY KEY (user_id, entity_id));""")
    if "last_entity" not in {r[1] for r in db.execute("PRAGMA table_info(users)")}:
        db.execute("ALTER TABLE users ADD COLUMN last_entity INTEGER")
    # user setup: roles give module access; a user's own module list starts from the role's
    db.execute("""CREATE TABLE IF NOT EXISTS roles (
                      id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT UNIQUE NOT NULL, description TEXT DEFAULT '',
                      is_admin INTEGER NOT NULL DEFAULT 0, modules TEXT NOT NULL DEFAULT '', created_at TEXT)""")
    if not db.execute("SELECT 1 FROM roles").fetchone():
        all_mods = ",".join(MODULE_KEYS)
        db.execute("INSERT INTO roles(name, description, is_admin, modules, created_at) VALUES (?,?,1,?,?)",
                   ("Administrator", "Full access, including system administration", all_mods, now()))
        db.execute("INSERT INTO roles(name, description, is_admin, modules, created_at) VALUES (?,?,0,?,?)",
                   ("User", "All business modules, no administration", all_mods, now()))
    user_cols = {r[1] for r in db.execute("PRAGMA table_info(users)")}
    for col, decl in (("email", "TEXT DEFAULT ''"), ("mobile", "TEXT DEFAULT ''"), ("photo", "TEXT DEFAULT ''"),
                      ("role_id", "INTEGER"), ("modules", "TEXT"), ("must_change_pw", "INTEGER DEFAULT 0"),
                      ("failed_logins", "INTEGER DEFAULT 0"), ("locked_at", "TEXT"), ("last_login", "TEXT"),
                      ("pw_changed_at", "TEXT"), ("created_by", "INTEGER")):
        if col not in user_cols:
            db.execute(f"ALTER TABLE users ADD COLUMN {col} {decl}")
    db.execute("""UPDATE users SET role_id = (SELECT id FROM roles WHERE name = CASE users.role WHEN 'admin'
                  THEN 'Administrator' ELSE 'User' END) WHERE role_id IS NULL""")
    db.execute("UPDATE users SET modules = (SELECT modules FROM roles r WHERE r.id = users.role_id) WHERE modules IS NULL")
    for table in ("roles", "users"):  # the permission matrix replaces the module lists
        if "perms" not in {r[1] for r in db.execute(f"PRAGMA table_info({table})")}:
            db.execute(f"ALTER TABLE {table} ADD COLUMN perms TEXT")
        for row in db.execute(f"SELECT id, modules FROM {table} WHERE perms IS NULL").fetchall():
            db.execute(f"UPDATE {table} SET perms = ? WHERE id = ?", (json.dumps(perms_from_modules(row[1])), row[0]))
    if not db.execute("SELECT 1 FROM entities").fetchone():
        # the data already here becomes the first entity, open to everyone who could use it before
        name = (db.execute("SELECT value FROM settings WHERE key = 'company_name'").fetchone() or ["Main"])[0]
        eid = db.execute("INSERT INTO entities(code, name, db_file, created_at) VALUES ('MAIN', ?, 'billing.db', ?)",
                         (name, now())).lastrowid
        db.execute("INSERT OR IGNORE INTO user_entities(user_id, entity_id) SELECT id, ? FROM users", (eid,))
    db.commit()
    others = [r["db_file"] for r in db.execute("SELECT db_file FROM entities WHERE db_file != 'billing.db'")]
    db.close()
    for f in others:
        if os.path.exists(os.path.join(BASE_DIR, f)):
            init_db(os.path.join(BASE_DIR, f))
    with app.app_context():
        sync_users()


def get_settings():
    if "settings" not in g:
        g.settings = {r["key"]: r["value"] for r in get_db().execute("SELECT key, value FROM settings")}
    return g.settings


def set_setting(key, value):
    get_db().execute("INSERT INTO settings(key, value) VALUES (?, ?) "
                     "ON CONFLICT(key) DO UPDATE SET value = excluded.value", (key, value))
    g.pop("settings", None)


def log(action, details=""):
    """Record an entry in the activity log for the current user."""
    user = getattr(g, "user", None)
    get_db().execute(
        "INSERT INTO logs(user_id, username, action, details, ip, created_at) VALUES (?,?,?,?,?,?)",
        (user["id"] if user else None, user["username"] if user else request.form.get("username", "-"),
         action, details, request.remote_addr, now()))
    get_db().commit()


# ---------------------------------------------------------------- auth

@app.before_request
def load_user():
    g.user, g.entity, g.entities = None, None, []
    uid = session.get("uid")
    if uid:
        user = main_db().execute("SELECT * FROM users WHERE id = ? AND active = 1", (uid,)).fetchone()
        allowed = user_entities(user) if user else []
        if not allowed:
            session.clear()
            return
        # the entity chosen in this session, if the user may still open it
        use_entity(next((e for e in allowed if e["id"] == session.get("entity")), allowed[0]))
        g.user, g.entities = user, allowed


@app.before_request
def check_access():
    if g.user is None or request.endpoint in (None, "static", "logout", "login"):
        return None
    if g.user["must_change_pw"] and request.endpoint != "profile":
        flash("Set a new password of your own before you continue.", "error")
        return redirect(url_for("profile"))
    need = need_for(request.endpoint, request.view_args, request.args, request.method)
    if not allowed(need):
        names = {k: n for k, _, n, _ in FEATURES}
        what = " / ".join(names[f] for f, _ in need)
        view_only = any(user_perms(g.user)[f] == VIEW for f, _ in need)
        flash(f"{what}: you have view-only access." if view_only else
              f"You don't have access to {what}. Ask the administrator.", "error")
        back = request.referrer if request.referrer and request.referrer.startswith(request.host_url) else None
        return redirect(back or url_for("dashboard"))
    if request.method == "POST" and (entry := entry_period()):
        module, dates = entry
        err = next((e for e in (period_error(d, module) for d in sorted(set(dates))) if e), None)
        if err:
            log("PERIOD BLOCKED", f"{request.endpoint}: {err}")
            flash(err, "error")
            back = request.referrer if request.referrer and request.referrer.startswith(request.host_url) else None
            return redirect(back or url_for("dashboard"))
    return None


def login_required(view):
    @wraps(view)
    def wrapped(*a, **kw):
        if g.user is None:
            return redirect(url_for("login", next=request.path))
        return view(*a, **kw)
    return wrapped


def admin_required(view):
    @wraps(view)
    @login_required
    def wrapped(*a, **kw):
        if g.user["role"] != "admin":
            flash("Admin access required.", "error")
            return redirect(url_for("dashboard"))
        return view(*a, **kw)
    wrapped.admin_only = True
    return wrapped


ADMIN_UNLOCK_SECONDS = 15 * 60


def admin_panel_required(view):
    """Admin Panel pages need the admin's password again; the unlock lasts 15 minutes of activity."""
    @wraps(view)
    @admin_required
    def wrapped(*a, **kw):
        ts = datetime.now().timestamp()
        if ts - session.get("admin_unlocked_at", 0) > ADMIN_UNLOCK_SECONDS:
            session.pop("admin_unlocked_at", None)
            return redirect(url_for("admin_unlock", next=request.full_path))
        session["admin_unlocked_at"] = ts
        return view(*a, **kw)
    wrapped.admin_only = True
    return wrapped


@app.template_filter("upload_url")
def upload_url(stored):
    """URL of an uploaded file saved as 'name.png?v=123' (the version only makes browsers fetch a new upload)."""
    name, _, ver = (stored or "").partition("?v=")
    return url_for("static", filename="uploads/" + name, v=ver or None)


@app.template_filter("disc")
def disc_note(it):
    """'Disc 10% · less 5.00/unit' for a line with a discount, else ''."""
    keys = it.keys()
    pct = it["disc_pct"] if "disc_pct" in keys else 0
    amt = it["disc_amt"] if "disc_amt" in keys else 0
    parts = ([f"Disc {num(pct)}%"] if pct else []) + ([f"less {money(amt)}/unit"] if amt else [])
    return " · ".join(parts)


@app.context_processor
def inject_globals():
    return {"S": get_settings(), "DOC_TYPES": DOC_TYPES, "current_user": g.get("user"),
            "SALES_FLOW": SALES_FLOW, "PURCHASE_FLOW": PURCHASE_FLOW, "UNPRICED": UNPRICED, "UNITS": UNITS,
            "pending_approvals": pending_approvals(), "po_pending": po_pending_count(),
            "po_wf_on": po_wf_enabled(), "WAREHOUSES": warehouse_map(), "default_wh": default_warehouse_id(),
            "CURRENCIES": currency_map(), "BASE_CUR": base_currency(), "PAY_TERMS": pay_terms(),
            "ENTITY": g.get("entity"), "ENTITIES": g.get("entities") or [],
            "MODULES": MODULES, "MY_MODULES": user_modules(g.user) if g.get("user") else set(),
            "FEATURES": FEATURES, "MY_PERMS": user_perms(g.user) if g.get("user") else {}, "url_ok": url_ok, "perm_summary": perm_summary,
            "PW_MIN": PW_MIN,
            "TERMS_REQUIRED": TERMS_REQUIRED, "PREV_TYPE": PREV_TYPE}


def pay_terms():
    """Payment terms master, active and inactive (forms offer the active ones)."""
    if "pay_terms" not in g:
        g.pay_terms = get_db().execute("SELECT * FROM payment_terms ORDER BY days, name").fetchall()
    return g.pay_terms


# ---------------------------------------------------------------- currencies
# Purchase documents (PO, GRN, purchase invoice, debit note) can be in a foreign currency at an exchange rate
# (base currency per 1 unit). A GRN / invoice / debit note takes the currency and rate of the document it comes from,
# so stock, the goods-received clearing account and the vendor balance all use the PO's rate. Each document also keeps
# base_total / base_vat: the ledger, party balances, payments and stock use those base-currency values.

def base_currency():
    return get_settings().get("currency") or "AED"


def currency_map():
    if "currencies" not in g:
        g.currencies = {r["code"]: r for r in get_db().execute("SELECT * FROM currencies ORDER BY code != ?, code",
                                                                (base_currency(),))}
    return g.currencies


def doc_currency(doc_type, f, source):
    """(currency, rate, error) for a document being saved: copied from its source, or as entered on a PO."""
    base = base_currency()
    if doc_type not in PURCHASE_FLOW:
        return base, 1.0, None
    if source is not None:
        return source["currency"] or base, source["exchange_rate"] or 1.0, None
    cur = (f.get("currency") or base).upper()
    c = currency_map().get(cur)
    if not c or not c["active"]:
        return base, 1.0, f"Currency {cur} is not set up."
    rate = 1.0 if cur == base else to_float(f.get("exchange_rate"))
    if rate <= 0:
        return cur, rate, "Enter the exchange rate."
    return cur, rate, None


# ---------------------------------------------------------------- warehouses
# Every document line has a warehouse (the document's warehouse is the default for new lines). Lines copied to a
# DN / GRN, invoice or return keep their warehouse, and every stock move is tagged with its line's warehouse, so
# quantities are known per warehouse. Cost stays one company-wide average per product.

def warehouse_map():
    if "warehouses" not in g:
        g.warehouses = {r["id"]: r for r in get_db().execute("SELECT * FROM warehouses ORDER BY code")}
    return g.warehouses


def default_warehouse_id():
    whs = warehouse_map()
    wid = int(get_settings().get("default_warehouse") or 0)
    return wid if wid in whs else next(iter(whs), None)


def wh_id(value):
    """A posted warehouse id if it is an active warehouse, otherwise the default one."""
    try:
        wid = int(value)
    except (TypeError, ValueError):
        return default_warehouse_id()
    w = warehouse_map().get(wid)
    return wid if w and w["active"] else default_warehouse_id()


def order_prefill(doc_type):
    """Header values from the Create purchase / sales order dialog (query string) for a new order form, or None."""
    a = request.args
    if not (a.get("customer_id") or a.get("cust_name", "").strip()):
        return None
    s = get_settings()
    sales = doc_type == "SO"
    d = {k: a.get(k, "").strip() for k in ("cust_name", "cust_contact", "attention", "lpo_no", "delivery_location",
                                          "payment_terms", "dispatch_mode", "receipt_date")}
    d["payment_terms"] = d["payment_terms"].replace("__add__", "")
    c = get_db().execute("SELECT * FROM customers WHERE id = ? AND kind = ?",
                         (a.get("customer_id", type=int), "customer" if sales else "supplier")).fetchone()
    if c:
        d.update(customer_id=c["id"], cust_name=c["name"], cust_area=c["area"], cust_po_box=c["po_box"],
                 cust_trn=c["trn"], cust_contact=d["cust_contact"] or c["contact"], attention=d["attention"] or c["attention"])
    if sales:  # sales are in the base currency, with the usual sales defaults
        d.update(currency=base_currency(), exchange_rate=1.0, receipt_date="", buyer="Same as above",
                 payment_terms=d["payment_terms"] or s.get("default_payment_terms", ""),
                 payment_resp=s.get("default_payment_resp", ""))
    else:
        cur = a.get("currency", "").upper()
        cur = cur if cur in currency_map() else (c["currency"] if c and c["currency"] in currency_map() else base_currency())
        d.update(currency=cur, exchange_rate=1.0 if cur == base_currency() else (to_float(a.get("exchange_rate"))
                                                                               or currency_map()[cur]["rate"]))
    d.update(warehouse_id=wh_id(a.get("warehouse_id")) if a.get("warehouse_id") else None, vat_rate=to_float(s.get("vat_rate")),
             dispatch_mode=d["dispatch_mode"] or s.get("default_dispatch", ""))
    return d


def wh_qty(product_id, warehouse_id):
    return get_db().execute("SELECT COALESCE(SUM(qty), 0) FROM stock_moves WHERE product_id = ? AND warehouse_id = ?",
                            (product_id, warehouse_id)).fetchone()[0]


# ---------------------------------------------------------------- purchase order approval workflow
# Switched on in Purchase -> Approval workflow setup. While on, submitting a PO sends it through the approval steps
# in order (a step can apply only from a PO amount up); each step is approved by any one of its approvers.
# After the last step the PO is Submitted (approved) and GRNs can be made. A rejection or a recall puts it back
# to Draft, and resubmitting starts again from the first step. Every action is kept in po_workflow.
# While off, submitting a PO approves it straight away, as before.

def po_wf_enabled():
    return get_settings().get("po_wf_enabled") == "1"


def wf_steps():
    return get_db().execute("SELECT * FROM po_wf_steps ORDER BY seq, id").fetchall()


def step_approvers(step):
    return {int(x) for x in (step["approvers"] or "").split(",") if x.strip().isdigit()}


def next_step(doc, after_seq=None):
    """The next approval step that applies to this PO's amount, after the given position."""
    for st in wf_steps():
        if (after_seq is None or st["seq"] > after_seq) and (doc["base_total"] or doc["total"]) >= (st["min_amount"] or 0):
            return st
    return None


def current_step(doc):
    if doc["doc_type"] != "PO" or doc["status"] != "Pending" or not doc["wf_step"]:
        return None
    return get_db().execute("SELECT * FROM po_wf_steps WHERE id = ?", (doc["wf_step"],)).fetchone()


def can_approve(doc):
    """An approver of the current step may decide, but not on their own PO; an admin may decide any step."""
    st = current_step(doc)
    if not st or not g.get("user"):
        return False
    if g.user["role"] == "admin":
        return True
    return g.user["id"] in step_approvers(st) and doc["created_by"] != g.user["id"]


def po_pending_count():
    """Purchase orders waiting for the current user's approval (badge in the menu)."""
    if not g.get("user"):
        return 0
    docs = get_db().execute("SELECT * FROM documents WHERE doc_type = 'PO' AND status = 'Pending'").fetchall()
    return sum(1 for d in docs if can_approve(d))


def po_history(doc_id):
    return get_db().execute("""SELECT w.*, u.username, u.full_name FROM po_workflow w LEFT JOIN users u ON u.id = w.user_id
                               WHERE w.doc_id = ? ORDER BY w.id""", (doc_id,)).fetchall()


def po_rejected_ids():
    """Draft POs whose last workflow action was a rejection."""
    return {r[0] for r in get_db().execute(
        """SELECT w.doc_id FROM po_workflow w JOIN documents d ON d.id = w.doc_id
           WHERE d.status = 'Draft' AND w.action = 'Rejected'
             AND w.id = (SELECT MAX(id) FROM po_workflow x WHERE x.doc_id = w.doc_id)""")}


def wf_log(doc_id, action, step_name="", remark=""):
    get_db().execute("INSERT INTO po_workflow(doc_id, action, step_name, user_id, remark, at) VALUES (?,?,?,?,?,?)",
                     (doc_id, action, step_name, g.user["id"], remark, now()))


def submit_po(doc, remark=""):
    """Send a draft PO into the approval workflow (or approve it at once when the workflow is off).

    Returns the step it now waits at, or None when it was approved straight away. Commits.
    """
    st = next_step(doc) if po_wf_enabled() else None
    if st:
        get_db().execute("UPDATE documents SET status = 'Pending', wf_step = ? WHERE id = ?", (st["id"], doc["id"]))
        wf_log(doc["id"], "Submitted", st["name"], remark)
        get_db().commit()
        return st
    if po_wf_enabled():
        wf_log(doc["id"], "Approved", "", "No approval step applies to this amount")
    confirm_doc(doc)
    return None


def pending_approvals():
    """Credit / Debit Note requests waiting for an admin (shown as a badge in the admin menu)."""
    user = g.get("user")
    if not user or user["role"] != "admin":
        return 0
    return get_db().execute("SELECT COUNT(*) FROM note_requests WHERE status = 'Pending'").fetchone()[0]


@app.template_filter("money")
def money(v):
    return f"{(v or 0):,.2f}"


@app.template_filter("num")
def num(v):
    v = v or 0
    return f"{v:,.0f}" if float(v).is_integer() else f"{v:,.2f}"


@app.template_filter("ddmmyyyy")
def ddmmyyyy(v):
    try:
        return datetime.strptime(v, "%Y-%m-%d").strftime("%d-%m-%Y")
    except (TypeError, ValueError):
        return v or ""


@app.route("/login", methods=["GET", "POST"])
def login():
    if request.method == "POST":
        username = request.form.get("username", "").strip()
        mdb = main_db()
        user = mdb.execute("SELECT * FROM users WHERE username = ?", (username,)).fetchone()
        if user and user["locked_at"]:
            until = datetime.strptime(user["locked_at"], "%Y-%m-%d %H:%M:%S") + timedelta(minutes=LOCK_MINUTES)
            if datetime.now() < until:
                log("LOGIN LOCKED", f"Login attempt for locked account '{username}'")
                flash(f"This account is locked after {MAX_FAILED_LOGINS} wrong passwords. Try again after "
                      f"{until.strftime('%H:%M')} or ask the administrator to unlock it.", "error")
                return render_template("login.html")
            mdb.execute("UPDATE users SET locked_at = NULL, failed_logins = 0 WHERE id = ?", (user["id"],))
            mdb.commit()
            user = mdb.execute("SELECT * FROM users WHERE id = ?", (user["id"],)).fetchone()
        if user and user["active"] and check_password_hash(user["password_hash"], request.form.get("password", "")):
            mdb.execute("UPDATE users SET failed_logins = 0, locked_at = NULL, last_login = ? WHERE id = ?", (now(), user["id"]))
            mdb.commit()
            allowed = user_entities(user)
            if not allowed:
                flash("No business entity is assigned to you. Ask the administrator.", "error")
                return render_template("login.html")
            session.clear()
            session["uid"] = user["id"]
            use_entity(next((e for e in allowed if e["id"] == user["last_entity"]), allowed[0]))
            g.user = user
            log("LOGIN", "User logged in")
            nxt = request.args.get("next", "")
            return redirect(nxt if nxt.startswith("/") else url_for("dashboard"))
        log("LOGIN FAILED", f"Failed login attempt for '{username}'")
        if user and user["active"]:
            fails = (user["failed_logins"] or 0) + 1
            mdb.execute("UPDATE users SET failed_logins = ?, locked_at = ? WHERE id = ?",
                        (fails, now() if fails >= MAX_FAILED_LOGINS else None, user["id"]))
            mdb.commit()
            if fails >= MAX_FAILED_LOGINS:
                log("USER LOCKED", f"Account '{username}' locked after {fails} wrong passwords")
                flash(f"Too many wrong passwords: the account is locked for {LOCK_MINUTES} minutes.", "error")
                return render_template("login.html")
        flash("Invalid username or password.", "error")
    return render_template("login.html")


@app.route("/logout")
@login_required
def logout():
    log("LOGOUT", "User logged out")
    session.clear()
    return redirect(url_for("login"))


@app.route("/entity/switch", methods=["POST"])
@login_required
def entity_switch():
    ent = next((e for e in g.entities if e["id"] == request.form.get("entity", type=int)), None)
    if ent is None:
        flash("You can't open that business entity.", "error")
        return redirect(url_for("dashboard"))
    if ent["id"] != g.entity["id"]:
        log("ENTITY LEAVE", f"Switched to {ent['code']} · {ent['name']}")
        use_entity(ent)
        main_db().execute("UPDATE users SET last_entity = ? WHERE id = ?", (ent["id"], g.user["id"]))
        main_db().commit()
        log("ENTITY OPEN", f"Switched from another entity to {ent['code']} · {ent['name']}")
        flash(f"Now working in {ent['code']} · {ent['name']}.", "ok")
    return redirect(url_for("dashboard"))


@app.route("/profile", methods=["GET", "POST"])
@login_required
def profile():
    if request.method == "POST":
        cur, new, confirm = (request.form.get(k, "") for k in ("current", "new", "confirm"))
        if not check_password_hash(g.user["password_hash"], cur):
            flash("Current password is wrong.", "error")
        elif new != confirm:
            flash("The new password and its confirmation don't match.", "error")
        elif password_problem(new):
            flash(password_problem(new), "error")
        elif cur == new:
            flash("Choose a password different from the current one.", "error")
        else:
            main_db().execute("UPDATE users SET password_hash = ?, must_change_pw = 0, pw_changed_at = ? WHERE id = ?",
                              (generate_password_hash(new), now(), g.user["id"]))
            main_db().commit()
            sync_users()
            log("PASSWORD CHANGE", "Changed own password")
            flash("Password changed.", "ok")
            return redirect(url_for("dashboard"))
    return render_template("profile.html")


# ---------------------------------------------------------------- dashboard

@app.route("/")
@login_required
def dashboard():
    db = get_db()
    today = date.today().isoformat()

    def one(sql, *p):
        return db.execute(sql, p).fetchone()[0]

    def pending(doc_type):
        if NEXT_TYPE[doc_type] in PARTIAL:
            return one(f"""SELECT COUNT(*) FROM documents s WHERE s.doc_type=? AND s.status='Submitted'
                           AND {OPEN_QTY_SQL.format(d='s')} > 0""", doc_type)
        return one("""SELECT COUNT(*) FROM documents s WHERE s.doc_type=? AND s.status='Submitted'
                      AND NOT EXISTS (SELECT 1 FROM doc_sources ds WHERE ds.source_id = s.id)""", doc_type)

    def total_today(doc_type):
        return one("SELECT COALESCE(SUM(base_total),0) FROM documents WHERE doc_type=? "
                   "AND status='Submitted' AND doc_date=?", doc_type, today)

    stats = {
        "so_today": one("SELECT COUNT(*) FROM documents WHERE doc_type='SO' AND doc_date=?", today),
        "pending_dn": pending("SO"),
        "pending_inv": pending("DN"),
        "sales_today": total_today("INV"),
        "po_today": one("SELECT COUNT(*) FROM documents WHERE doc_type='PO' AND doc_date=?", today),
        "pending_grn": pending("PO"),
        "pending_pi": pending("GRN"),
        "purchases_today": total_today("PI"),
        "stock_value": one("SELECT COALESCE(SUM(stock_qty * avg_cost), 0) FROM products WHERE stock_qty > 0"),
        "drafts": one("SELECT COUNT(*) FROM documents WHERE status='Draft'"),
        "receivable": party_balances("customer"),
        "payable": party_balances("supplier"),
        "received_today": one("SELECT COALESCE(SUM(amount), 0) FROM payments WHERE kind = 'receipt' AND status = 'Posted' "
                              "AND pay_date = ?", today),
        "paid_today": one("SELECT COALESCE(SUM(amount), 0) FROM payments WHERE kind = 'payment' AND status = 'Posted' "
                          "AND pay_date = ?", today),
        "my_approved": one("""SELECT COUNT(*) FROM note_requests WHERE user_id = ? AND status = 'Approved'
                              AND note_id IS NULL""", g.user["id"]),
    }
    recent = db.execute(DOC_LIST_SQL + " ORDER BY d.id DESC LIMIT 10").fetchall()

    # ---- this month
    t = date.today()
    month = t.replace(day=1).isoformat()
    stats.update(
        sales_month=one("""SELECT COALESCE(SUM(CASE WHEN doc_type = 'INV' THEN base_total ELSE -base_total END), 0) FROM documents
                           WHERE doc_type IN ('INV', 'SR') AND status = 'Submitted' AND doc_date >= ?""", month),
        purchases_month=one("""SELECT COALESCE(SUM(CASE WHEN doc_type = 'PI' THEN base_total ELSE -base_total END), 0) FROM documents
                               WHERE doc_type IN ('PI', 'PR') AND status = 'Submitted' AND doc_date >= ?""", month),
        po_month=one("SELECT COUNT(*) FROM documents WHERE doc_type = 'PO' AND status != 'Draft' AND doc_date >= ?", month),
        po_month_value=one("""SELECT COALESCE(SUM(base_total), 0) FROM documents WHERE doc_type = 'PO' AND status != 'Draft'
                              AND doc_date >= ?""", month),
        approved_month=one("""SELECT COUNT(*) FROM documents WHERE doc_type = 'PO' AND status = 'Submitted'
                              AND submitted_at >= ?""", month),
        rejected_month=one("SELECT COUNT(*) FROM po_workflow WHERE action = 'Rejected' AND at >= ?", month),
    )

    # ---- waiting for a decision: POs at an approval step, and (admins) credit / debit note requests
    waiting = []
    for d in db.execute("""SELECT d.*, u.username AS creator, st.name AS step_name FROM documents d
                           LEFT JOIN users u ON u.id = d.created_by LEFT JOIN po_wf_steps st ON st.id = d.wf_step
                           WHERE d.doc_type = 'PO' AND d.status = 'Pending' ORDER BY d.id""").fetchall():
        waiting.append(dict(no=d["doc_no"], kind="Purchase order", party=d["cust_name"], by=d["creator"], date=d["doc_date"],
                            amount=f"{d['currency'] or s_cur()} {money(d['total'])}", status=d["step_name"] or "Pending",
                            mine=can_approve(d), url=url_for("doc_view", doc_id=d["id"])))
    if g.user["role"] == "admin":
        for r in db.execute("""SELECT r.*, d.doc_no AS invoice_no, d.cust_name, u.username FROM note_requests r
                               JOIN documents d ON d.id = r.invoice_id LEFT JOIN users u ON u.id = r.user_id
                               WHERE r.status = 'Pending' ORDER BY r.id""").fetchall():
            waiting.append(dict(no=r["invoice_no"], kind=DOC_TYPES[r["doc_type"]] + " request", party=r["cust_name"],
                                by=r["username"], date=r["created_at"][:10], amount="", status="Pending", mine=True,
                                url=url_for("approvals")))
    waiting.sort(key=lambda w: not w["mine"])

    # ---- purchase orders of this month by status (donut)
    inv_pos = {r[0] for r in db.execute("""SELECT DISTINCT g.parent_id FROM documents g JOIN doc_sources ds ON ds.source_id = g.id
                                           JOIN documents pi ON pi.id = ds.doc_id WHERE g.doc_type = 'GRN' AND pi.doc_type = 'PI'""")}
    po_mix = {"Invoiced": 0, "Received": 0, "Partly received": 0, "Open order": 0, "Pending approval": 0}
    for d in db.execute(f"""SELECT d.id, d.status, {OPEN_QTY_SQL.format(d='d')} AS open_qty,
                               EXISTS (SELECT 1 FROM documents c WHERE c.parent_id = d.id) AS has_child
                            FROM documents d WHERE d.doc_type = 'PO' AND d.status != 'Draft' AND d.doc_date >= ?""", (month,)):
        key = ("Pending approval" if d["status"] == "Pending" else "Partly received" if d["open_qty"] and d["has_child"]
               else "Open order" if d["open_qty"] else "Invoiced" if d["id"] in inv_pos else "Received")
        po_mix[key] += 1

    # ---- calendar: requested receipts of open POs and invoices, about three months around today
    lo, hi = (t.replace(day=1) - timedelta(days=62)).isoformat(), (t + timedelta(days=95)).isoformat()
    events = []
    for d in db.execute(f"""SELECT d.id, d.doc_no, d.cust_name, d.receipt_date, {OPEN_QTY_SQL.format(d='d')} AS open_qty
                            FROM documents d WHERE d.doc_type = 'PO' AND d.status != 'Draft' AND d.receipt_date BETWEEN ? AND ?""",
                         (lo, hi)):
        if d["open_qty"]:
            events.append(dict(date=d["receipt_date"], kind="receipt", late=d["receipt_date"] < t.isoformat(),
                               text=f"Receive {d['doc_no']}", sub=d["cust_name"], url=url_for("doc_view", doc_id=d["id"])))
    for d in db.execute("""SELECT id, doc_type, doc_no, cust_name, doc_date, total, currency FROM documents
                           WHERE doc_type IN ('INV', 'PI') AND status = 'Submitted' AND doc_date BETWEEN ? AND ?""", (lo, hi)):
        events.append(dict(date=d["doc_date"], kind="sale" if d["doc_type"] == "INV" else "purchase", late=False,
                           text=f"{DOC_TYPES[d['doc_type']]} {d['doc_no']}",
                           sub=f"{d['cust_name']} · {d['currency'] or s_cur()} {money(d['total'])}",
                           url=url_for("doc_view", doc_id=d["id"])))

    # ---- latest activity (everyone's for admins, your own otherwise)
    where = "" if g.user["role"] == "admin" else "WHERE user_id = ?"
    activity = []
    for r in db.execute(f"SELECT * FROM logs {where} ORDER BY id DESC LIMIT 6",
                        () if g.user["role"] == "admin" else (g.user["id"],)).fetchall():
        secs = (datetime.now() - datetime.strptime(r["created_at"], "%Y-%m-%d %H:%M:%S")).total_seconds()
        ago = ("just now" if secs < 60 else f"{int(secs // 60)} min ago" if secs < 3600 else
               f"{int(secs // 3600)} hour{'s' if secs >= 7200 else ''} ago" if secs < 86400 else
               f"{int(secs // 86400)} day{'s' if secs >= 172800 else ''} ago")
        activity.append(dict(text=r["details"] or r["action"], who=r["username"], action=r["action"], ago=ago))

    return render_template("dashboard.html", stats=stats, recent=recent, waiting=waiting, po_mix=po_mix,
                           events=events, activity=activity, today=t.isoformat())


def s_cur():
    return get_settings().get("currency") or "AED"


# ---------------------------------------------------------------- billing

# Quantity of an order ({d} = the documents alias) not yet covered by its GRNs / Delivery Notes, per line
OPEN_QTY_SQL = """(SELECT COALESCE(SUM(MAX(i.qty - COALESCE((SELECT SUM(ci.qty) FROM items ci
                      JOIN documents c ON c.id = ci.document_id
                      WHERE c.parent_id = i.document_id AND ci.source_item_id = i.id), 0), 0)), 0)
                   FROM items i WHERE i.document_id = {d}.id)"""

DOC_LIST_SQL = f"""SELECT d.*, u.username AS creator,
                  (SELECT c.account_no FROM customers c WHERE c.id = d.customer_id) AS party_account,
                  COALESCE((SELECT GROUP_CONCAT(s.doc_no, ', ') FROM doc_sources ds JOIN documents s ON s.id = ds.source_id
                            WHERE ds.doc_id = d.id), p.doc_no) AS parent_no,
                  (SELECT GROUP_CONCAT(c.doc_no, ', ') FROM documents c WHERE c.parent_id = d.id
                      OR c.id IN (SELECT doc_id FROM doc_sources WHERE source_id = d.id)) AS child_no,
                  CASE WHEN d.doc_type IN ('SO', 'PO') THEN {OPEN_QTY_SQL.format(d='d')} END AS open_qty
                  FROM documents d LEFT JOIN users u ON u.id = d.created_by
                  LEFT JOIN documents p ON p.id = d.parent_id WHERE 1=1"""


def line_net(qty, rate, disc_pct=0.0, disc_amt=0.0):
    """Line net amount: quantity x (unit price - discount per unit) x (1 - discount % / 100)."""
    return r2(qty * (rate - (disc_amt or 0)) * (1 - (disc_pct or 0) / 100))


def r2(v):
    """Round money half-up to 2 decimals (38.125 -> 38.13)."""
    return float(Decimal(str(v)).quantize(Decimal("0.01"), ROUND_HALF_UP))


def to_float(v):
    try:
        return float(str(v).replace(",", "").strip() or 0)
    except ValueError:
        return 0.0


def next_doc_no(doc_type):
    s = get_settings()
    key = doc_type.lower()
    prefix, n = s[f"{key}_prefix"], int(s[f"{key}_next"] or 1)
    db = get_db()
    while True:
        doc_no = f"{prefix} {n:06d}"
        if not db.execute("SELECT 1 FROM documents WHERE doc_no = ?", (doc_no,)).fetchone():
            return doc_no, n, key
        n += 1


def get_doc(doc_id):
    return get_db().execute("SELECT * FROM documents WHERE id = ?", (doc_id,)).fetchone() or abort(404)


CHILDREN_SQL = """SELECT * FROM documents WHERE parent_id = ? OR id IN (SELECT doc_id FROM doc_sources WHERE source_id = ?)
                  ORDER BY id"""


def child_of(doc_id):
    return get_db().execute(CHILDREN_SQL, (doc_id, doc_id)).fetchone()


def invoiced_in(doc):
    """The invoice a GRN / Delivery Note is on, or for a PO / SO the first invoice made from its GRNs / Delivery
    Notes (draft or posted). The document is then locked for everyone, admins included; or None."""
    if doc["doc_type"] in ("PO", "SO"):
        return get_db().execute("""SELECT inv.* FROM documents n JOIN doc_sources ds ON ds.source_id = n.id
                                   JOIN documents inv ON inv.id = ds.doc_id WHERE n.parent_id = ?
                                   ORDER BY inv.id LIMIT 1""", (doc["id"],)).fetchone()
    if doc["doc_type"] not in PARTIAL:
        return None
    return get_db().execute("""SELECT d.* FROM documents d JOIN doc_sources ds ON ds.doc_id = d.id
                               WHERE ds.source_id = ?""", (doc["id"],)).fetchone()


def sources_of(doc):
    """The GRNs / Delivery Notes an invoice was made from (or the single parent of any other document)."""
    rows = get_db().execute("""SELECT s.* FROM doc_sources ds JOIN documents s ON s.id = ds.source_id
                               WHERE ds.doc_id = ? ORDER BY s.id""", (doc["id"],)).fetchall()
    return rows or ([get_doc(doc["parent_id"])] if doc["parent_id"] else [])


def invoice_sources(doc_type, raw_ids):
    """Validate the GRNs / Delivery Notes chosen for one invoice. Returns (documents, error message)."""
    src_type = PREV_TYPE[doc_type]
    ids = sorted({int(x) for v in raw_ids for x in str(v).split(",") if x.strip().isdigit()})
    if not ids:
        return [], f"Choose at least one {DOC_TYPES[src_type]}."
    db = get_db()
    docs = db.execute(f"SELECT * FROM documents WHERE id IN ({','.join('?' * len(ids))}) ORDER BY id", ids).fetchall()
    for d in docs:
        inv = invoiced_in(d) if d["doc_type"] == src_type else None
        if d["doc_type"] != src_type or d["status"] != "Submitted":
            return [], f"{d['doc_no']} is not a submitted {DOC_TYPES[src_type]}."
        if inv:
            return [], f"{d['doc_no']} is already invoiced in {inv['doc_no']}."
    if len({d["customer_id"] or d["cust_name"].strip().lower() for d in docs}) > 1:
        return [], f"All {DOC_TYPES[src_type]}s on one invoice must be for the same {party_kind(doc_type)}."
    if len({(d["currency"], d["exchange_rate"]) for d in docs}) > 1:
        return [], f"All {DOC_TYPES[src_type]}s on one invoice must have the same currency and exchange rate."
    return docs, None


def fulfilment(order_id, exclude_doc_id=0):
    """Lines of an SO / PO with how much is already delivered / received and how much is still pending.

    Drafts count too, so two people can't receive the same quantity twice.
    """
    rows = get_db().execute("""SELECT i.*, COALESCE((SELECT SUM(ci.qty) FROM items ci
                                   JOIN documents c ON c.id = ci.document_id
                                   WHERE c.parent_id = i.document_id AND ci.source_item_id = i.id AND c.id != ?), 0) AS done
                               FROM items i WHERE i.document_id = ? ORDER BY i.sl""", (exclude_doc_id, order_id)).fetchall()
    return [dict(r, pending=max(r["qty"] - r["done"], 0)) for r in rows]


def source_for(doc_type, parent_id):
    """Return the parent a new DN/GRN/INV/PI may be created from, or None if the workflow doesn't allow it."""
    if not parent_id:
        return None
    p = get_db().execute("SELECT * FROM documents WHERE id = ?", (parent_id,)).fetchone()
    if not p or p["doc_type"] != PREV_TYPE.get(doc_type) or p["status"] != "Submitted":
        return None
    if doc_type in OPEN_TYPES:
        return p if any(l["pending"] > 0 for l in fulfilment(p["id"])) else None
    return None if child_of(p["id"]) else p


def next_product_code():
    s = get_settings()
    n = int(s["item_next"] or 1)
    while True:
        code = f"{s['item_prefix']}-{n:05d}"
        if not get_db().execute("SELECT 1 FROM products WHERE code = ?", (code,)).fetchone():
            return code, n
        n += 1


def resolve_product(product_id, name, details, unit, rate, doc_type):
    """Find the product an item line refers to, creating it (with a new code) if it is new.

    The latest price used on a sales / purchase document becomes the product's sale / purchase price.
    """
    db = get_db()
    row = None
    if product_id:
        row = db.execute("SELECT * FROM products WHERE id = ?", (product_id,)).fetchone()
        if row and row["name"].strip().lower() != name.lower():
            row = None  # the name was changed after picking: treat as typed
    if not row:
        row = db.execute("SELECT * FROM products WHERE lower(name) = lower(?)", (name,)).fetchone()
    price_col = "purchase_price" if doc_type in PURCHASE_FLOW else "sale_price"
    if row:
        if rate > 0 and doc_type not in UNPRICED and doc_type not in RETURNS:
            db.execute(f"UPDATE products SET {price_col} = ? WHERE id = ?", (rate, row["id"]))
        return row["id"], row["code"]
    code, n = next_product_code()
    pid = db.execute(
        f"INSERT INTO products(code, name, details, unit, {price_col}, created_by, created_at) VALUES (?,?,?,?,?,?,?)",
        (code, name, details, unit, rate if doc_type not in UNPRICED else 0, g.user["id"], now())).lastrowid
    set_setting("item_next", str(n + 1))
    log("PRODUCT ADD", f"New product {code} '{name}' created from {DOC_TYPES[doc_type]}")
    return pid, code


# ---------------------------------------------------------------- inventory (weighted average cost)
#
# Stock moves IN when a GRN is submitted (at the purchase price, net of document discount) and OUT when a
# Delivery Note is submitted (at the average cost at that moment). Average cost is recomputed by replaying a
# product's moves in date order, so backdated documents, edits and deletes all give the correct result.

STOCK_DOCS = {"GRN": 1, "DN": -1, "SR": 1, "PR": -1}  # doc type -> direction


def recompute_stock(product_id, from_date=None):
    """Replay a product's moves (from from_date on: earlier ones are unchanged) to set average cost and values."""
    db = get_db()
    qty = avg = 0.0
    sql, params = "SELECT * FROM stock_moves WHERE product_id = ?", [product_id]
    if from_date:
        prev = db.execute("""SELECT balance_qty, avg_cost FROM stock_moves WHERE product_id = ? AND move_date < ?
                             ORDER BY move_date DESC, id DESC LIMIT 1""", (product_id, from_date)).fetchone()
        if prev:
            qty, avg = prev["balance_qty"] or 0.0, prev["avg_cost"] or 0.0
        sql += " AND move_date >= ?"
        params.append(from_date)
    changed = set()
    for m in db.execute(sql + " ORDER BY move_date, id", params).fetchall():
        if m["qty"] > 0:
            cost = m["unit_cost"]
            # with no stock (or negative stock) on hand, the incoming cost becomes the average
            avg = cost if qty <= 0 else (qty * avg + m["qty"] * cost) / (qty + m["qty"])
        elif m["fixed_cost"]:
            # a purchase return goes back at its purchase price; what remains keeps the rest of the value
            cost = m["unit_cost"]
            left = qty + m["qty"]
            avg = (qty * avg + m["qty"] * cost) / left if left > 0 and qty > 0 else avg
        else:
            cost = avg  # issues go out at the current average cost
        qty += m["qty"]
        new = (round(cost, 6), r2(abs(m["qty"]) * cost), qty, round(avg, 6))
        if new != (m["unit_cost"], m["value"], m["balance_qty"], m["avg_cost"]):  # write only what changed
            db.execute("UPDATE stock_moves SET unit_cost = ?, value = ?, balance_qty = ?, avg_cost = ? WHERE id = ?",
                       (*new, m["id"]))
            if new[1] != m["value"]:
                changed.add(("doc", m["document_id"]) if m["document_id"] else
                            ("se", m["entry_id"]) if m["entry_id"] else ("adj", m["id"]))
    db.execute("UPDATE products SET stock_qty = ?, avg_cost = ? WHERE id = ?", (qty, round(avg, 6), product_id))
    for rk, rid in changed:  # their stock value moved: rewrite their ledger lines
        gl_refresh(rk, rid)


def post_stock(doc_id):
    """(Re)write the stock moves of a GRN / Delivery Note from its current items and status."""
    db = get_db()
    doc = get_doc(doc_id)
    old = db.execute("SELECT product_id, move_date FROM stock_moves WHERE document_id = ?", (doc_id,)).fetchall()
    touched = {r[0]: r[1] for r in old}
    db.execute("DELETE FROM stock_moves WHERE document_id = ?", (doc_id,))
    direction = STOCK_DOCS.get(doc["doc_type"])
    if direction and doc["status"] == "Submitted":
        # spread the document discount over the lines so stock is valued at what was really paid
        factor = (doc["subtotal"] - doc["discount_amount"]) / doc["subtotal"] if doc["subtotal"] else 1
        for it in db.execute("SELECT * FROM items WHERE document_id = ? AND product_id IS NOT NULL AND qty != 0",
                             (doc_id,)).fetchall():
            if doc["doc_type"] in ("GRN", "PR"):
                net = it["amount"] / it["qty"] if it["qty"] else it["rate"]  # unit price after the line discount
                cost = net * factor * (doc["exchange_rate"] or 1)  # purchase price net of discounts, in base
                if doc["doc_type"] == "GRN":
                    cost += grn_landed(it["id"]) / it["qty"]  # landed cost billed on posted purchase invoices
            elif doc["doc_type"] == "SR":
                cost = issue_cost(it)        # comes back at the cost it went out at
            else:
                cost = 0                     # delivery: average cost, set when replaying
            db.execute("""INSERT INTO stock_moves(product_id, document_id, item_id, move_date, kind, ref, qty, unit_cost,
                          fixed_cost, warehouse_id, created_by, created_at) VALUES (?,?,?,?,?,?,?,?,?,?,?,?)""",
                       (it["product_id"], doc_id, it["id"], doc["doc_date"], doc["doc_type"], doc["doc_no"],
                        direction * it["qty"], cost, 1 if doc["doc_type"] == "PR" else 0,
                        it["warehouse_id"] or doc["warehouse_id"] or default_warehouse_id(), g.user["id"], now()))
            touched[it["product_id"]] = min(touched.get(it["product_id"], doc["doc_date"]), doc["doc_date"])
    for pid, from_date in touched.items():
        recompute_stock(pid, from_date)


def landed_charges(doc_id):
    return [dict(r) for r in get_db().execute("""SELECT description, currency, rate, amount, base_amount FROM landed_costs
                                                 WHERE doc_id = ? ORDER BY id""", (doc_id,))]


def grn_landed(grn_item_id):
    """Landed cost (base currency) that posted Purchase Invoices put on one GRN line."""
    return get_db().execute("""SELECT COALESCE(SUM(l.landed), 0) FROM items l JOIN documents d ON d.id = l.document_id
                               WHERE l.source_item_id = ? AND d.doc_type = 'PI' AND d.status = 'Submitted'""",
                            (grn_item_id,)).fetchone()[0]


def post_landed(pi):
    """Re-cost the GRNs of a Purchase Invoice with its landed cost, keeping their stock moves in place.

    A GRN that is invoiced is locked, so its moves are still the ones post_stock() wrote from its lines, in line order.
    """
    db = get_db()
    if pi["doc_type"] != "PI" or not pi["landed_amount"]:
        return
    for grn in sources_of(pi):
        if grn["doc_type"] != "GRN" or grn["status"] != "Submitted":
            continue
        factor = (grn["subtotal"] - grn["discount_amount"]) / grn["subtotal"] if grn["subtotal"] else 1
        lines = db.execute("SELECT * FROM items WHERE document_id = ? AND product_id IS NOT NULL AND qty != 0 ORDER BY id",
                           (grn["id"],)).fetchall()
        moves = db.execute("SELECT id, product_id FROM stock_moves WHERE document_id = ? ORDER BY id", (grn["id"],)).fetchall()
        if [m["product_id"] for m in moves] != [it["product_id"] for it in lines]:
            post_stock(grn["id"])  # moves don't match the lines: write them again
            continue
        for m, it in zip(moves, lines):
            net = it["amount"] / it["qty"] if it["qty"] else it["rate"]
            cost = net * factor * (grn["exchange_rate"] or 1) + grn_landed(it["id"]) / it["qty"]
            db.execute("UPDATE stock_moves SET unit_cost = ? WHERE id = ?", (cost, m["id"]))
        for pid in {it["product_id"] for it in lines}:
            recompute_stock(pid, grn["doc_date"])


def issue_cost(return_item):
    """Unit cost a sales-returned line left stock at: return line -> invoice line -> delivery note line."""
    db = get_db()
    row = db.execute("""SELECT m.unit_cost FROM items inv_line
                        JOIN items dn_line ON dn_line.id = inv_line.source_item_id
                        JOIN stock_moves m ON m.document_id = dn_line.document_id AND m.product_id = ?
                        WHERE inv_line.id = ? LIMIT 1""",
                     (return_item["product_id"], return_item["source_item_id"])).fetchone()
    if row:
        return row["unit_cost"]
    return db.execute("SELECT avg_cost FROM products WHERE id = ?", (return_item["product_id"],)).fetchone()[0] or 0


def stock_shortages(doc_id):
    """Items on a Delivery Note / Debit Note that take a product's stock in its warehouse below zero."""
    return get_db().execute("""SELECT p.code, p.name, SUM(m.qty) AS stock_qty, w.code AS wh FROM stock_moves m
        JOIN products p ON p.id = m.product_id JOIN warehouses w ON w.id = m.warehouse_id
        WHERE (m.product_id, m.warehouse_id) IN (SELECT product_id, warehouse_id FROM items WHERE document_id = ?)
        GROUP BY p.id, w.id HAVING SUM(m.qty) < 0""", (doc_id,)).fetchall()


def warn_shortages(doc):
    if doc["doc_type"] in ("DN", "PR"):
        short = stock_shortages(doc["id"])
        if short:
            flash("Stock is now negative for: " + ", ".join(f"{r['code']} {r['name']} in {r['wh']} ({num(r['stock_qty'])})"
                                                             for r in short), "error")


def returned_in(doc):
    """A return made against this invoice (the invoice is then locked), or None."""
    if doc["doc_type"] not in ("INV", "PI"):
        return None
    return get_db().execute("SELECT * FROM documents WHERE parent_id = ? AND doc_type IN ('SR', 'PR')",
                            (doc["id"],)).fetchone()


def invoice_settlement(doc):
    """Paid / outstanding and the receipts / payments of a posted invoice (None for other documents)."""
    if doc["doc_type"] not in ("INV", "PI") or doc["status"] != "Submitted":
        return None
    paid, outstanding = invoice_outstanding(doc["id"])
    vouchers = get_db().execute("""SELECT p.id, p.voucher_no, p.pay_date, p.mode, a.amount FROM payment_allocations a
                                   JOIN payments p ON p.id = a.payment_id WHERE a.document_id = ? AND p.status = 'Posted'
                                   ORDER BY p.pay_date""", (doc["id"],)).fetchall()
    state = "Paid" if outstanding <= 0.004 else ("Partly paid" if paid > 0 else "Unpaid")
    return dict(paid=paid, outstanding=outstanding, vouchers=vouchers, state=state,
                kind="receipt" if doc["doc_type"] == "INV" else "payment")


def is_final(doc):
    return doc["doc_type"] in FINAL_TYPES and doc["status"] == "Submitted"


def can_edit(doc):
    if is_final(doc) or invoiced_in(doc) or returned_in(doc):
        return False  # invoiced GRN / DN or returned invoice: corrections are made with a new document
    return doc["status"] == "Draft" or g.user["role"] == "admin"


@app.route("/billing")
@login_required
def documents():
    q = request.args.get("q", "").strip()
    dtype = request.args.get("type", "")
    status = request.args.get("status", "")
    sql, params = DOC_LIST_SQL, []
    if dtype in DOC_TYPES:
        sql += " AND d.doc_type = ?"
        params.append(dtype)
    else:  # all documents: only the kinds this user may view
        seen = [t for t in DOC_TYPES if user_perms(g.user)[t.lower()] >= VIEW]
        sql += f" AND d.doc_type IN ({','.join('?' * len(seen)) or 'NULL'})"
        params += seen
    if status in ("Draft", "Pending", "Submitted"):
        sql += " AND d.status = ?"
        params.append(status)
    if q:
        sql += (" AND (d.doc_no LIKE ? OR d.cust_name LIKE ? OR d.lpo_no LIKE ? OR d.supplier_do_no LIKE ?"
                " OR d.supplier_inv_no LIKE ?)")
        params += [f"%{q}%"] * 5
    page = page_no()
    docs = get_db().execute(sql + f" ORDER BY d.id DESC LIMIT {PAGE + 1} OFFSET {(page - 1) * PAGE}", params).fetchall()
    has_next, docs = len(docs) > PAGE, docs[:PAGE]
    if dtype == "PO":
        # the list shows each order's lines under the grid and whether a purchase invoice has been made from it
        invoiced = {r[0] for r in get_db().execute(
            """SELECT DISTINCT g.parent_id FROM documents g JOIN doc_sources ds ON ds.source_id = g.id
               JOIN documents pi ON pi.id = ds.doc_id WHERE g.doc_type = 'GRN' AND pi.doc_type = 'PI'""")}
        steps = {r["id"]: r["name"] for r in wf_steps()}
        party = request.args.get("party", type=int)
        new_party = get_db().execute("""SELECT id, name, area, po_box, contact, trn, attention, account_no, country,
                                               contact_name, email, currency FROM customers
                                        WHERE id = ? AND kind = 'supplier'""", (party,)).fetchone() if party else None
        return render_template("po_list.html", docs=docs, q=q, dtype=dtype, status=status, page=page,
                               preview_no=next_doc_no("PO")[0], new_party=dict(new_party) if new_party else None,
                               has_next=has_next, lines={d["id"]: fulfilment(d["id"]) for d in docs},
                               invoiced=invoiced, rejected=po_rejected_ids(), steps=steps)
    if dtype == "SO":
        # same list as purchase orders: each order's lines under the grid, and whether a tax invoice has been made
        invoiced = {r[0] for r in get_db().execute(
            """SELECT DISTINCT n.parent_id FROM documents n JOIN doc_sources ds ON ds.source_id = n.id
               JOIN documents inv ON inv.id = ds.doc_id WHERE n.doc_type = 'DN' AND inv.doc_type = 'INV'""")}
        party = request.args.get("party", type=int)
        new_party = get_db().execute("""SELECT id, name, area, po_box, contact, trn, attention, account_no, country,
                                               contact_name, email, currency FROM customers
                                        WHERE id = ? AND kind = 'customer'""", (party,)).fetchone() if party else None
        return render_template("so_list.html", docs=docs, q=q, dtype=dtype, status=status, page=page,
                               preview_no=next_doc_no("SO")[0], new_party=dict(new_party) if new_party else None,
                               has_next=has_next, lines={d["id"]: fulfilment(d["id"]) for d in docs}, invoiced=invoiced)
    return render_template("documents.html", docs=docs, q=q, dtype=dtype, status=status,
                           page=page, has_next=has_next)


@app.route("/billing/new/<doc_type>", methods=["GET", "POST"])
@app.route("/billing/<int:doc_id>/edit", methods=["GET", "POST"])
@login_required
def doc_form(doc_type=None, doc_id=None):
    db = get_db()
    s = get_settings()
    doc, parent, parents, approval = None, None, [], None
    if doc_id:
        doc = get_doc(doc_id)
        doc_type = doc["doc_type"]
        inv = invoiced_in(doc)
        if inv:
            flash(f"{doc['doc_no']} is invoiced in {inv['doc_no']} and can't be changed. "
                  f"Make a new {DOC_TYPES[doc_type]} for any change.", "error")
            return redirect(url_for("doc_view", doc_id=doc_id))
        if is_final(doc):
            flash(f"{doc['doc_no']} is posted and can't be changed. Corrections are made with a "
                  f"{'Debit' if doc['doc_type'] in PURCHASE_FLOW else 'Credit'} Note.", "error")
            return redirect(url_for("doc_view", doc_id=doc_id))
        ret = returned_in(doc)
        if ret:
            flash(f"{doc['doc_no']} has a return ({ret['doc_no']}) and can't be changed.", "error")
            return redirect(url_for("doc_view", doc_id=doc_id))
        if not can_edit(doc):
            flash(f"{doc['doc_no']} is submitted and locked. Only an admin can edit it.", "error")
            return redirect(url_for("doc_view", doc_id=doc_id))
        parents = sources_of(doc)
        parent = parents[0] if parents else None
    elif doc_type in ("INV", "PI"):
        # an invoice can be made from several GRNs / Delivery Notes of one supplier / customer
        parents, err = invoice_sources(doc_type, request.values.getlist("from"))
        if err:
            flash(err, "error")
            return redirect(url_for("invoice_select", doc_type=doc_type))
        parent = parents[0]
    elif doc_type in PREV_TYPE:
        parent = source_for(doc_type, request.values.get("from"))
        parents = [parent] if parent else []
        if not parent:
            flash(f"A {DOC_TYPES[doc_type]} can only be created from a submitted {DOC_TYPES[PREV_TYPE[doc_type]]} "
                  + ("with quantity still to return." if doc_type in RETURNS else
                     "with quantity still pending." if doc_type in PARTIAL else f"that has no {DOC_TYPES[doc_type]} yet."),
                  "error")
            return redirect(url_for("documents", type=PREV_TYPE[doc_type]))
        if doc_type in RETURNS and g.user["role"] != "admin":
            approval = approved_request(doc_type, parent["id"])
            if not approval:
                flash(f"A {DOC_TYPES[doc_type]} needs admin approval first. Send a request for {parent['doc_no']}.", "error")
                return redirect(url_for("note_request", doc_type=doc_type, inv_id=parent["id"]))
    if doc_type not in DOC_TYPES:
        abort(404)

    if request.method == "POST":
        f = request.form
        if not f.get("cust_name", "").strip():
            flash("Customer name is required.", "error")
            return redirect(request.url)
        # A GRN records the supplier's own Delivery Note number and date
        supplier_do_no = f.get("supplier_do_no", "").strip() if doc_type == "GRN" else ""
        supplier_do_date = f.get("supplier_do_date", "").strip() if doc_type == "GRN" else ""
        if doc_type == "GRN":
            if not supplier_do_no or not supplier_do_date:
                flash("Enter the supplier's Delivery Note No. and DO Date.", "error")
                return redirect(request.url)
            dup = db.execute("""SELECT doc_no FROM documents WHERE doc_type = 'GRN' AND id != ?
                                AND lower(supplier_do_no) = lower(?) AND lower(cust_name) = lower(?)""",
                             (doc["id"] if doc else 0, supplier_do_no, f["cust_name"].strip())).fetchone()
            if dup:
                flash(f"Supplier DO {supplier_do_no} from {f['cust_name'].strip()} is already entered on {dup['doc_no']}.", "error")
                return redirect(request.url)
        if doc_type in TERMS_REQUIRED and not f.get("payment_terms", "").replace("__add__", "").strip():
            flash("Choose the payment terms.", "error")
            return redirect(request.url)
        # A Purchase Invoice records the supplier's own invoice number and date; both are needed to submit it
        supplier_inv_no = f.get("supplier_inv_no", "").strip() if doc_type == "PI" else ""
        supplier_inv_date = f.get("supplier_inv_date", "").strip() if doc_type == "PI" else ""
        if doc_type == "PI":
            err = supplier_inv_error(doc["id"] if doc else 0, f["cust_name"].strip(), supplier_inv_no, supplier_inv_date,
                                     f.get("after") == "submit" or (doc and doc["status"] == "Submitted"))
            if err:
                flash(err, "error")
                return redirect(request.url)
        vat_rate = to_float(f.get("vat_rate"))
        cur, xr, cur_err = doc_currency(doc_type, f, parents[0] if parents else parent)
        if cur_err:
            flash(cur_err, "error")
            return redirect(request.url)
        rows = []
        srcs = f.getlist("source_item_id")
        line_whs = f.getlist("line_wh")
        head_wh = wh_id(f.get("warehouse_id"))
        posted_wh = f.get("warehouse_id", "")
        chosen = posted_wh.isdigit() and wh_id(posted_wh) == int(posted_wh)  # an active warehouse, not the fallback
        if doc_type in ("SO", "PO") and not doc and not chosen and sum(w["active"] for w in warehouse_map().values()) > 1:
            flash("Choose the warehouse for this order.", "error")
            return redirect(request.url)
        for i, title in enumerate(f.getlist("title")):
            details = f.getlist("details")[i]
            if not title.strip() and not details.strip():
                continue
            qty = to_float(f.getlist("qty")[i])
            src_id = int(srcs[i]) if i < len(srcs) and srcs[i].isdigit() else None
            if doc_type in OPEN_TYPES and parent and qty <= 0:
                continue  # nothing received / delivered on this line this time
            unit = f.getlist("unit")[i].strip()
            rate = to_float(f.getlist("rate")[i])
            d_pcts, d_amts = f.getlist("disc_pct"), f.getlist("disc_amt")
            d_pct = to_float(d_pcts[i]) if i < len(d_pcts) else 0.0
            d_amt = to_float(d_amts[i]) if i < len(d_amts) else 0.0
            if not 0 <= d_pct <= 100 or d_amt < 0 or (rate >= 0 and d_amt > rate):
                flash(f"Line {i + 1} ({title.strip() or details.strip()[:30]}): discount % must be 0-100 and the discount "
                      f"can't be more than the unit price.", "error")
                return redirect(request.url)
            value = line_net(qty, rate, d_pct, d_amt)
            vat = r2(value * vat_rate / 100)
            pid, code = None, ""
            if title.strip():
                pids = f.getlist("product_id")
                pid, code = resolve_product(pids[i] if i < len(pids) else None,  # product prices are in base currency
                                            title.strip(), details.strip(), unit, r2(rate * xr), doc_type)
            rows.append((title.strip(), details.strip(), qty, unit, rate, value, vat, r2(value + vat), pid, code, src_id,
                         wh_id(line_whs[i]) if i < len(line_whs) and line_whs[i] else head_wh, d_pct, d_amt))
        if not rows:
            flash("Enter a quantity on at least one item." if doc_type in OPEN_TYPES else "Add at least one item.", "error")
            return redirect(request.url)
        over = []
        if doc_type in OPEN_TYPES and parent:
            open_qty = {l["id"]: l for l in fulfilment(parent["id"], doc["id"] if doc else 0)}
            # a line that lost its link to the order (e.g. an old browser tab) is matched by item name
            free = [l for l in open_qty.values() if l["id"] not in {r[10] for r in rows}]
            for k, r in enumerate(rows):
                if r[10] is None:
                    match = next((l for l in free if l["title"].strip().lower() == r[0].lower()), None)
                    if match:
                        rows[k] = r[:10] + (match["id"],) + r[11:]
                        free.remove(match)
            taken = {}  # order line id -> qty on this document (a line may be split over several rows)
            for r in rows:
                taken[r[10]] = taken.get(r[10], 0) + r[2]
            over = [f"{open_qty[k]['title']} ({num(q)} > {'returnable' if doc_type in RETURNS else 'pending'} "
                    f"{num(open_qty[k]['pending'])})"
                    for k, q in taken.items() if k in open_qty and q > open_qty[k]["pending"] + 1e-9]
            if over and doc_type in RETURNS:  # more can't be returned than was invoiced
                flash("A credit / debit note can't return more than was invoiced: " + "; ".join(over), "error")
                return redirect(request.url)
            if doc_type == "GRN":  # a GRN can't receive more than the PO still has pending, or items not on it
                extra = [r[0] for r in rows if r[10] not in open_qty]
                if over or extra:
                    flash("A GRN can't receive more than the Purchase Order: "
                          + "; ".join(over + [f"{t} is not on {parent['doc_no']}" for t in extra]), "error")
                    return redirect(request.url)
        if doc_type == "PI" and parents:
            # a purchase invoice bills what its GRNs received - never more, so never more than the PO
            ids = [p["id"] for p in parents]
            grn_lines = {r["id"]: r for r in db.execute(f"""SELECT i.id, i.title, i.qty, d.doc_no FROM items i JOIN documents d
                         ON d.id = i.document_id WHERE i.document_id IN ({','.join('?' * len(ids))})""", ids)}
            free = [l for l in grn_lines.values() if l["id"] not in {r[10] for r in rows}]
            for k, r in enumerate(rows):
                if r[10] not in grn_lines:
                    match = next((l for l in free if l["title"].strip().lower() == r[0].lower()), None)
                    rows[k] = r[:10] + (match["id"] if match else None,) + r[11:]
                    if match:
                        free.remove(match)
            taken = {}
            for r in rows:
                taken[r[10]] = taken.get(r[10], 0) + r[2]
            bad = [f"{grn_lines[k]['title']} ({num(q)} > {num(grn_lines[k]['qty'])} received on {grn_lines[k]['doc_no']})"
                   for k, q in taken.items() if k in grn_lines and q > grn_lines[k]["qty"] + 1e-9]
            bad += [f"{r[0]} is not on {', '.join(p['doc_no'] for p in parents)}" for r in rows if r[10] is None]
            if bad:
                flash("A Purchase Invoice can't bill more than was received against the Purchase Order: "
                      + "; ".join(bad), "error")
                return redirect(request.url)
        subtotal = r2(sum(r[5] for r in rows))
        # One document discount, taken off before VAT
        discount_type = "percent" if f.get("discount_type") == "percent" else "amount"
        discount_value = max(0.0, to_float(f.get("discount_value")))
        discount = r2(subtotal * discount_value / 100) if discount_type == "percent" else r2(discount_value)
        discount = min(discount, subtotal)
        vat_amount = r2((subtotal - discount) * vat_rate / 100)
        total_qty = sum(r[2] for r in rows)
        # Landed cost charges (Purchase Invoice only): each in its own currency, no VAT, no discount, shared
        # equally by the lines. A charge with no amount is skipped.
        charges = []  # (description, currency, rate, amount, base amount)
        if doc_type == "PI":
            curs = currency_map()
            for desc, ccy, amt in zip(f.getlist("lc_desc"), f.getlist("lc_cur"), f.getlist("lc_amount")):
                if not amt.strip() or to_float(amt) == 0:
                    continue
                if to_float(amt) < 0:
                    flash(f"Landed cost '{desc.strip() or 'charge'}': the amount can't be negative.", "error")
                    return redirect(request.url)
                ccy = ccy if ccy in curs else cur
                rate = xr if ccy == cur else curs[ccy]["rate"]  # the invoice's own currency keeps the invoice's rate
                charges.append((desc.strip() or "Landed cost", ccy, rate, r2(to_float(amt)), r2(to_float(amt) * rate)))
        base_landed = r2(sum(c[4] for c in charges))
        landed = r2(base_landed / xr)  # in the invoice currency: added to what the vendor is owed
        shares = [r2(base_landed / len(rows))] * len(rows)
        shares[-1] = r2(base_landed - sum(shares[:-1]))  # the cents left over go on the last line

        # Save the customer / supplier to its list if new
        kind = party_kind(doc_type)
        customer_id = f.get("customer_id") or None
        if not customer_id:
            ex = db.execute("SELECT id FROM customers WHERE name = ? AND kind = ?",
                            (f["cust_name"].strip(), kind)).fetchone()
            if ex:
                customer_id = ex["id"]
            else:
                customer_id = db.execute(
                    "INSERT INTO customers(name, area, po_box, contact, trn, attention, kind, created_at) VALUES (?,?,?,?,?,?,?,?)",
                    (f["cust_name"].strip(), f.get("cust_area", ""), f.get("cust_po_box", ""),
                     f.get("cust_contact", ""), f.get("cust_trn", ""), f.get("attention", ""), kind, now())).lastrowid
                log(f"{kind.upper()} ADD", f"Added {kind} '{f['cust_name'].strip()}' (from {DOC_TYPES[doc_type]})")

        fields = dict(
            warehouse_id=head_wh, receipt_date=f.get("receipt_date", "").strip(),
            doc_date=f.get("doc_date") or date.today().isoformat(), customer_id=customer_id,
            cust_name=f["cust_name"].strip(), cust_area=f.get("cust_area", ""), cust_po_box=f.get("cust_po_box", ""),
            cust_contact=f.get("cust_contact", ""), cust_trn=f.get("cust_trn", ""), buyer=f.get("buyer", ""),
            attention=f.get("attention", ""), lpo_no=f.get("lpo_no", ""), delivery_location=f.get("delivery_location", ""),
            payment_terms=f.get("payment_terms", "").replace("__add__", ""), payment_resp=f.get("payment_resp", ""),
            dispatch_mode=f.get("dispatch_mode", ""), goods_desc=f.get("goods_desc", ""), notes=f.get("notes", "").strip(),
            vat_rate=vat_rate, subtotal=subtotal, discount_type=discount_type, discount_value=discount_value,
            discount_amount=discount, vat_amount=vat_amount, total=r2(subtotal - discount + vat_amount + landed),
            landed_amount=landed,
            total_qty=total_qty, supplier_do_no=supplier_do_no, supplier_do_date=supplier_do_date,
            supplier_inv_no=supplier_inv_no, supplier_inv_date=supplier_inv_date,
        )
        fields.update(currency=cur, exchange_rate=xr, base_total=r2(fields["total"] * xr), base_vat=r2(vat_amount * xr))
        submit = f.get("after") == "submit" and (not doc or doc["status"] == "Draft")
        if submit and doc_type != "PO":  # a PO is submitted through submit_po() once it is saved
            fields.update(status="Submitted", submitted_by=g.user["id"], submitted_at=now())
        if doc:
            fields.update(updated_by=g.user["id"], updated_at=now())
            db.execute(f"UPDATE documents SET {', '.join(k + ' = ?' for k in fields)} WHERE id = ?",
                       (*fields.values(), doc["id"]))
            db.execute("DELETE FROM items WHERE document_id = ?", (doc["id"],))
            new_id, doc_no, action = doc["id"], doc["doc_no"], "EDIT"
        else:
            doc_no, n, key = next_doc_no(doc_type)
            fields.update(doc_type=doc_type, doc_no=doc_no, created_by=g.user["id"], created_at=now(),
                          parent_id=parent["id"] if parent else None)
            new_id = db.execute(f"INSERT INTO documents({', '.join(fields)}) VALUES ({', '.join('?' * len(fields))})",
                                tuple(fields.values())).lastrowid
            if doc_type in ("INV", "PI"):
                db.executemany("INSERT INTO doc_sources(doc_id, source_id) VALUES (?, ?)",
                               [(new_id, p["id"]) for p in parents])
            set_setting(f"{key}_next", str(n + 1))
            action = "CREATE"
            if approval:  # the approval is used up by this note
                db.execute("UPDATE note_requests SET status = 'Used', note_id = ? WHERE id = ?", (new_id, approval["id"]))
        for sl, r in enumerate(rows, 1):
            db.execute("""INSERT INTO items(document_id, sl, title, details, qty, unit, rate, amount, vat, line_total,
                          product_id, code, source_item_id, warehouse_id, disc_pct, disc_amt, landed)
                          VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)""", (new_id, sl, *r, shares[sl - 1]))
        db.execute("DELETE FROM landed_costs WHERE doc_id = ?", (new_id,))
        db.executemany("INSERT INTO landed_costs(doc_id, description, currency, rate, amount, base_amount) VALUES (?,?,?,?,?,?)",
                       [(new_id, *c) for c in charges])
        if doc_type in STOCK_DOCS:
            post_stock(new_id)
        if submit:
            post_landed(get_doc(new_id))
        gl_refresh("doc", new_id)
        db.commit()
        waiting = submit_po(get_doc(new_id)) if submit and doc_type == "PO" else None
        summary = f"{DOC_TYPES[doc_type]} {doc_no} - {fields['cust_name']} - {len(rows)} item(s), qty {num(total_qty)}"
        if doc_type not in UNPRICED:
            if discount:
                summary += f", discount {money(discount)}"
            summary += f", total {cur} {money(fields['total'])}" + (f" @ {xr:g} = {s['currency']} {money(fields['base_total'])}"
                                                                     if cur != s["currency"] else "")
        if supplier_do_no:
            summary += f", supplier DO {supplier_do_no} dated {ddmmyyyy(supplier_do_date)}"
        if supplier_inv_no:
            summary += f", supplier invoice {supplier_inv_no} dated {ddmmyyyy(supplier_inv_date)}"
        if landed:
            summary += f", landed cost {money(landed)} (" + ", ".join(f"{c[0]} {c[1]} {money(c[3])}" for c in charges) + ")"
        if parents:
            summary += f" (from {', '.join(p['doc_no'] for p in parents)})"
        log(f"{doc_type} {action}", summary)
        if submit:
            log(f"{doc_type} SUBMIT", f"Submitted {DOC_TYPES[doc_type]} {doc_no}"
                                      + (f" for approval ({waiting['name']})" if waiting else ""))
        flash(f"{DOC_TYPES[doc_type]} {doc_no} " + (f"submitted for approval: waiting for {waiting['name']}" if waiting
                                                      else "submitted" if submit else "saved") + ".", "ok")
        if over:
            flash("More than the pending quantity: " + "; ".join(over), "error")
            log(f"{doc_type} OVER", f"{doc_no}: " + "; ".join(over))
        warn_shortages(get_doc(new_id))
        return redirect(url_for("doc_view", doc_id=new_id))

    src = doc or parent or (order_prefill(doc_type) if doc_type in ("PO", "SO") else None)
    if doc_type in ("PO", "SO") and not src:
        return redirect(url_for("documents", type=doc_type, new=1))  # a new order starts from its Create order panel
    pending = {}  # order line id -> qty still open (for the hints next to Qty)
    if doc:
        items = [dict(r) for r in db.execute("SELECT * FROM items WHERE document_id = ? ORDER BY sl", (doc["id"],))]
        if doc_type in OPEN_TYPES and parent:
            pending = {l["id"]: l["pending"] for l in fulfilment(parent["id"], doc["id"])}
    elif parent and doc_type in OPEN_TYPES:
        # only what is still pending on the order, with the pending quantity filled in
        lines = fulfilment(parent["id"])
        pending = {l["id"]: l["pending"] for l in lines}
        items = [dict(l, qty=l["pending"], source_item_id=l["id"]) for l in lines if l["pending"] > 0]
        if doc_type in RETURNS and parent["discount_amount"]:
            # the invoice discount applies to the returned goods too, as a percentage
            src = dict(parent, discount_type="percent",
                       discount_value=round(parent["discount_amount"] / parent["subtotal"] * 100, 4))
    elif parents:
        items = [dict(r, source_item_id=r["id"], src_doc=p["doc_no"]) for p in parents for r in
                 db.execute("SELECT * FROM items WHERE document_id = ? ORDER BY sl", (p["id"],))]
        if len(parents) > 1:
            # header from the first one; discounts: same % on all keeps the %, otherwise add the amounts
            src = dict(parents[0])
            if {(p["discount_type"], p["discount_value"]) for p in parents} != {("percent", src["discount_value"])}:
                src.update(discount_type="amount", discount_value=sum(p["discount_amount"] or 0 for p in parents))
    else:
        items = []
    pi_refs, pi_pos, pi_party = {}, [], None  # vendor invoice page: GRN line -> its GRN / PO, the POs, the vendor
    if doc_type != "PI" and src and "customer_id" in src.keys():  # document pages show the party's account
        pi_party = db.execute("SELECT * FROM customers WHERE id = ?", (src["customer_id"],)).fetchone()
    if doc_type == "PI" and parents:  # a PI line can bill up to what its GRN line received
        pending = {r["id"]: r["qty"] for p in parents
                   for r in db.execute("SELECT id, qty FROM items WHERE document_id = ?", (p["id"],))}
        ids = [p["id"] for p in parents]
        for r in db.execute(f"""SELECT i.id, d.id AS grn_id, d.doc_no AS grn_no, po.id AS po_id, po.doc_no AS po_no
                                FROM items i JOIN documents d ON d.id = i.document_id LEFT JOIN documents po ON po.id = d.parent_id
                                WHERE i.document_id IN ({','.join('?' * len(ids))})""", ids):
            pi_refs[r["id"]] = dict(r)
        pi_pos = sorted({(r["po_id"], r["po_no"]) for r in pi_refs.values() if r["po_id"]}, key=lambda x: x[1])
        pi_party = db.execute("SELECT * FROM customers WHERE id = ?", (src["customer_id"] if src else None,)).fetchone()
    new_party = None
    if request.args.get("party", type=int):
        new_party = db.execute("SELECT id, name, area, po_box, contact, trn, attention FROM customers WHERE id = ? AND kind = ?",
                               (request.args.get("party", type=int), party_kind(doc_type))).fetchone()
    # where the "+" (add customer / vendor) button comes back to
    back_args = {k: v for k, v in request.args.items() if k != "party"}
    return_url = url_for(request.endpoint, **request.view_args, **back_args)
    return render_template("doc_form.html", doc=doc, d=src, parent=parent, parents=parents, items=items, pending=pending,
                           new_party=dict(new_party) if new_party else None, return_url=return_url,
                           approval=approval, pi_refs=pi_refs, pi_pos=pi_pos, pi_party=pi_party,
                           doc_type=doc_type, charges=landed_charges(doc["id"]) if doc else [],
                           today=request.args.get("doc_date") if not doc and not parent and request.args.get("doc_date")
                           else date.today().isoformat(),
                           preview_no=None if doc else next_doc_no(doc_type)[0])


@app.route("/billing/<int:doc_id>")
@login_required
def doc_view(doc_id):
    db = get_db()
    doc = get_doc(doc_id)
    items = db.execute("SELECT * FROM items WHERE document_id = ? ORDER BY sl", (doc_id,)).fetchall()
    # Walk the whole SO -> DNs -> INVs (or PO -> GRNs -> PIs) tree this document belongs to
    root = doc
    while root["parent_id"]:
        root = get_doc(root["parent_id"])
    level, chain = [root], {}
    for t in flow_of(doc["doc_type"]):
        chain[t] = level
        ids = [d["id"] for d in level]
        marks = ",".join("?" * len(ids))
        level = db.execute(f"""SELECT * FROM documents WHERE parent_id IN ({marks})
                               OR id IN (SELECT doc_id FROM doc_sources WHERE source_id IN ({marks})) ORDER BY id""",
                           ids * 2).fetchall() if ids else []
    children = db.execute(CHILDREN_SQL, (doc_id, doc_id)).fetchall()
    next_type = NEXT_TYPE.get(doc["doc_type"])
    lines = fulfilment(doc_id) if next_type in OPEN_TYPES else []
    open_qty = sum(l["pending"] for l in lines)
    can_next = doc["status"] == "Submitted" and (open_qty > 0 if next_type in OPEN_TYPES else not children)
    users = {r["id"]: r["username"] for r in db.execute("SELECT id, username FROM users")}
    template = "po_view.html" if doc["doc_type"] == "PO" else "doc_view.html"
    party = db.execute("SELECT * FROM customers WHERE id = ?", (doc["customer_id"],)).fetchone() if doc["customer_id"] else None
    is_po = doc["doc_type"] == "PO"
    return render_template(template, doc=doc, items=items, chain=chain, users=users,
                           party=party, history=po_history(doc_id) if is_po else [], approvable=is_po and can_approve(doc),
                           wf_step=current_step(doc) if is_po else None, all_steps=wf_steps() if is_po else [],
                           step_approvers=step_approvers,
                           children=children, next_type=next_type, can_next=can_next,
                           lines=lines, open_qty=open_qty, flow=flow_of(doc["doc_type"]),
                           editable=can_edit(doc), invoiced=invoiced_in(doc), returned=returned_in(doc),
                           req_state=request_state(next_type, doc_id) if next_type in RETURNS else None,
                           final=is_final(doc),
                           settlement=invoice_settlement(doc), charges=landed_charges(doc_id),
                           sources=sources_of(doc))


@app.route("/billing/<int:doc_id>/submit", methods=["POST"])
@login_required
def doc_submit(doc_id):
    doc = get_doc(doc_id)
    if doc["status"] != "Draft":
        flash(f"{doc['doc_no']} is already submitted.", "error")
    elif doc["doc_type"] == "PI" and (err := supplier_inv_error(doc["id"], doc["cust_name"], doc["supplier_inv_no"],
                                                               doc["supplier_inv_date"], True)):
        flash(err + " Edit the draft to enter it, then submit.", "error")
    elif doc["doc_type"] == "PO" and (st := submit_po(doc, request.form.get("remark", "").strip())):
        log("PO SUBMIT", f"Submitted Purchase Order {doc['doc_no']} for approval ({st['name']})")
        flash(f"{doc['doc_no']} submitted for approval: waiting for {st['name']}.", "ok")
    else:
        if doc["doc_type"] != "PO":
            confirm_doc(doc)
        log(f"{doc['doc_type']} SUBMIT", f"Submitted {DOC_TYPES[doc['doc_type']]} {doc['doc_no']}")
        flash(f"{doc['doc_no']} submitted.", "ok")
        warn_shortages(doc)
    return redirect(url_for("doc_view", doc_id=doc_id))


def supplier_inv_error(doc_id, supplier, inv_no, inv_date, submitting):
    """Why a Purchase Invoice's supplier invoice no. / date can't be accepted, or None.

    Both are required to submit (a draft may leave them blank); one supplier's invoice can be booked only once.
    """
    if submitting and (not inv_no or not inv_date):
        return "Enter the supplier's invoice No. and invoice date to submit the Purchase Invoice."
    if inv_no:
        dup = get_db().execute("""SELECT doc_no FROM documents WHERE doc_type = 'PI' AND id != ?
                                  AND lower(supplier_inv_no) = lower(?) AND lower(cust_name) = lower(?)""",
                               (doc_id, inv_no, supplier)).fetchone()
        if dup:
            return f"Supplier invoice {inv_no} from {supplier} is already booked on {dup['doc_no']}."
    return None


def confirm_doc(doc):
    """Make a document Submitted and post its stock and ledger lines. Commits."""
    get_db().execute("UPDATE documents SET status='Submitted', wf_step=NULL, submitted_by=?, submitted_at=? WHERE id=?",
                     (g.user["id"], now(), doc["id"]))
    if doc["doc_type"] in STOCK_DOCS:
        post_stock(doc["id"])
    post_landed(get_doc(doc["id"]))
    gl_refresh("doc", doc["id"])
    get_db().commit()


@app.route("/billing/<int:doc_id>/approve", methods=["POST"])
@login_required
def po_approve(doc_id):
    doc = get_doc(doc_id)
    st = current_step(doc)
    back = request.form.get("next") or url_for("doc_view", doc_id=doc_id)
    if not can_approve(doc):
        flash(f"You can't approve {doc['doc_no']} at this step.", "error")
        return redirect(back)
    wf_log(doc_id, "Approved", st["name"], request.form.get("remark", "").strip())
    nxt = next_step(doc, st["seq"])
    if nxt:
        get_db().execute("UPDATE documents SET wf_step = ? WHERE id = ?", (nxt["id"], doc_id))
        get_db().commit()
        log("PO APPROVE", f"Approved Purchase Order {doc['doc_no']} at {st['name']}; next: {nxt['name']}")
        flash(f"{doc['doc_no']} approved at {st['name']}. Now waiting for {nxt['name']}.", "ok")
    else:
        confirm_doc(doc)
        log("PO APPROVE", f"Approved Purchase Order {doc['doc_no']} at {st['name']} (final approval)")
        flash(f"{doc['doc_no']} fully approved. Goods can now be received against it.", "ok")
    return redirect(back)


@app.route("/billing/<int:doc_id>/reject", methods=["POST"])
@login_required
def po_reject(doc_id):
    doc = get_doc(doc_id)
    st = current_step(doc)
    remark = request.form.get("remark", "").strip()
    back = request.form.get("next") or url_for("doc_view", doc_id=doc_id)
    if not can_approve(doc):
        flash(f"You can't reject {doc['doc_no']} at this step.", "error")
    elif not remark:
        flash("Give a reason for the rejection.", "error")
    else:
        get_db().execute("UPDATE documents SET status = 'Draft', wf_step = NULL WHERE id = ?", (doc_id,))
        wf_log(doc_id, "Rejected", st["name"], remark)
        get_db().commit()
        log("PO REJECT", f"Rejected Purchase Order {doc['doc_no']} at {st['name']}: {remark}")
        flash(f"{doc['doc_no']} rejected and returned to draft.", "ok")
    return redirect(back)


@app.route("/billing/<int:doc_id>/recall", methods=["POST"])
@login_required
def po_recall(doc_id):
    doc = get_doc(doc_id)
    st = current_step(doc)
    if not st or (doc["created_by"] != g.user["id"] and g.user["role"] != "admin"):
        flash(f"You can't recall {doc['doc_no']}.", "error")
    else:
        get_db().execute("UPDATE documents SET status = 'Draft', wf_step = NULL WHERE id = ?", (doc_id,))
        wf_log(doc_id, "Recalled", st["name"], request.form.get("remark", "").strip())
        get_db().commit()
        log("PO RECALL", f"Recalled Purchase Order {doc['doc_no']} from approval")
        flash(f"{doc['doc_no']} recalled to draft.", "ok")
    return redirect(url_for("doc_view", doc_id=doc_id))


@app.route("/purchase/approvals")
@login_required
def po_approvals():
    db = get_db()
    pending = db.execute("""SELECT d.*, u.username AS creator, st.name AS step_name, st.approvers,
                               (SELECT MAX(at) FROM po_workflow w WHERE w.doc_id = d.id) AS since
                            FROM documents d LEFT JOIN users u ON u.id = d.created_by
                            LEFT JOIN po_wf_steps st ON st.id = d.wf_step
                            WHERE d.doc_type = 'PO' AND d.status = 'Pending' ORDER BY d.id""").fetchall()
    history = db.execute("""SELECT w.*, d.doc_no, d.cust_name, d.total, u.username FROM po_workflow w
                            JOIN documents d ON d.id = w.doc_id LEFT JOIN users u ON u.id = w.user_id
                            ORDER BY w.id DESC LIMIT 200""").fetchall()
    names = {r["id"]: r["username"] for r in db.execute("SELECT id, username FROM users")}
    return render_template("po_approvals.html", pending=pending, history=history, names=names,
                           mine=[d for d in pending if can_approve(d)],
                           tab=request.args.get("tab", "mine"), can_approve=can_approve, step_approvers=step_approvers)


@app.route("/purchase/workflow", methods=["GET", "POST"])
@admin_required
def po_workflow_setup():
    db = get_db()
    if request.method == "POST":
        f = request.form
        act = f.get("act")
        if act == "toggle":
            on = f.get("enabled") == "1"
            if on and not wf_steps():
                flash("Add at least one approval step before enabling the workflow.", "error")
            else:
                set_setting("po_wf_enabled", "1" if on else "0")
                db.commit()
                log("PO WORKFLOW", ("Enabled" if on else "Disabled") + " the purchase order approval workflow")
                flash("Approval workflow " + ("enabled." if on else "disabled. New POs are approved on submit."), "ok")
        elif act == "save":
            name = f.get("name", "").strip()
            approvers = ",".join(sorted({x for x in f.getlist("approvers") if x.isdigit()}, key=int))
            if not name or not approvers:
                flash("A step needs a name and at least one approver.", "error")
                return redirect(url_for("po_workflow_setup", edit=f.get("id") or None))
            amount = to_float(f.get("min_amount"))
            if f.get("id"):
                db.execute("UPDATE po_wf_steps SET name = ?, min_amount = ?, approvers = ? WHERE id = ?",
                           (name, amount, approvers, int(f["id"])))
                log("PO WORKFLOW", f"Edited approval step '{name}'")
            else:
                seq = (db.execute("SELECT MAX(seq) FROM po_wf_steps").fetchone()[0] or 0) + 1
                db.execute("INSERT INTO po_wf_steps(seq, name, min_amount, approvers) VALUES (?,?,?,?)",
                           (seq, name, amount, approvers))
                log("PO WORKFLOW", f"Added approval step '{name}'")
            db.commit()
            flash(f"Step '{name}' saved.", "ok")
        elif act in ("up", "down"):
            steps = [dict(r) for r in wf_steps()]
            i = next((k for k, r in enumerate(steps) if r["id"] == int(f.get("id", 0))), None)
            j = None if i is None else (i - 1 if act == "up" else i + 1)
            if i is not None and 0 <= j < len(steps):
                steps[i], steps[j] = steps[j], steps[i]
                for n, r in enumerate(steps, 1):
                    db.execute("UPDATE po_wf_steps SET seq = ? WHERE id = ?", (n, r["id"]))
                db.commit()
        elif act == "delete":
            sid = int(f.get("id", 0))
            if db.execute("SELECT 1 FROM documents WHERE status = 'Pending' AND wf_step = ?", (sid,)).fetchone():
                flash("POs are waiting at this step. Approve, reject or recall them first.", "error")
            else:
                db.execute("DELETE FROM po_wf_steps WHERE id = ?", (sid,))
                if not wf_steps():
                    set_setting("po_wf_enabled", "0")
                db.commit()
                log("PO WORKFLOW", f"Deleted approval step #{sid}")
                flash("Step deleted.", "ok")
        return redirect(url_for("po_workflow_setup"))
    edit = None
    if request.args.get("edit"):
        edit = db.execute("SELECT * FROM po_wf_steps WHERE id = ?", (request.args["edit"],)).fetchone()
    users = db.execute("SELECT id, username, full_name, role FROM users WHERE active = 1 ORDER BY username").fetchall()
    return render_template("po_workflow.html", steps=wf_steps(), users=users, edit=edit,
                           step_approvers=step_approvers,
                           waiting={r[0]: r[1] for r in db.execute("""SELECT wf_step, COUNT(*) FROM documents
                                    WHERE status = 'Pending' GROUP BY wf_step""")})


@app.route("/billing/<int:doc_id>/print")
@login_required
def doc_print(doc_id):
    db = get_db()
    doc = get_doc(doc_id)
    items = db.execute("SELECT * FROM items WHERE document_id = ? ORDER BY sl", (doc_id,)).fetchall()
    sources = sources_of(doc)
    s = get_settings()
    qr_text = (f"{s['company_name']}\nTRN: {s['trn']}\n{DOC_TYPES[doc['doc_type']]}: {doc['doc_no']}\n"
               f"Date: {ddmmyyyy(doc['doc_date'])}\n{party_kind(doc['doc_type']).title()}: {doc['cust_name']}\nTotal Qty: {num(doc['total_qty'])}")
    if doc["doc_type"] not in UNPRICED:
        qr_text += f"\nVAT: {money(doc['vat_amount'])}\nTotal: {doc['currency'] or s['currency']} {money(doc['total'])}"
    svg = qrcode.make(qr_text, image_factory=qrcode.image.svg.SvgPathImage, box_size=10, border=0).to_string(encoding="unicode")
    log(f"{doc['doc_type']} PRINT", f"Printed/viewed {DOC_TYPES[doc['doc_type']]} {doc['doc_no']}")
    return render_template("print.html", doc=doc, items=items, sources=sources, qr=Markup(svg), charges=landed_charges(doc_id),
                           words=amount_in_words(doc["total"], doc["currency"] or s["currency"]))


@app.route("/billing/<int:doc_id>/delete", methods=["POST"])
@admin_required
def doc_delete(doc_id):
    db = get_db()
    doc = get_doc(doc_id)
    if is_final(doc):
        flash(f"{doc['doc_no']} is posted and can't be deleted.", "error")
        return redirect(url_for("doc_view", doc_id=doc_id))
    child = child_of(doc_id)
    if child:
        flash(f"Cannot delete {doc['doc_no']}: {child['doc_no']} was created from it. Delete that first.", "error")
        return redirect(url_for("doc_view", doc_id=doc_id))
    db.execute("DELETE FROM doc_sources WHERE doc_id = ?", (doc_id,))  # frees its GRNs / Delivery Notes
    db.execute("UPDATE note_requests SET status = 'Approved', note_id = NULL WHERE note_id = ?", (doc_id,))
    touched = db.execute("SELECT product_id, MIN(move_date) FROM stock_moves WHERE document_id = ? GROUP BY product_id",
                         (doc_id,)).fetchall()
    db.execute("DELETE FROM stock_moves WHERE document_id = ?", (doc_id,))
    db.execute("DELETE FROM po_workflow WHERE doc_id = ?", (doc_id,))
    db.execute("DELETE FROM landed_costs WHERE doc_id = ?", (doc_id,))
    db.execute("DELETE FROM documents WHERE id = ?", (doc_id,))
    db.execute("DELETE FROM gl_lines WHERE rk = 'doc' AND rid = ?", (doc_id,))
    for pid, from_date in touched:
        recompute_stock(pid, from_date)
    db.commit()
    log(f"{doc['doc_type']} DELETE", f"Deleted {DOC_TYPES[doc['doc_type']]} {doc['doc_no']} - {doc['cust_name']}")
    flash(f"{doc['doc_no']} deleted.", "ok")
    return redirect(url_for("documents"))


@app.route("/billing/returns/<doc_type>")
@login_required
def return_select(doc_type):
    """Submitted invoices that still have quantity that can be returned."""
    if doc_type not in RETURNS:
        abort(404)
    q = request.args.get("q", "").strip()
    rows = get_db().execute(f"""SELECT * FROM (SELECT d.*, {OPEN_QTY_SQL.format(d='d')} AS returnable FROM documents d
                                WHERE d.doc_type = ? AND d.status = 'Submitted' AND (d.doc_no LIKE ? OR d.cust_name LIKE ?)
                                ORDER BY d.id DESC LIMIT 2000) WHERE returnable > 0 LIMIT 200""",
                            (PREV_TYPE[doc_type], f"%{q}%", f"%{q}%")).fetchall()
    states = {r["id"]: request_state(doc_type, r["id"]) for r in rows}
    return render_template("return_select.html", rows=rows, doc_type=doc_type, states=states, q=q)


# ---------------------------------------------------------------- credit / debit note approvals
#
# A normal user asks for permission to post a Credit / Debit Note against one invoice; an admin approves or
# rejects it. One approval allows one note (deleting that note gives the approval back). Admins need none.

def approved_request(doc_type, inv_id):
    return get_db().execute("""SELECT * FROM note_requests WHERE doc_type = ? AND invoice_id = ? AND user_id = ?
                               AND status = 'Approved' AND note_id IS NULL ORDER BY id LIMIT 1""",
                            (doc_type, inv_id, g.user["id"])).fetchone()


def request_state(doc_type, inv_id):
    """'admin', 'approved', 'pending' or None (nothing asked yet / last request rejected) for the current user."""
    if g.user["role"] == "admin":
        return "admin"
    if approved_request(doc_type, inv_id):
        return "approved"
    if get_db().execute("""SELECT 1 FROM note_requests WHERE doc_type = ? AND invoice_id = ? AND user_id = ?
                           AND status = 'Pending'""", (doc_type, inv_id, g.user["id"])).fetchone():
        return "pending"
    return None


@app.route("/billing/returns/<doc_type>/request/<int:inv_id>", methods=["GET", "POST"])
@login_required
def note_request(doc_type, inv_id):
    if doc_type not in RETURNS:
        abort(404)
    inv = get_doc(inv_id)
    if inv["doc_type"] != PREV_TYPE[doc_type] or inv["status"] != "Submitted":
        abort(404)
    state = request_state(doc_type, inv_id)
    if state in ("admin", "approved"):
        return redirect(url_for("doc_form", doc_type=doc_type, **{"from": inv_id}))
    if request.method == "POST" and state != "pending":
        reason = request.form.get("reason", "").strip()
        if not reason:
            flash("Please give the reason for the return.", "error")
        else:
            db = get_db()
            db.execute("INSERT INTO note_requests(doc_type, invoice_id, user_id, reason, created_at) VALUES (?,?,?,?,?)",
                       (doc_type, inv_id, g.user["id"], reason, now()))
            db.commit()
            log(f"{doc_type} REQUEST", f"Requested approval for a {DOC_TYPES[doc_type]} on {inv['doc_no']}: {reason}")
            flash(f"Request sent. An admin must approve it before you can post the {DOC_TYPES[doc_type]}.", "ok")
            return redirect(url_for("my_requests"))
    lines = fulfilment(inv_id)
    return render_template("note_request.html", inv=inv, doc_type=doc_type, state=state, lines=lines)


@app.route("/billing/requests")
@login_required
def my_requests():
    rows = get_db().execute("""SELECT r.*, d.doc_no AS invoice_no, d.cust_name, n.doc_no AS note_no, a.username AS admin_name
                               FROM note_requests r JOIN documents d ON d.id = r.invoice_id
                               LEFT JOIN documents n ON n.id = r.note_id LEFT JOIN users a ON a.id = r.admin_id
                               WHERE r.user_id = ? ORDER BY r.id DESC""", (g.user["id"],)).fetchall()
    return render_template("note_requests.html", rows=rows, admin_view=False)


@app.route("/admin/approvals")
@admin_panel_required
def approvals():
    rows = get_db().execute("""SELECT r.*, d.doc_no AS invoice_no, d.cust_name, d.total AS invoice_total,
                               n.doc_no AS note_no, u.username, a.username AS admin_name
                               FROM note_requests r JOIN documents d ON d.id = r.invoice_id
                               JOIN users u ON u.id = r.user_id LEFT JOIN users a ON a.id = r.admin_id
                               LEFT JOIN documents n ON n.id = r.note_id
                               ORDER BY r.status != 'Pending', r.id DESC LIMIT 300""").fetchall()
    return render_template("note_requests.html", rows=rows, admin_view=True)


@app.route("/admin/approvals/<int:rid>", methods=["POST"])
@admin_panel_required
def approval_decide(rid):
    db = get_db()
    r = db.execute("""SELECT r.*, d.doc_no AS invoice_no, u.username FROM note_requests r
                      JOIN documents d ON d.id = r.invoice_id JOIN users u ON u.id = r.user_id
                      WHERE r.id = ?""", (rid,)).fetchone() or abort(404)
    decision = request.form.get("decision")
    if r["status"] != "Pending" or decision not in ("Approved", "Rejected"):
        flash("This request was already decided.", "error")
        return redirect(url_for("approvals"))
    remark = request.form.get("remark", "").strip()
    db.execute("UPDATE note_requests SET status = ?, admin_id = ?, admin_remark = ?, decided_at = ? WHERE id = ?",
               (decision, g.user["id"], remark, now(), rid))
    db.commit()
    log(f"{r['doc_type']} {'APPROVE' if decision == 'Approved' else 'REJECT'}",
        f"{decision} {r['username']}'s request for a {DOC_TYPES[r['doc_type']]} on {r['invoice_no']}"
        + (f" ({remark})" if remark else ""))
    flash(f"Request from {r['username']} for {r['invoice_no']} {decision.lower()}.", "ok")
    return redirect(url_for("approvals"))


@app.route("/billing/invoice/<doc_type>")
@login_required
def invoice_select(doc_type):
    """Pick one or more submitted, not yet invoiced GRNs / Delivery Notes of one party for a single invoice."""
    if doc_type not in ("INV", "PI"):
        abort(404)
    src_type = PREV_TYPE[doc_type]
    db = get_db()
    pre = request.args.get("from", type=int)
    pre_doc = db.execute("SELECT * FROM documents WHERE id = ?", (pre,)).fetchone() if pre else None
    q = request.args.get("q", "").strip()
    sql = """SELECT d.*, (SELECT GROUP_CONCAT(i.title, ', ') FROM items i WHERE i.document_id = d.id) AS item_names
             FROM documents d WHERE d.doc_type = ? AND d.status = 'Submitted'
             AND NOT EXISTS (SELECT 1 FROM doc_sources ds WHERE ds.source_id = d.id)
             AND (d.doc_no LIKE ? OR d.cust_name LIKE ? OR d.supplier_do_no LIKE ?)"""
    params = [src_type, *[f"%{q}%"] * 3]
    if pre_doc:  # opened from one GRN / Delivery Note: only that party's
        sql += " AND (d.customer_id = ? OR (d.customer_id IS NULL AND lower(d.cust_name) = lower(?)))"
        params += [pre_doc["customer_id"], pre_doc["cust_name"]]
    rows = db.execute(sql + " ORDER BY d.cust_name, d.doc_date, d.id LIMIT 500", params).fetchall()
    party = lambda r: str(r["customer_id"] or r["cust_name"].strip().lower())
    return render_template("invoice_select.html", rows=rows, doc_type=doc_type, src_type=src_type,
                           pre=pre, party=party, q=q)


def amount_in_words(amount, currency):
    ones = ["", "One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine", "Ten", "Eleven",
            "Twelve", "Thirteen", "Fourteen", "Fifteen", "Sixteen", "Seventeen", "Eighteen", "Nineteen"]
    tens = ["", "", "Twenty", "Thirty", "Forty", "Fifty", "Sixty", "Seventy", "Eighty", "Ninety"]

    def words(n):
        if n < 20:
            return ones[n]
        if n < 100:
            return (tens[n // 10] + " " + ones[n % 10]).strip()
        if n < 1000:
            return (ones[n // 100] + " Hundred " + words(n % 100)).strip()
        for div, name in ((10**9, "Billion"), (10**6, "Million"), (1000, "Thousand")):
            if n >= div:
                return (words(n // div) + f" {name} " + words(n % div)).strip()

    amount = round(amount or 0, 2)
    whole, fils = int(amount), int(round((amount - int(amount)) * 100))
    text = f"{currency} {words(whole) or 'Zero'}"
    if fils:
        text += f" and Fils {words(fils)}"
    return text + " Only"


# ---------------------------------------------------------------- customers

@app.route("/customers", methods=["GET", "POST"], defaults={"kind": "customer"})
@app.route("/suppliers", methods=["GET", "POST"], defaults={"kind": "supplier"}, endpoint="suppliers")
@login_required
def customers(kind):
    db = get_db()
    endpoint = kind + "s"
    # opened with "+" from an order: after adding, go back to that order with the new party filled in
    back = request.values.get("next", "")
    back = back if back.startswith("/") and not back.startswith("//") else ""
    edit = None
    if request.args.get("edit"):
        edit = db.execute("SELECT * FROM customers WHERE id = ? AND kind = ?", (request.args["edit"], kind)).fetchone()
    if request.method == "POST":
        f = request.form
        vals = tuple(f.get(k, "").strip() for k in PARTY_FIELDS)
        vals = vals[:7] + ((vals[7].upper() or next_account_no(db, kind)),) + vals[8:11] \
            + ((vals[11].upper() if vals[11].upper() in currency_map() else base_currency()),)
        dup = db.execute("SELECT id FROM customers WHERE kind = ? AND lower(name) = lower(?) AND id != ?",
                         (kind, vals[0], f.get("id") or 0)).fetchone()
        dup_acc = db.execute("SELECT name FROM customers WHERE kind = ? AND upper(account_no) = ? AND id != ?",
                             (kind, vals[7], f.get("id") or 0)).fetchone()
        email = vals[10]
        if not vals[0]:
            flash(f"{kind.title()} name is required.", "error")
        elif dup or dup_acc or (email and ("@" not in email or " " in email)):
            flash(f"A {MASTER_WORD[kind].lower()} named '{vals[0]}' already exists." if dup else
                  f"Account number {vals[7]} is already used by {dup_acc['name']}." if dup_acc else
                  f"'{email}' is not a valid e-mail address.", "error")
            return redirect(url_for(endpoint, next=back, edit=f.get("id") or None) if back or f.get("id")
                            else url_for(endpoint))
        elif f.get("id"):
            db.execute(f"UPDATE customers SET {', '.join(k + '=?' for k in PARTY_FIELDS)} WHERE id=? AND kind=?",
                       (*vals, f["id"], kind))
            db.commit()
            log(f"{kind.upper()} EDIT", f"Edited {kind} '{vals[0]}'")
            flash(f"{kind.title()} updated.", "ok")
        else:
            new_id = db.execute(f"INSERT INTO customers({', '.join(PARTY_FIELDS)}, kind, created_at) "
                                f"VALUES ({', '.join('?' * (len(PARTY_FIELDS) + 2))})", (*vals, kind, now())).lastrowid
            db.commit()
            log(f"{kind.upper()} ADD", f"Added {kind} '{vals[0]}'" + (" (from an order)" if back else ""))
            flash(f"{MASTER_WORD[kind]} '{vals[0]}' added as {vals[7]}.", "ok")
            if back:
                return redirect(back + ("&" if "?" in back else "?") + f"party={new_id}")
        return redirect(url_for(endpoint))
    q, page = request.args.get("q", "").strip(), page_no()
    rows = db.execute(f"""SELECT * FROM customers WHERE kind = ? AND (name LIKE ? OR trn LIKE ? OR contact LIKE ?
                              OR account_no LIKE ? OR contact_name LIKE ? OR email LIKE ? OR entity_code LIKE ?)
                          ORDER BY account_no, name LIMIT {PAGE + 1} OFFSET {(page - 1) * PAGE}""",
                      (kind, *[f"%{q}%"] * 7)).fetchall()
    bal = party_balance_map(kind, [r["id"] for r in rows])
    return render_template("customers.html", rows=[dict(r, balance=bal.get(r["id"], 0)) for r in rows[:PAGE]], edit=edit,
                           kind=kind, endpoint=endpoint, q=q, page=page, has_next=len(rows) > PAGE, back=back,
                           word=MASTER_WORD[kind], next_no=next_account_no(db, kind),
                           entity_default=db.execute("""SELECT entity_code FROM customers WHERE kind = ? AND entity_code != ''
                                                       ORDER BY id DESC LIMIT 1""", (kind,)).fetchone())


MASTER_WORD = {"customer": "Customer", "supplier": "Vendor"}
PARTY_FIELDS = ("name", "area", "po_box", "contact", "trn", "attention", "entity_code", "account_no", "country",
                "contact_name", "email", "currency")


def next_account_no(db, kind):
    """Next free account number: V000001... for vendors, C000001... for customers."""
    prefix = "V" if kind == "supplier" else "C"
    last = db.execute("""SELECT MAX(CAST(substr(account_no, 2) AS INTEGER)) FROM customers
                         WHERE kind = ? AND account_no GLOB ?""", (kind, prefix + "[0-9]*")).fetchone()[0] or 0
    return f"{prefix}{last + 1:06d}"


@app.route("/customers/<int:cid>/delete", methods=["POST"])
@admin_required
def customer_delete(cid):
    db = get_db()
    c = db.execute("SELECT * FROM customers WHERE id = ?", (cid,)).fetchone() or abort(404)
    db.execute("DELETE FROM customers WHERE id = ?", (cid,))
    db.commit()
    log(f"{c['kind'].upper()} DELETE", f"Deleted {c['kind']} '{c['name']}'")
    flash(f"{c['kind'].title()} deleted.", "ok")
    return redirect(url_for(c["kind"] + "s"))


# ---------------------------------------------------------------- products

@app.route("/api/products")
@login_required
def api_products():
    """Products matching what is typed (code or name), for the item suggestions; never the whole list."""
    q = request.args.get("q", "").strip()
    wh = request.args.get("wh", type=int)
    stock = ("COALESCE((SELECT SUM(m.qty) FROM stock_moves m WHERE m.product_id = p.id AND m.warehouse_id = ?), 0)"
             if wh else "p.stock_qty")
    rows = get_db().execute(f"""SELECT id, code, name, details, unit, sale_price, purchase_price, {stock} AS stock_qty
                                FROM products p WHERE active = 1 AND (code LIKE ? OR name LIKE ?)
                                ORDER BY lower(code) = lower(?) DESC, name LIMIT 15""",
                            ([wh] if wh else []) + [f"%{q}%", f"%{q}%", q]).fetchall()
    return jsonify([dict(r) for r in rows])


@app.route("/api/parties")
@login_required
def api_parties():
    """Customers or suppliers matching what is typed, for the saved-party list on documents."""
    kind = "supplier" if request.args.get("kind") == "supplier" else "customer"
    q = request.args.get("q", "").strip()
    rows = get_db().execute("""SELECT id, name, area, po_box, contact, trn, attention, account_no, country, contact_name,
                                      email, currency FROM customers WHERE kind = ? AND (name LIKE ? OR account_no LIKE ?)
                               ORDER BY name LIMIT 20""", (kind, f"%{q}%", f"%{q}%")).fetchall()
    return jsonify([dict(r) for r in rows])


@app.route("/products", methods=["GET", "POST"])
@login_required
def products():
    db = get_db()
    edit = None
    if request.args.get("edit"):
        edit = db.execute("SELECT * FROM products WHERE id = ?", (request.args["edit"],)).fetchone()
    if request.method == "POST":
        f = request.form
        name = f.get("name", "").strip()
        vals = (name, f.get("details", "").strip(), f.get("unit", "").strip(),
                to_float(f.get("sale_price")), to_float(f.get("purchase_price")), 1 if f.get("active") else 0)
        dup = db.execute("SELECT code FROM products WHERE lower(name) = lower(?) AND id != ?",
                         (name, f.get("id") or 0)).fetchone()
        if not name:
            flash("Product name is required.", "error")
        elif dup:
            flash(f"A product with this name already exists ({dup['code']}).", "error")
        elif f.get("id"):
            db.execute("UPDATE products SET name=?, details=?, unit=?, sale_price=?, purchase_price=?, active=? WHERE id=?",
                       (*vals, f["id"]))
            code = db.execute("SELECT code FROM products WHERE id = ?", (f["id"],)).fetchone()["code"]
            db.commit()
            log("PRODUCT EDIT", f"Edited product {code} '{name}'")
            flash(f"Product {code} updated.", "ok")
        else:
            code, n = next_product_code()
            db.execute("""INSERT INTO products(name, details, unit, sale_price, purchase_price, active, code, created_by, created_at)
                          VALUES (?,?,?,?,?,?,?,?,?)""", (*vals, code, g.user["id"], now()))
            set_setting("item_next", str(n + 1))
            db.commit()
            log("PRODUCT ADD", f"Added product {code} '{name}'")
            flash(f"Product {code} added.", "ok")
        return redirect(url_for("products"))
    q, page = request.args.get("q", "").strip(), page_no()
    rows = db.execute(f"""SELECT p.*, (SELECT COUNT(*) FROM items i WHERE i.product_id = p.id) AS used
                          FROM products p WHERE p.code LIKE ? OR p.name LIKE ? OR p.details LIKE ?
                          ORDER BY p.code LIMIT {PAGE + 1} OFFSET {(page - 1) * PAGE}""", (f"%{q}%",) * 3).fetchall()
    return render_template("products.html", rows=rows[:PAGE], edit=edit, q=q, page=page, has_next=len(rows) > PAGE,
                           next_code=None if edit else next_product_code()[0])


@app.route("/products/<int:pid>/delete", methods=["POST"])
@admin_required
def product_delete(pid):
    db = get_db()
    p = db.execute("SELECT * FROM products WHERE id = ?", (pid,)).fetchone() or abort(404)
    if (db.execute("SELECT 1 FROM items WHERE product_id = ?", (pid,)).fetchone()
            or db.execute("SELECT 1 FROM stock_moves WHERE product_id = ?", (pid,)).fetchone()):
        flash(f"{p['code']} is used on documents, so it can't be deleted. Untick 'Active' to hide it instead.", "error")
        return redirect(url_for("products"))
    db.execute("DELETE FROM products WHERE id = ?", (pid,))
    db.commit()
    log("PRODUCT DELETE", f"Deleted product {p['code']} '{p['name']}'")
    flash(f"Product {p['code']} deleted.", "ok")
    return redirect(url_for("products"))


# ---------------------------------------------------------------- inventory pages

@app.route("/inventory")
@login_required
def inventory():
    db = get_db()
    q, page = request.args.get("q", "").strip(), page_no()
    wh = request.args.get("wh", type=int)
    wh = wh if wh in warehouse_map() else None
    # quantity shown: the product's total, or what is in the chosen warehouse
    qty = ("COALESCE((SELECT SUM(m.qty) FROM stock_moves m WHERE m.product_id = p.id AND m.warehouse_id = :wh), 0)"
           if wh else "p.stock_qty")
    rows = db.execute(f"""SELECT * FROM (SELECT p.*, {qty} AS qty,
            (SELECT MAX(move_date) FROM stock_moves m WHERE m.product_id = p.id
                AND (:wh IS NULL OR m.warehouse_id = :wh)) AS last_move
            FROM products p WHERE (p.code LIKE :q OR p.name LIKE :q)
              AND (:wh IS NULL OR p.id IN (SELECT product_id FROM stock_moves WHERE warehouse_id = :wh)))
            ORDER BY code LIMIT {PAGE + 1} OFFSET {(page - 1) * PAGE}""", {"q": f"%{q}%", "wh": wh}).fetchall()
    summary = db.execute(f"""SELECT COALESCE(SUM(CASE WHEN t.q > 0 THEN t.q * p.avg_cost END), 0), SUM(t.q > 0), SUM(t.q < 0)
                             FROM (SELECT p.id, {qty} AS q FROM products p) t JOIN products p ON p.id = t.id""",
                         {"wh": wh}).fetchone()
    has_next, rows = len(rows) > PAGE, rows[:PAGE]
    by_wh = {}  # product id -> [(warehouse code, qty)]
    if rows and not wh:
        ids = [r["id"] for r in rows]
        for r in db.execute(f"""SELECT m.product_id, w.code, SUM(m.qty) FROM stock_moves m JOIN warehouses w ON w.id = m.warehouse_id
                                WHERE m.product_id IN ({",".join("?" * len(ids))}) GROUP BY m.product_id, w.id
                                HAVING SUM(m.qty) != 0 ORDER BY w.code""", ids):
            by_wh.setdefault(r[0], []).append((r[1], r[2]))
    return render_template("inventory.html", rows=rows, q=q, wh=wh, by_wh=by_wh, total=summary[0],
                           in_stock=summary[1] or 0, negative=summary[2] or 0, today=date.today().isoformat(),
                           page=page, has_next=has_next)


@app.route("/inventory/<int:pid>")
@login_required
def stock_ledger(pid):
    db = get_db()
    p = db.execute("SELECT * FROM products WHERE id = ?", (pid,)).fetchone() or abort(404)
    page = page_no()
    wh = request.args.get("wh", type=int)
    wh = wh if wh in warehouse_map() else None
    moves = db.execute(f"""SELECT * FROM (SELECT m.*, u.username, w.code AS wh_code,
                               SUM(m.qty) OVER (PARTITION BY m.warehouse_id ORDER BY m.move_date, m.id) AS wh_balance
                           FROM stock_moves m LEFT JOIN users u ON u.id = m.created_by
                           LEFT JOIN warehouses w ON w.id = m.warehouse_id WHERE m.product_id = :pid)
                           WHERE :wh IS NULL OR warehouse_id = :wh ORDER BY move_date, id
                           LIMIT {PAGE + 1} OFFSET {(page - 1) * PAGE}""", {"pid": pid, "wh": wh}).fetchall()
    by_wh = db.execute("""SELECT w.id, w.code, w.name, SUM(m.qty) AS qty FROM stock_moves m JOIN warehouses w ON w.id = m.warehouse_id
                          WHERE m.product_id = ? GROUP BY w.id ORDER BY w.code""", (pid,)).fetchall()
    return render_template("stock_ledger.html", p=p, moves=moves[:PAGE], page=page, has_next=len(moves) > PAGE,
                           wh=wh, by_wh=by_wh)


# Inventory transactions: every stock movement line by line, as on the Dynamics inquiry. The quantity still open on a
# purchase order line is "Ordered" and on a sales order line "On order" (from the moment the line is created). A receipt
# is "Received" until its line is on a posted purchase invoice ("Purchased"); an issue is "Deducted" until invoiced
# ("Sold"). Notes, stock entries and adjustments are financial at once. The financial date is the invoice date (or the
# movement date). Order lines move no stock: no physical date, no cost amount.
INV_TRANS_SQL = """
WITH t AS (
  SELECT m.id, m.move_date, m.kind, m.qty, m.value, m.unit_cost, m.document_id, m.entry_id, m.note,
         p.id AS pid, p.code, p.name, COALESCE(NULLIF(it.unit, ''), p.unit) AS unit, w.code AS wh, m.warehouse_id,
         d.doc_no, d.cust_name AS party, o.id AS order_id, o.doc_no AS order_no,
         CASE m.kind WHEN 'GRN' THEN 'Purchase order' WHEN 'DN' THEN 'Sales order' WHEN 'SR' THEN 'Sales return'
              WHEN 'PR' THEN 'Purchase return' WHEN 'SIN' THEN 'Stock in' WHEN 'SOUT' THEN 'Stock out'
              ELSE 'Adjustment' END AS reference,
         CASE WHEN m.kind IN ('GRN', 'DN') THEN COALESCE(o.doc_no, d.doc_no)
              WHEN m.kind = 'ADJ' THEN 'ADJ-' || m.id ELSE m.ref END AS number,
         COALESCE((SELECT SUM(il.qty) FROM items il JOIN documents x ON x.id = il.document_id
                   WHERE il.source_item_id = m.item_id AND x.status = 'Submitted' AND x.doc_type IN ('INV', 'PI')), 0) AS inv_qty,
         (SELECT x.id FROM items il JOIN documents x ON x.id = il.document_id WHERE il.source_item_id = m.item_id
            AND x.status = 'Submitted' AND x.doc_type IN ('INV', 'PI') ORDER BY x.doc_date, x.id LIMIT 1) AS inv_id
  FROM stock_moves m JOIN products p ON p.id = m.product_id
  LEFT JOIN warehouses w ON w.id = m.warehouse_id
  LEFT JOIN documents d ON d.id = m.document_id
  LEFT JOIN documents o ON o.id = d.parent_id AND m.kind IN ('GRN', 'DN')
  LEFT JOIN items it ON it.id = m.item_id
  UNION ALL
  -- what is still open on purchase / sales order lines (ordered less what submitted GRNs / delivery notes moved)
  SELECT -ol.id, o.doc_date, o.doc_type,
         (CASE o.doc_type WHEN 'PO' THEN 1 ELSE -1 END) * (ol.qty - COALESCE((SELECT SUM(cl.qty) FROM items cl
             JOIN documents c ON c.id = cl.document_id WHERE cl.source_item_id = ol.id AND c.status = 'Submitted'
             AND c.doc_type IN ('GRN', 'DN')), 0)),
         NULL, NULL, o.id, NULL, '', p.id, p.code, p.name, COALESCE(NULLIF(ol.unit, ''), p.unit), w.code,
         COALESCE(ol.warehouse_id, o.warehouse_id), NULL, o.cust_name, NULL, NULL,
         CASE o.doc_type WHEN 'PO' THEN 'Purchase order' ELSE 'Sales order' END, o.doc_no, 0, NULL
  FROM items ol JOIN documents o ON o.id = ol.document_id AND o.doc_type IN ('PO', 'SO')
  JOIN products p ON p.id = ol.product_id
  LEFT JOIN warehouses w ON w.id = COALESCE(ol.warehouse_id, o.warehouse_id)
  WHERE ol.qty - COALESCE((SELECT SUM(cl.qty) FROM items cl JOIN documents c ON c.id = cl.document_id
            WHERE cl.source_item_id = ol.id AND c.status = 'Submitted' AND c.doc_type IN ('GRN', 'DN')), 0) > 1e-9
),
v AS (
  SELECT t.*, x.doc_no AS inv_no,
         CASE WHEN kind IN ('PO', 'SO') THEN NULL WHEN kind NOT IN ('GRN', 'DN') THEN move_date ELSE x.doc_date END AS fin_date,
         CASE WHEN kind IN ('PO', 'SO') THEN 0 WHEN kind NOT IN ('GRN', 'DN') OR inv_qty >= ABS(qty) - 1e-9 THEN 1
              ELSE 0 END AS financial,
         CASE WHEN kind IN ('PO', 'SO') THEN 1 ELSE 0 END AS ordered
  FROM t LEFT JOIN documents x ON x.id = t.inv_id
)
SELECT v.*, CASE WHEN ordered THEN NULL ELSE move_date END AS phys_date,
       CASE WHEN qty > 0 THEN CASE WHEN ordered THEN 'Ordered' WHEN financial THEN 'Purchased'
                              WHEN inv_qty > 0 THEN 'Received (part invoiced)' ELSE 'Received' END END AS receipt,
       CASE WHEN qty < 0 THEN CASE WHEN ordered THEN 'On order' WHEN financial THEN 'Sold'
                              WHEN inv_qty > 0 THEN 'Deducted (part invoiced)' ELSE 'Deducted' END END AS issue,
       CASE WHEN ordered THEN NULL WHEN qty < 0 THEN -value ELSE value END AS cost
FROM v WHERE 1 = 1"""
INV_REFERENCES = ("Purchase order", "Sales order", "Sales return", "Purchase return", "Stock in", "Stock out", "Adjustment")


def inv_trans_query(args):
    sql, params = INV_TRANS_SQL, {}
    if args.get("q", "").strip():
        sql += """ AND (code LIKE :q OR name LIKE :q OR number LIKE :q OR doc_no LIKE :q OR inv_no LIKE :q
                   OR party LIKE :q OR note LIKE :q)"""
        params["q"] = f"%{args['q'].strip()}%"
    if args.get("wh", "").isdigit():
        sql += " AND warehouse_id = :wh"
        params["wh"] = int(args["wh"])
    if args.get("ref") in INV_REFERENCES:
        sql += " AND reference = :ref"
        params["ref"] = args["ref"]
    if args.get("dir") in ("in", "out"):
        sql += " AND qty > 0" if args["dir"] == "in" else " AND qty < 0"
    sql += {"ordered": " AND ordered = 1", "physical": " AND ordered = 0 AND financial = 0",
            "financial": " AND financial = 1", "moved": " AND ordered = 0"}.get(args.get("status"), "")
    for key, op in (("from", ">="), ("to", "<=")):
        if args.get(key):
            sql += f" AND move_date {op} :{key}"
            params[key] = args[key]
    return sql, params


@app.route("/inventory/transactions")
@login_required
def inventory_transactions():
    db = get_db()
    sql, params = inv_trans_query(request.args)
    if request.args.get("export"):
        out = io.StringIO()
        w = csv.writer(out)
        w.writerow(["Item number", "Item name", "Physical date", "Financial date", "Reference", "Number", "Document",
                    "Invoice", "Party", "Warehouse", "Receipt", "Issue", "Quantity", "Unit", "Cost amount"])
        for r in db.execute(sql + " ORDER BY move_date DESC, id DESC", params):
            w.writerow([r["code"], r["name"], r["phys_date"] or "", r["fin_date"] or "", r["reference"], r["number"],
                        r["doc_no"] or "", r["inv_no"] or "", r["party"] or "", r["wh"] or "", r["receipt"] or "",
                        r["issue"] or "", r["qty"], r["unit"], "" if r["cost"] is None else round(r["cost"], 2)])
        log("STOCK EXPORT", "Exported inventory transactions to CSV")
        return Response("\ufeff" + out.getvalue(), mimetype="text/csv",
                        headers={"Content-Disposition": "attachment; filename=inventory_transactions.csv"})
    page = page_no()
    rows = db.execute(sql + f" ORDER BY move_date DESC, id DESC LIMIT {PAGE + 1} OFFSET {(page - 1) * PAGE}", params).fetchall()
    totals = db.execute(f"""SELECT COUNT(*) AS n, SUM(CASE WHEN qty > 0 AND NOT ordered THEN qty END) AS qin,
                            SUM(CASE WHEN qty < 0 AND NOT ordered THEN -qty END) AS qout, SUM(cost) AS cost,
                            SUM(CASE WHEN ordered AND qty > 0 THEN qty END) AS qordered,
                            SUM(CASE WHEN ordered AND qty < 0 THEN -qty END) AS qonorder FROM ({sql})""", params).fetchone()
    return render_template("inventory_transactions.html", rows=rows[:PAGE], page=page, has_next=len(rows) > PAGE,
                           count=totals["n"], totals=totals, references=INV_REFERENCES)


@app.route("/ledger/fiscal", methods=["GET", "POST"])
@login_required
def fiscal_calendar():
    db = get_db()
    years = db.execute("SELECT * FROM fiscal_years ORDER BY start_date").fetchall()
    if request.method == "POST":
        f = request.form
        if f.get("action") == "add_year":
            try:
                start = date.fromisoformat(f.get("start_date", "")).replace(day=1)
            except ValueError:
                flash("Enter the first day of the new fiscal year.", "error")
                return redirect(url_for("fiscal_calendar"))
            end = add_months(start, 12) - timedelta(days=1)
            name = f.get("name", "").strip() or f"FY{start.year}"
            clash = db.execute("SELECT name FROM fiscal_years WHERE start_date <= ? AND end_date >= ? OR name = ?",
                               (end.isoformat(), start.isoformat(), name)).fetchone()
            if clash:
                flash(f"It overlaps or shares its name with fiscal year {clash['name']}.", "error")
                return redirect(url_for("fiscal_calendar"))
            yid = add_fiscal_year(db, name, start, g.user["id"])
            db.commit()
            log("FISCAL YEAR ADD", f"Fiscal year {name}: {ddmmyyyy(start.isoformat())} - {ddmmyyyy(end.isoformat())}, 12 periods, open")
            flash(f"Fiscal year {name} created with 12 open periods.", "ok")
            return redirect(url_for("fiscal_calendar", year=yid))
        yid = f.get("year_id", type=int)
        changes = []
        for per in db.execute("SELECT * FROM fiscal_periods WHERE year_id = ? ORDER BY seq", (yid,)).fetchall():
            if per["status"] == "Closed":
                continue  # closed for good
            status = f.get(f"status_{per['id']}", per["status"])
            status = status if status in PERIOD_STATUSES else per["status"]
            holds = {m: 1 if f.get(f"hold_{m}_{per['id']}") else 0 for m, _ in PERIOD_MODULES}
            if status == per["status"] and all(holds[m] == per["hold_" + m] for m in holds):
                continue
            db.execute(f"""UPDATE fiscal_periods SET status = ?, {', '.join(f'hold_{m} = ?' for m in holds)},
                           updated_by = ?, updated_at = ? WHERE id = ?""", (status, *holds.values(), g.user["id"], now(), per["id"]))
            held = [n for m, n in PERIOD_MODULES if holds[m]]
            changes.append(f"{per['name']}: {status}" + (f" (on hold: {', '.join(held)})" if held and status == "Open" else ""))
        db.commit()
        if changes:
            log("FISCAL PERIODS", "; ".join(changes))
            flash(f"{len(changes)} period(s) updated.", "ok")
        return redirect(url_for("fiscal_calendar", year=yid))
    year = next((y for y in years if y["id"] == request.args.get("year", type=int)), None) or \
        next((y for y in years if y["start_date"] <= date.today().isoformat() <= y["end_date"]), None) or (years[-1] if years else None)
    periods = db.execute("""SELECT p.*, u.username FROM fiscal_periods p LEFT JOIN users u ON u.id = p.updated_by
                            WHERE year_id = ? ORDER BY seq""", (year["id"] if year else 0,)).fetchall()
    next_start = add_months(date.fromisoformat(years[-1]["end_date"]), 1) if years else date(date.today().year, 1, 1)
    return render_template("fiscal.html", years=years, year=year, periods=periods, pmods=PERIOD_MODULES,
                           statuses=PERIOD_STATUSES, next_start=next_start.isoformat(), today=date.today().isoformat())


@app.route("/inventory/adjust", methods=["POST"])
@admin_required
def stock_adjust():
    """Opening stock or a correction: positive qty adds stock at the given cost, negative removes at average cost."""
    db = get_db()
    f = request.form
    p = db.execute("SELECT * FROM products WHERE id = ?", (f.get("product_id"),)).fetchone()
    qty = to_float(f.get("qty"))
    if not p or not qty:
        flash("Choose a product and enter a quantity (negative to reduce stock).", "error")
        return redirect(url_for("inventory"))
    cost = to_float(f.get("unit_cost")) if f.get("unit_cost", "").strip() else p["avg_cost"]
    note = f.get("note", "").strip()
    move_date = f.get("move_date") or date.today().isoformat()
    wid = wh_id(f.get("warehouse_id"))
    mid = db.execute("""INSERT INTO stock_moves(product_id, move_date, kind, ref, note, qty, unit_cost, warehouse_id,
                        created_by, created_at) VALUES (?,?,?,?,?,?,?,?,?,?)""",
                     (p["id"], move_date, "ADJ", "Adjustment", note, qty, cost if qty > 0 else 0, wid,
                      g.user["id"], now())).lastrowid
    recompute_stock(p["id"], move_date)
    gl_refresh("adj", mid)
    db.commit()
    p = db.execute("SELECT * FROM products WHERE id = ?", (p["id"],)).fetchone()
    log("STOCK ADJUST", f"{p['code']} '{p['name']}' {'+' if qty > 0 else ''}{num(qty)} {p['unit']}"
        + f" in {warehouse_map()[wid]['code']}"
        + (f" @ {money(cost)}" if qty > 0 else "") + f" -> stock {num(p['stock_qty'])}, avg cost {p['avg_cost']:.4f}"
        + (f" ({note})" if note else ""))
    flash(f"Stock adjusted: {p['code']} now {num(p['stock_qty'])} {p['unit']} at avg cost {p['avg_cost']:.4f}.", "ok")
    return redirect(url_for("stock_ledger", pid=p["id"]))


@app.route("/ledger/currencies", methods=["GET", "POST"])
@login_required
def currencies_page():
    db = get_db()
    base = base_currency()
    if request.method == "POST":
        if g.user["role"] != "admin":
            flash("Admin access required.", "error")
            return redirect(url_for("currencies_page"))
        f = request.form
        code, name = f.get("code", "").strip().upper(), f.get("name", "").strip()
        rate = 1.0 if code == base else to_float(f.get("rate"))
        if f.get("act") == "toggle":
            c = currency_map().get(code)
            if c and code != base:
                db.execute("UPDATE currencies SET active = ? WHERE code = ?", (0 if c["active"] else 1, code))
                log("CURRENCY", f"{'Deactivated' if c['active'] else 'Activated'} currency {code}")
        elif len(code) != 3 or not code.isalpha() or not name or rate <= 0:
            flash("Enter a 3-letter code, a name and a rate above zero.", "error")
            return redirect(url_for("currencies_page", edit=code if code in currency_map() else None))
        else:
            old = currency_map().get(code)
            db.execute("""INSERT INTO currencies(code, name, rate, updated_at) VALUES (?,?,?,?)
                          ON CONFLICT(code) DO UPDATE SET name = excluded.name, rate = excluded.rate,
                          updated_at = excluded.updated_at""", (code, name, rate, now()))
            log("CURRENCY", f"{'Updated' if old else 'Added'} currency {code} {name}, rate {rate:g} {base}"
                + (f" (was {old['rate']:g})" if old and old["rate"] != rate else ""))
            flash(f"{code} saved: 1 {code} = {rate:g} {base}. New purchase orders use this rate; existing ones keep theirs.", "ok")
        db.commit()
        return redirect(url_for("currencies_page"))
    used = {r[0]: r[1] for r in db.execute("SELECT currency, COUNT(*) FROM documents GROUP BY currency")}
    return render_template("currencies.html", rows=list(currency_map().values()), used=used,
                           edit=currency_map().get((request.args.get("edit") or "").upper()))


@app.route("/api/payment-terms", methods=["POST"])
@login_required
def api_payment_term_add():
    """Add a payment term from the "+ Add new" entry of a payment terms dropdown; an existing name is reused."""
    db = get_db()
    name, days = request.form.get("name", "").strip(), int(to_float(request.form.get("days")))
    if not name or days < 0 or name == "__add__":
        return jsonify(error="Enter a name and the number of days (0 or more)."), 400
    t = db.execute("SELECT * FROM payment_terms WHERE lower(name) = lower(?)", (name,)).fetchone()
    if t:
        if not t["active"]:
            db.execute("UPDATE payment_terms SET active = 1 WHERE id = ?", (t["id"],))
            db.commit()
        return jsonify(name=t["name"], days=t["days"], existed=True)
    db.execute("INSERT INTO payment_terms(name, days, created_at) VALUES (?,?,?)", (name, days, now()))
    db.commit()
    log("PAYMENT TERM", f"Added payment term '{name}', {days} days (from a form)")
    return jsonify(name=name, days=days, existed=False)


@app.route("/setup/payment-terms", methods=["GET", "POST"])
@login_required
def payment_terms_page():
    db = get_db()
    if request.method == "POST":
        if g.user["role"] != "admin":
            flash("Admin access required.", "error")
            return redirect(url_for("payment_terms_page"))
        f = request.form
        act, tid = f.get("act"), f.get("id", type=int)
        t = db.execute("SELECT * FROM payment_terms WHERE id = ?", (tid,)).fetchone() if tid else None
        used = db.execute("SELECT COUNT(*) FROM documents WHERE payment_terms = ?", (t["name"],)).fetchone()[0] if t else 0
        if act == "save":
            name, days = f.get("name", "").strip(), int(to_float(f.get("days")))
            if not name or days < 0:
                flash("Enter a name and the number of days (0 or more).", "error")
                return redirect(url_for("payment_terms_page", edit=tid))
            if db.execute("SELECT 1 FROM payment_terms WHERE lower(name) = lower(?) AND id != ?", (name, tid or 0)).fetchone():
                flash(f"Payment term '{name}' already exists.", "error")
                return redirect(url_for("payment_terms_page", edit=tid))
            if t:
                db.execute("UPDATE payment_terms SET name = ?, days = ? WHERE id = ?", (name, days, tid))
                if name != t["name"] and get_settings().get("default_payment_terms") == t["name"]:
                    set_setting("default_payment_terms", name)
                log("PAYMENT TERM", f"Edited payment term '{t['name']}' -> '{name}', {days} days")
            else:
                db.execute("INSERT INTO payment_terms(name, days, created_at) VALUES (?,?,?)", (name, days, now()))
                log("PAYMENT TERM", f"Added payment term '{name}', {days} days")
            flash(f"Payment term '{name}' saved.", "ok")
        elif t and act == "toggle":
            db.execute("UPDATE payment_terms SET active = ? WHERE id = ?", (0 if t["active"] else 1, tid))
            log("PAYMENT TERM", f"{'Deactivated' if t['active'] else 'Activated'} payment term '{t['name']}'")
        elif t and act == "default":
            set_setting("default_payment_terms", t["name"])
            log("PAYMENT TERM", f"Default payment term set to '{t['name']}'")
            flash(f"'{t['name']}' is now the default for new sales orders.", "ok")
        elif t and act == "delete":
            if used:
                flash(f"'{t['name']}' is used on {used} document(s); deactivate it instead.", "error")
            else:
                db.execute("DELETE FROM payment_terms WHERE id = ?", (tid,))
                log("PAYMENT TERM", f"Deleted payment term '{t['name']}'")
                flash(f"'{t['name']}' deleted.", "ok")
        db.commit()
        return redirect(url_for("payment_terms_page"))
    used = {r[0]: r[1] for r in db.execute("SELECT payment_terms, COUNT(*) FROM documents GROUP BY payment_terms")}
    edit = db.execute("SELECT * FROM payment_terms WHERE id = ?", (request.args.get("edit", type=int),)).fetchone()
    return render_template("payment_terms.html", rows=pay_terms(), used=used, edit=edit)


@app.route("/inventory/warehouses", methods=["GET", "POST"])
@login_required
def warehouses_page():
    db = get_db()
    if request.method == "POST":
        if g.user["role"] != "admin":
            flash("Admin access required.", "error")
            return redirect(url_for("warehouses_page"))
        f = request.form
        act, wid = f.get("act"), f.get("id", type=int)
        w = warehouse_map().get(wid)
        if act == "save":
            code, name = f.get("code", "").strip().upper(), f.get("name", "").strip()
            if not code or not name:
                flash("Warehouse code and name are required.", "error")
                return redirect(url_for("warehouses_page", edit=wid))
            clash = db.execute("SELECT id FROM warehouses WHERE code = ? AND id != ?", (code, wid or 0)).fetchone()
            if clash:
                flash(f"Warehouse code {code} is already used.", "error")
                return redirect(url_for("warehouses_page", edit=wid))
            if w:
                db.execute("UPDATE warehouses SET code = ?, name = ?, location = ? WHERE id = ?",
                           (code, name, f.get("location", "").strip(), wid))
                log("WAREHOUSE EDIT", f"Edited warehouse {code} - {name}")
            else:
                db.execute("INSERT INTO warehouses(code, name, location, created_at) VALUES (?,?,?,?)",
                           (code, name, f.get("location", "").strip(), now()))
                log("WAREHOUSE ADD", f"Added warehouse {code} - {name}")
            flash(f"Warehouse {code} saved.", "ok")
        elif w and act == "default":
            if not w["active"]:
                flash("Activate the warehouse before making it the default.", "error")
            else:
                set_setting("default_warehouse", str(wid))
                log("WAREHOUSE DEFAULT", f"Default warehouse set to {w['code']}")
                flash(f"{w['code']} is now the default warehouse.", "ok")
        elif w and act == "toggle":
            if w["active"] and wid == default_warehouse_id():
                flash("The default warehouse can't be deactivated. Make another one the default first.", "error")
            else:
                db.execute("UPDATE warehouses SET active = ? WHERE id = ?", (0 if w["active"] else 1, wid))
                log("WAREHOUSE EDIT", f"{'Deactivated' if w['active'] else 'Activated'} warehouse {w['code']}")
                flash(f"{w['code']} {'deactivated' if w['active'] else 'activated'}.", "ok")
        elif w and act == "delete":
            if db.execute("SELECT 1 FROM documents WHERE warehouse_id = ? UNION SELECT 1 FROM stock_moves WHERE warehouse_id = ?",
                          (wid, wid)).fetchone() or wid == default_warehouse_id():
                flash(f"{w['code']} is used by documents or stock, or is the default; deactivate it instead.", "error")
            else:
                db.execute("DELETE FROM warehouses WHERE id = ?", (wid,))
                log("WAREHOUSE DELETE", f"Deleted warehouse {w['code']}")
                flash(f"{w['code']} deleted.", "ok")
        db.commit()
        return redirect(url_for("warehouses_page"))
    stats = {r[0]: r for r in db.execute("""SELECT t.wid, COALESCE(SUM(CASE WHEN t.q > 0 THEN t.q * p.avg_cost END), 0) AS value,
                                                SUM(t.q > 0) AS items, SUM(t.q < 0) AS negative
                                            FROM (SELECT warehouse_id AS wid, product_id, SUM(qty) AS q FROM stock_moves
                                                  GROUP BY warehouse_id, product_id) t
                                            JOIN products p ON p.id = t.product_id GROUP BY t.wid""")}
    docs = {r[0]: r[1] for r in db.execute("SELECT warehouse_id, COUNT(*) FROM documents GROUP BY warehouse_id")}
    edit = warehouse_map().get(request.args.get("edit", type=int))
    return render_template("warehouses.html", rows=list(warehouse_map().values()), stats=stats, docs=docs, edit=edit)


@app.route("/inventory/move/<int:mid>/delete", methods=["POST"])
@admin_required
def stock_move_delete(mid):
    db = get_db()
    m = db.execute("SELECT * FROM stock_moves WHERE id = ? AND kind = 'ADJ'", (mid,)).fetchone() or abort(404)
    db.execute("DELETE FROM stock_moves WHERE id = ?", (mid,))
    db.execute("DELETE FROM gl_lines WHERE rk = 'adj' AND rid = ?", (mid,))
    recompute_stock(m["product_id"], m["move_date"])
    db.commit()
    p = db.execute("SELECT * FROM products WHERE id = ?", (m["product_id"],)).fetchone()
    log("STOCK ADJUST", f"Removed adjustment of {num(m['qty'])} on {p['code']} -> stock {num(p['stock_qty'])}")
    flash("Adjustment removed.", "ok")
    return redirect(url_for("stock_ledger", pid=m["product_id"]))


# ---------------------------------------------------------------- stock entries (stock in / stock out)
# A voucher that moves several products into or out of one warehouse and posts its own journal against an
# account the user picks: Stock In = Dr Inventory / Cr account, Stock Out = Dr account / Cr Inventory.
# Stock in is valued at the cost entered (blank = current average), stock out at the average cost.
# A posted entry can't be edited; an admin cancels it, which removes its stock moves and journal lines.

SE_KINDS = {"in": "IN", "out": "OUT"}


def next_se_no():
    s = get_settings()
    n = int(s["se_next"] or 1)
    while True:
        no = f"{s['se_prefix']} {n:06d}"
        if not get_db().execute("SELECT 1 FROM stock_entries WHERE se_no = ?", (no,)).fetchone():
            return no, n
        n += 1


@app.route("/inventory/entries")
@login_required
def stock_entries():
    db = get_db()
    kind = SE_KINDS.get(request.args.get("kind", ""), "")
    q, page = request.args.get("q", "").strip(), page_no()
    rows = db.execute(f"""SELECT e.*, w.code AS wh_code, a.code AS acc_code, a.name AS acc_name, u.username,
                              (SELECT COUNT(*) FROM stock_entry_lines l WHERE l.entry_id = e.id) AS lines,
                              COALESCE((SELECT SUM(m.value) FROM stock_moves m WHERE m.entry_id = e.id), 0) AS value
                          FROM stock_entries e JOIN warehouses w ON w.id = e.warehouse_id JOIN coa a ON a.id = e.account_id
                          LEFT JOIN users u ON u.id = e.created_by
                          WHERE (:k = '' OR e.kind = :k) AND (e.se_no LIKE :q OR e.narration LIKE :q)
                          ORDER BY e.se_date DESC, e.id DESC LIMIT {PAGE + 1} OFFSET {(page - 1) * PAGE}""",
                      {"k": kind, "q": f"%{q}%"}).fetchall()
    return render_template("stock_entries.html", rows=rows[:PAGE], kind=kind, q=q, page=page, has_next=len(rows) > PAGE)


@app.route("/inventory/entry/new/<kind>", methods=["GET", "POST"])
@admin_required
def stock_entry_new(kind):
    kind = SE_KINDS.get(kind) or abort(404)
    db = get_db()
    accounts_ = db.execute("""SELECT * FROM coa WHERE is_group = 0 AND active = 1 AND COALESCE(system_key, '') != 'inventory'
                              ORDER BY code""").fetchall()
    if request.method == "POST":
        f = request.form
        narration, se_date = f.get("narration", "").strip(), f.get("se_date") or date.today().isoformat()
        wid, aid = wh_id(f.get("warehouse_id")), f.get("account_id", type=int)
        lines = []
        for pid, qty, cost, note in zip(f.getlist("product_id"), f.getlist("qty"), f.getlist("unit_cost"), f.getlist("line_note")):
            if not pid and not qty:
                continue
            p = db.execute("SELECT * FROM products WHERE id = ?", (pid,)).fetchone() if pid.isdigit() else None
            qty = to_float(qty)
            if not p or qty <= 0:
                flash("Each line needs a product from the list and a quantity above zero.", "error")
                return redirect(request.url)
            unit_cost = to_float(cost) if kind == "IN" and cost.strip() else None
            lines.append((p, qty, unit_cost, note.strip()))
        if not lines or not narration or aid not in {a["id"] for a in accounts_}:
            flash("Enter a narration, the account to post against and at least one product line.", "error")
            return redirect(request.url)
        no, n = next_se_no()
        eid = db.execute("""INSERT INTO stock_entries(se_no, se_date, kind, warehouse_id, account_id, narration, created_by, created_at)
                            VALUES (?,?,?,?,?,?,?,?)""", (no, se_date, kind, wid, aid, narration, g.user["id"], now())).lastrowid
        sign = 1 if kind == "IN" else -1
        for p, qty, unit_cost, note in lines:
            cost = (p["avg_cost"] if unit_cost is None else unit_cost) if kind == "IN" else 0  # out: average, set on replay
            mid = db.execute("""INSERT INTO stock_moves(product_id, entry_id, move_date, kind, ref, note, qty, unit_cost,
                                warehouse_id, created_by, created_at) VALUES (?,?,?,?,?,?,?,?,?,?,?)""",
                             (p["id"], eid, se_date, "S" + kind, no, note or narration, sign * qty, cost, wid,
                              g.user["id"], now())).lastrowid
            db.execute("INSERT INTO stock_entry_lines(entry_id, product_id, qty, unit_cost, note, move_id) VALUES (?,?,?,?,?,?)",
                       (eid, p["id"], qty, unit_cost, note, mid))
        for pid in {l[0]["id"] for l in lines}:
            recompute_stock(pid, se_date)
        gl_refresh("se", eid)
        set_setting("se_next", str(n + 1))
        db.commit()
        value = db.execute("SELECT COALESCE(SUM(value), 0) FROM stock_moves WHERE entry_id = ?", (eid,)).fetchone()[0]
        log(f"STOCK {kind}", f"{no} - {narration} - {len(lines)} line(s) in {warehouse_map()[wid]['code']}, "
                             f"value {get_settings()['currency']} {money(value)}")
        if kind == "OUT":
            short = db.execute("""SELECT p.code, p.name, SUM(m.qty) AS q FROM stock_moves m JOIN products p ON p.id = m.product_id
                                  WHERE m.warehouse_id = ? AND m.product_id IN (SELECT product_id FROM stock_entry_lines
                                  WHERE entry_id = ?) GROUP BY p.id HAVING SUM(m.qty) < 0""", (wid, eid)).fetchall()
            if short:
                flash("Stock is now negative for: " + ", ".join(f"{r['code']} {r['name']} ({num(r['q'])})" for r in short), "error")
        flash(f"Stock {'in' if kind == 'IN' else 'out'} {no} posted with its journal entry.", "ok")
        return redirect(url_for("stock_entry_view", eid=eid))
    default_acc = coa_keys().get("stock_adj")
    return render_template("stock_entry_form.html", kind=kind, accounts=accounts_, default_acc=default_acc,
                           today=date.today().isoformat(), preview_no=next_se_no()[0])


@app.route("/inventory/entry/<int:eid>")
@login_required
def stock_entry_view(eid):
    db = get_db()
    e = db.execute("""SELECT e.*, u.username, x.username AS cancelled_name, w.code AS wh_code, w.name AS wh_name,
                             a.code AS acc_code, a.name AS acc_name
                      FROM stock_entries e LEFT JOIN users u ON u.id = e.created_by LEFT JOIN users x ON x.id = e.cancelled_by
                      JOIN warehouses w ON w.id = e.warehouse_id JOIN coa a ON a.id = e.account_id
                      WHERE e.id = ?""", (eid,)).fetchone() or abort(404)
    lines = db.execute("""SELECT l.*, p.code, p.name, p.unit, COALESCE(m.unit_cost, l.unit_cost) AS cost,
                                 COALESCE(m.value, l.qty * l.unit_cost) AS value
                          FROM stock_entry_lines l JOIN products p ON p.id = l.product_id
                          LEFT JOIN stock_moves m ON m.id = l.move_id WHERE l.entry_id = ? ORDER BY l.id""", (eid,)).fetchall()
    gl = db.execute("""SELECT g.*, a.code, a.name FROM gl_lines g JOIN coa a ON a.id = g.account_id
                       WHERE g.rk = 'se' AND g.rid = ? ORDER BY g.id""", (eid,)).fetchall()
    return render_template("stock_entry_view.html", e=e, lines=lines, gl=gl)


@app.route("/inventory/entry/<int:eid>/cancel", methods=["POST"])
@admin_required
def stock_entry_cancel(eid):
    db = get_db()
    e = db.execute("SELECT * FROM stock_entries WHERE id = ?", (eid,)).fetchone() or abort(404)
    reason = request.form.get("reason", "").strip()
    if e["status"] != "Posted" or not reason:
        flash("Give a reason to cancel a posted stock entry.", "error")
        return redirect(url_for("stock_entry_view", eid=eid))
    # keep the cost each line moved at on the cancelled record, then take its stock moves out
    db.execute("""UPDATE stock_entry_lines SET unit_cost = (SELECT m.unit_cost FROM stock_moves m WHERE m.id = move_id)
                  WHERE entry_id = ? AND move_id IN (SELECT id FROM stock_moves)""", (eid,))
    pids = [r[0] for r in db.execute("SELECT DISTINCT product_id FROM stock_moves WHERE entry_id = ?", (eid,))]
    db.execute("DELETE FROM stock_moves WHERE entry_id = ?", (eid,))
    db.execute("UPDATE stock_entries SET status = 'Cancelled', cancel_reason = ?, cancelled_by = ?, cancelled_at = ? WHERE id = ?",
               (reason, g.user["id"], now(), eid))
    for pid in pids:
        recompute_stock(pid, e["se_date"])
    gl_refresh("se", eid)
    db.commit()
    log(f"STOCK {e['kind']}", f"Cancelled {e['se_no']}: {reason}")
    flash(f"{e['se_no']} cancelled; its stock and journal entry were reversed.", "ok")
    return redirect(url_for("stock_entry_view", eid=eid))


# ---------------------------------------------------------------- customer / supplier accounts

PAY_KINDS = {"receipt": "customer", "payment": "supplier"}       # voucher kind -> party kind
PARTY_PAY = {v: k for k, v in PAY_KINDS.items()}                   # party kind -> voucher kind
PAY_TITLES = {"receipt": "Receipt", "payment": "Payment"}
PAY_MODES = ["Cash", "Bank Transfer", "Cheque", "Card", "Online"]


def party_balances(kind, party_id=None):
    """Total balance of all customers (receivable) or suppliers (payable), or of one of them.

    Invoices raise it; Credit / Debit Notes and posted Receipts / Payments bring it down.
    """
    main, note = ("INV", "SR") if kind == "customer" else ("PI", "PR")
    where, params = "", []
    if party_id:
        where, params = " AND customer_id = ?", [party_id]
    db = get_db()
    docs = db.execute(f"""SELECT COALESCE(SUM(CASE WHEN doc_type = ? THEN base_total ELSE -base_total END), 0) FROM documents
                          WHERE status = 'Submitted' AND doc_type IN (?, ?){where}""", [main, main, note, *params]).fetchone()[0]
    paid = db.execute(f"""SELECT COALESCE(SUM(amount), 0) FROM payments WHERE kind = ? AND status = 'Posted'
                          {where.replace('customer_id', 'party_id')}""", [PARTY_PAY[kind], *params]).fetchone()[0]
    return r2(docs - paid)


def party_balance_map(kind, ids):
    """Balances of several customers / suppliers with two grouped queries."""
    if not ids:
        return {}
    main, note = ("INV", "SR") if kind == "customer" else ("PI", "PR")
    marks = ",".join("?" * len(ids))
    db = get_db()
    out = {r[0]: r[1] for r in db.execute(
        f"""SELECT customer_id, SUM(CASE WHEN doc_type = ? THEN base_total ELSE -base_total END) FROM documents
            WHERE status = 'Submitted' AND doc_type IN (?, ?) AND customer_id IN ({marks}) GROUP BY customer_id""",
        (main, main, note, *ids))}
    for pid, paid in db.execute(f"""SELECT party_id, SUM(amount) FROM payments WHERE kind = ? AND status = 'Posted'
                                    AND party_id IN ({marks}) GROUP BY party_id""", (PARTY_PAY[kind], *ids)):
        out[pid] = out.get(pid, 0) - paid
    return {k: r2(v) for k, v in out.items()}


def invoice_outstanding(inv_id):
    """(paid, outstanding) of one invoice: its total less its Credit / Debit Notes less allocated receipts / payments."""
    db = get_db()
    total = db.execute("SELECT base_total FROM documents WHERE id = ?", (inv_id,)).fetchone()[0]
    notes = db.execute("""SELECT COALESCE(SUM(base_total), 0) FROM documents WHERE parent_id = ? AND doc_type IN ('SR', 'PR')
                          AND status = 'Submitted'""", (inv_id,)).fetchone()[0]
    paid = db.execute("""SELECT COALESCE(SUM(a.amount), 0) FROM payment_allocations a JOIN payments p ON p.id = a.payment_id
                         WHERE a.document_id = ? AND p.status = 'Posted'""", (inv_id,)).fetchone()[0]
    return r2(paid), r2(total - notes - paid)


def open_invoices(kind, party_id):
    """Posted invoices of a customer / supplier that still have something to pay, oldest first."""
    inv_type = "INV" if kind == "customer" else "PI"
    rows = get_db().execute("""SELECT d.*,
            COALESCE((SELECT SUM(a.amount) FROM payment_allocations a JOIN payments p ON p.id = a.payment_id
                      WHERE a.document_id = d.id AND p.status = 'Posted'), 0) AS paid,
            COALESCE((SELECT SUM(n.base_total) FROM documents n WHERE n.parent_id = d.id AND n.doc_type IN ('SR', 'PR')
                      AND n.status = 'Submitted'), 0) AS noted
            FROM documents d WHERE d.doc_type = ? AND d.status = 'Submitted' AND d.customer_id = ?
            ORDER BY d.doc_date, d.id""", (inv_type, party_id)).fetchall()
    out = []
    for r in rows:
        outstanding = r2(r["base_total"] - r["noted"] - r["paid"])
        if outstanding > 0.004:  # amounts in base currency; doc_total / currency keep the invoice's own figure
            out.append(dict(r, total=r["base_total"], doc_total=r["total"], paid=r2(r["paid"]), outstanding=outstanding))
    return out


def next_voucher_no(kind):
    s = get_settings()
    key = "rv" if kind == "receipt" else "pv"
    n = int(s[f"{key}_next"] or 1)
    while True:
        no = f"{s[f'{key}_prefix']} {n:06d}"
        if not get_db().execute("SELECT 1 FROM payments WHERE voucher_no = ?", (no,)).fetchone():
            return no, n, key
        n += 1


AGING_BUCKETS = [("Not due", None, 0), ("1-30", 1, 30), ("31-60", 31, 60), ("61-90", 61, 90), ("91-120", 91, 120),
                 ("Over 120", 121, None)]


def aging(kind, as_of, basis="due", party_id=None):
    """Open invoices of customers (receivable) or suppliers (payable) as of a date, aged into buckets.

    Outstanding = invoice total less credit / debit notes and allocated receipts / payments dated up to as_of.
    Due date = invoice date + the days of its payment term (payment terms master; unknown terms count as 0 days).
    A purchase invoice is dated by the supplier's invoice date when it has one. Age is counted from the due date
    (basis "due") or the invoice date (basis "invoice"). Money received / paid but not allocated to an invoice is
    returned per party as "unapplied", so the net matches what the party owes.
    """
    inv_type = "INV" if kind == "customer" else "PI"
    db = get_db()
    terms = {r["name"].lower(): r["days"] for r in pay_terms()}
    rows = db.execute("""SELECT d.id, d.doc_no, d.customer_id, d.cust_name, d.payment_terms, d.base_total AS total,
            CASE WHEN d.doc_type = 'PI' AND COALESCE(d.supplier_inv_date, '') != '' THEN d.supplier_inv_date ELSE d.doc_date END AS inv_date,
            d.supplier_inv_no, c.account_no,
            COALESCE((SELECT SUM(a.amount) FROM payment_allocations a JOIN payments p ON p.id = a.payment_id
                      WHERE a.document_id = d.id AND p.status = 'Posted' AND p.pay_date <= :d), 0) AS paid,
            COALESCE((SELECT SUM(n.base_total) FROM documents n WHERE n.parent_id = d.id AND n.doc_type IN ('SR', 'PR')
                      AND n.status = 'Submitted' AND n.doc_date <= :d), 0) AS noted
            FROM documents d LEFT JOIN customers c ON c.id = d.customer_id
            WHERE d.doc_type = :t AND d.status = 'Submitted' AND d.doc_date <= :d AND (:p IS NULL OR d.customer_id = :p)
            ORDER BY d.cust_name, inv_date, d.id""", {"d": as_of, "t": inv_type, "p": party_id}).fetchall()
    as_of_d = date.fromisoformat(as_of)
    invoices = []
    for r in rows:
        outstanding = r2(r["total"] - r["noted"] - r["paid"])
        if outstanding <= 0.004:
            continue
        days = terms.get((r["payment_terms"] or "").strip().lower(), 0)
        inv_d = date.fromisoformat(r["inv_date"])
        due = inv_d + timedelta(days=days)
        age = (as_of_d - (due if basis == "due" else inv_d)).days
        bucket = next(i for i, (_, lo, hi) in enumerate(AGING_BUCKETS)
                      if (lo is None and age < 1) or (lo is not None and age >= lo and (hi is None or age <= hi)))
        invoices.append(dict(r, outstanding=outstanding, paid=r2(r["paid"] + r["noted"]), term_days=days,
                             due_date=due.isoformat(), age=age, overdue=(as_of_d - due).days, bucket=bucket))
    # receipts / payments not allocated to any invoice (advances), up to as_of
    unapplied = {r[0]: r2(r[1]) for r in db.execute(
        """SELECT p.party_id, SUM(p.amount - COALESCE((SELECT SUM(a.amount) FROM payment_allocations a WHERE a.payment_id = p.id), 0))
           FROM payments p WHERE p.kind = ? AND p.status = 'Posted' AND p.pay_date <= ? AND (? IS NULL OR p.party_id = ?)
           GROUP BY p.party_id""", (PARTY_PAY[kind], as_of, party_id, party_id)) if r2(r[1]) > 0.004}
    parties = {}
    for i in invoices:
        pt = parties.setdefault(i["customer_id"], dict(id=i["customer_id"], name=i["cust_name"], account_no=i["account_no"],
                                                       buckets=[0.0] * len(AGING_BUCKETS), total=0.0, invoices=[]))
        pt["buckets"][i["bucket"]] = r2(pt["buckets"][i["bucket"]] + i["outstanding"])
        pt["total"] = r2(pt["total"] + i["outstanding"])
        pt["invoices"].append(i)
    for pid, amt in unapplied.items():
        if pid not in parties:
            c = db.execute("SELECT name, account_no FROM customers WHERE id = ?", (pid,)).fetchone()
            parties[pid] = dict(id=pid, name=c["name"] if c else "?", account_no=c["account_no"] if c else "",
                                buckets=[0.0] * len(AGING_BUCKETS), total=0.0, invoices=[])
    out = sorted(parties.values(), key=lambda x: x["name"].lower())
    for pt in out:
        pt["unapplied"] = unapplied.get(pt["id"], 0.0)
        pt["net"] = r2(pt["total"] - pt["unapplied"])
        pt["overdue"] = r2(sum(pt["buckets"][1:]))
    return out


@app.route("/accounts/<kind>/aging")
@login_required
def aging_report(kind):
    if kind not in ("customer", "supplier"):
        abort(404)
    as_of = request.args.get("as_of") or date.today().isoformat()
    basis = "invoice" if request.args.get("basis") == "invoice" else "due"
    party_id = request.args.get("party", type=int)
    rows = aging(kind, as_of, basis, party_id)
    if request.args.get("export"):  # one line per open invoice, for Excel
        buf = io.StringIO()
        w = csv.writer(buf)
        w.writerow(["Account", "Name", "Invoice", "Supplier invoice" if kind == "supplier" else "", "Invoice date", "Payment terms",
                    "Due date", "Days overdue", "Bucket", "Invoice total", "Paid / credited", "Outstanding"])
        for pt in rows:
            for i in pt["invoices"]:
                w.writerow([pt["account_no"], pt["name"], i["doc_no"], i["supplier_inv_no"] or "", i["inv_date"], i["payment_terms"] or "",
                            i["due_date"], max(i["overdue"], 0), AGING_BUCKETS[i["bucket"]][0], i["total"], i["paid"], i["outstanding"]])
            if pt["unapplied"]:
                w.writerow([pt["account_no"], pt["name"], "Unapplied advance", "", "", "", "", "", "", "", "", -pt["unapplied"]])
        log("AGING EXPORT", f"Exported {'receivable' if kind == 'customer' else 'payable'} aging as of {as_of}")
        return Response(buf.getvalue(), mimetype="text/csv", headers={
            "Content-Disposition": f"attachment; filename={'receivable' if kind == 'customer' else 'payable'}-aging-{as_of}.csv"})
    totals = dict(buckets=[r2(sum(pt["buckets"][k] for pt in rows)) for k in range(len(AGING_BUCKETS))],
                  total=r2(sum(pt["total"] for pt in rows)), unapplied=r2(sum(pt["unapplied"] for pt in rows)),
                  net=r2(sum(pt["net"] for pt in rows)), overdue=r2(sum(pt["overdue"] for pt in rows)))
    parties = get_db().execute("SELECT id, name FROM customers WHERE kind = ? ORDER BY name", (kind,)).fetchall()
    return render_template("aging.html", kind=kind, rows=rows, totals=totals, buckets=[b[0] for b in AGING_BUCKETS],
                           as_of=as_of, basis=basis, party_id=party_id, parties=parties)


@app.route("/accounts/<kind>")
@login_required
def accounts(kind):
    if kind not in ACCOUNT_DOCS:
        abort(404)
    main, notes = ("INV", "SR") if kind == "customer" else ("PI", "PR")
    rows = get_db().execute("""SELECT c.*,
            COALESCE(SUM(CASE WHEN d.doc_type = ? THEN d.base_total END), 0) AS invoiced,
            COALESCE(SUM(CASE WHEN d.doc_type = ? THEN d.base_total END), 0) AS noted,
            (SELECT COALESCE(SUM(p.amount), 0) FROM payments p WHERE p.party_id = c.id AND p.status = 'Posted') AS paid,
            MAX(d.doc_date) AS last_date
            FROM customers c LEFT JOIN documents d ON d.customer_id = c.id AND d.status = 'Submitted' AND d.doc_type IN (?, ?)
            WHERE c.kind = ? GROUP BY c.id ORDER BY c.name""", (main, notes, main, notes, kind)).fetchall()
    rows = [dict(r, balance=r2(r["invoiced"] - r["noted"] - r["paid"])) for r in rows]
    return render_template("accounts.html", rows=rows, kind=kind, main=main, notes=notes,
                           total=r2(sum(r["balance"] for r in rows)), pay_kind=PARTY_PAY[kind])


@app.route("/accounts/<kind>/<int:cid>")
@login_required
def statement(kind, cid):
    if kind not in ACCOUNT_DOCS:
        abort(404)
    db = get_db()
    party = db.execute("SELECT * FROM customers WHERE id = ? AND kind = ?", (cid, kind)).fetchone() or abort(404)
    dr, cr = ACCOUNT_DOCS[kind]
    d_from, d_to = request.args.get("from", ""), request.args.get("to", "")
    # every posted entry of the account: invoices, notes and receipts / payments
    entries = []
    for d in db.execute("""SELECT * FROM documents WHERE customer_id = ? AND status = 'Submitted' AND doc_type IN (?, ?)""",
                        (cid, dr, cr)).fetchall():
        entries.append(dict(date=d["doc_date"], seq=d["created_at"] or "", kind=d["doc_type"], label=DOC_TYPES[d["doc_type"]],
                            no=d["doc_no"], url=url_for("doc_view", doc_id=d["id"]),
                            ref=", ".join(p["doc_no"] for p in sources_of(d))
                            + (f" · {d['notes']}" if d["notes"] else "") + (f" · Ref {d['lpo_no']}" if d["lpo_no"] else "")
                            + (f" · {d['currency']} {money(d['total'])} @ {d['exchange_rate']:g}"
                               if d["currency"] and d["currency"] != base_currency() else ""),
                            debit=d["base_total"] if d["doc_type"] == dr else 0,
                            credit=d["base_total"] if d["doc_type"] == cr else 0))
    for p in db.execute("SELECT * FROM payments WHERE party_id = ? AND status = 'Posted'", (cid,)).fetchall():
        entries.append(dict(date=p["pay_date"], seq=p["created_at"], kind=p["kind"], label=PAY_TITLES[p["kind"]],
                            no=p["voucher_no"], url=url_for("voucher", vid=p["id"]),
                            ref=" · ".join(x for x in (p["mode"], p["reference"], p["notes"]) if x),
                            debit=p["amount"] if kind == "supplier" else 0, credit=p["amount"] if kind == "customer" else 0))
    entries.sort(key=lambda e: (e["date"], e["seq"]))
    sign = 1 if kind == "customer" else -1  # customers: debit balance (they owe us); suppliers: credit balance (we owe)
    opening, lines = 0.0, []
    for e in entries:
        if d_from and e["date"] < d_from:
            opening += sign * (e["debit"] - e["credit"])
            continue
        if d_to and e["date"] > d_to:
            continue
        prev = lines[-1]["balance"] if lines else opening
        lines.append(dict(e, balance=prev + sign * (e["debit"] - e["credit"])))
    closing = lines[-1]["balance"] if lines else opening
    return render_template("statement.html", party=party, kind=kind, lines=lines, opening=opening, closing=closing,
                           d_from=d_from, d_to=d_to, pay_kind=PARTY_PAY[kind])


# ---------------------------------------------------------------- receipts / payments

@app.route("/payments/<kind>")
@login_required
def payments(kind):
    if kind not in PAY_KINDS:
        abort(404)
    q = request.args.get("q", "").strip()
    rows = get_db().execute(f"""SELECT p.*, c.name AS party, u.username,
            (SELECT COALESCE(SUM(a.amount), 0) FROM payment_allocations a WHERE a.payment_id = p.id) AS allocated
            FROM payments p JOIN customers c ON c.id = p.party_id LEFT JOIN users u ON u.id = p.created_by
            WHERE p.kind = ? AND (p.voucher_no LIKE ? OR c.name LIKE ? OR p.reference LIKE ?)
            ORDER BY p.pay_date DESC, p.id DESC LIMIT {PAGE + 1} OFFSET {(page_no() - 1) * PAGE}""",
                            (kind, *[f"%{q}%"] * 3)).fetchall()
    total = get_db().execute("""SELECT COALESCE(SUM(p.amount), 0) FROM payments p JOIN customers c ON c.id = p.party_id
            WHERE p.kind = ? AND p.status = 'Posted' AND (p.voucher_no LIKE ? OR c.name LIKE ? OR p.reference LIKE ?)""",
                             (kind, *[f"%{q}%"] * 3)).fetchone()[0]
    return render_template("payments.html", rows=rows[:PAGE], kind=kind, q=q, total=total, page=page_no(),
                           has_next=len(rows) > PAGE)


@app.route("/payments/<kind>/new", methods=["GET", "POST"])
@login_required
def payment_new(kind):
    if kind not in PAY_KINDS:
        abort(404)
    party_kind_ = PAY_KINDS[kind]
    db = get_db()
    party = None
    pid = request.values.get("party", type=int)
    if pid:
        party = db.execute("SELECT * FROM customers WHERE id = ? AND kind = ?", (pid, party_kind_)).fetchone()

    if request.method == "POST":
        f = request.form
        amount = r2(to_float(f.get("amount")))
        if not party or amount <= 0:
            flash(f"Choose the {party_kind_} and enter an amount above zero.", "error")
            return redirect(request.url)
        open_inv = {r["id"]: r for r in open_invoices(party_kind_, party["id"])}
        allocs = []
        for inv_id, val in zip(f.getlist("alloc_id"), f.getlist("alloc_amount")):
            val = r2(to_float(val))
            if val <= 0:
                continue
            inv = open_inv.get(int(inv_id))
            if not inv or val > inv["outstanding"] + 0.004:
                flash(f"Allocation to {inv['doc_no'] if inv else 'an invoice'} is more than its outstanding amount.", "error")
                return redirect(request.url)
            allocs.append((inv["id"], inv["doc_no"], val))
        if sum(a[2] for a in allocs) > amount + 0.004:
            flash("The allocations add up to more than the amount.", "error")
            return redirect(request.url)
        no, n, key = next_voucher_no(kind)
        vid = db.execute("""INSERT INTO payments(kind, voucher_no, party_id, pay_date, amount, mode, reference, bank,
                            cheque_date, notes, created_by, created_at) VALUES (?,?,?,?,?,?,?,?,?,?,?,?)""",
                         (kind, no, party["id"], f.get("pay_date") or date.today().isoformat(), amount,
                          f.get("mode", "Cash"), f.get("reference", "").strip(), f.get("bank", "").strip(),
                          f.get("cheque_date", ""), f.get("notes", "").strip(), g.user["id"], now())).lastrowid
        db.executemany("INSERT INTO payment_allocations(payment_id, document_id, amount) VALUES (?,?,?)",
                       [(vid, a[0], a[2]) for a in allocs])
        gl_refresh("pay", vid)
        set_setting(f"{key}_next", str(n + 1))
        db.commit()
        on_account = r2(amount - sum(a[2] for a in allocs))
        log(f"{kind.upper()} CREATE", f"{PAY_TITLES[kind]} {no} - {party['name']} - {get_settings()['currency']} {money(amount)}"
            f" by {f.get('mode', 'Cash')}"
            + (f" against {', '.join(f'{a[1]} ({money(a[2])})' for a in allocs)}" if allocs else "")
            + (f", {money(on_account)} on account" if on_account else ""))
        flash(f"{PAY_TITLES[kind]} {no} posted.", "ok")
        return redirect(url_for("voucher", vid=vid))

    parties = db.execute("SELECT id, name FROM customers WHERE kind = ? ORDER BY name", (party_kind_,)).fetchall()
    invoices = open_invoices(party_kind_, party["id"]) if party else []
    return render_template("payment_form.html", kind=kind, party=party, parties=parties, invoices=invoices,
                           modes=PAY_MODES, today=date.today().isoformat(), preview_no=next_voucher_no(kind)[0],
                           balance=party_balances(party_kind_, party["id"]) if party else 0,
                           preselect=request.args.get("invoice", type=int))


@app.route("/payments/voucher/<int:vid>")
@login_required
def voucher(vid):
    db = get_db()
    p = db.execute("""SELECT p.*, c.name AS party, c.area, c.po_box, c.contact, c.trn, u.username, x.username AS cancelled_name
                      FROM payments p JOIN customers c ON c.id = p.party_id LEFT JOIN users u ON u.id = p.created_by
                      LEFT JOIN users x ON x.id = p.cancelled_by WHERE p.id = ?""", (vid,)).fetchone() or abort(404)
    allocs = db.execute("""SELECT a.amount, d.id, d.doc_no, d.doc_date, d.base_total AS total FROM payment_allocations a
                           JOIN documents d ON d.id = a.document_id WHERE a.payment_id = ? ORDER BY d.doc_date""", (vid,)).fetchall()
    on_account = r2(p["amount"] - sum(a["amount"] for a in allocs))
    log(f"{p['kind'].upper()} PRINT", f"Viewed/printed {PAY_TITLES[p['kind']]} {p['voucher_no']}")
    return render_template("voucher.html", p=p, allocs=allocs, on_account=on_account,
                           words=amount_in_words(p["amount"], get_settings()["currency"]))


@app.route("/payments/voucher/<int:vid>/cancel", methods=["POST"])
@admin_required
def voucher_cancel(vid):
    db = get_db()
    p = db.execute("SELECT * FROM payments WHERE id = ?", (vid,)).fetchone() or abort(404)
    reason = request.form.get("reason", "").strip()
    if p["status"] != "Posted" or not reason:
        flash("Give a reason to cancel a posted voucher.", "error")
        return redirect(url_for("voucher", vid=vid))
    db.execute("UPDATE payments SET status = 'Cancelled', cancel_reason = ?, cancelled_by = ?, cancelled_at = ? WHERE id = ?",
               (reason, g.user["id"], now(), vid))
    gl_refresh("pay", vid)
    db.commit()
    log(f"{p['kind'].upper()} CANCEL", f"Cancelled {PAY_TITLES[p['kind']]} {p['voucher_no']} ({money(p['amount'])}): {reason}")
    flash(f"{p['voucher_no']} cancelled; it no longer counts in the account.", "ok")
    return redirect(url_for("voucher", vid=vid))


# ---------------------------------------------------------------- general ledger
#
# Double entry. Every posted document, stock adjustment and receipt / payment produces its journal entry
# automatically (built from the live data, so it always matches current stock costs); manual Journal
# Vouchers cover everything else. Trial Balance and ledgers are read from the same journal.

ACCOUNT_TYPES = ["Asset", "Liability", "Equity", "Income", "Expense"]
DEBIT_NATURE = {"Asset", "Expense"}  # normal balance side: debit for these, credit for the others

DEFAULT_COA = [  # code, name, type, parent code, is group, system key (used by automatic posting)
    ("1000", "Assets", "Asset", None, 1, None),
    ("1100", "Cash in Hand", "Asset", "1000", 0, "cash"),
    ("1110", "Bank Account", "Asset", "1000", 0, "bank"),
    ("1200", "Accounts Receivable (Customers)", "Asset", "1000", 0, "ar"),
    ("1300", "Inventory", "Asset", "1000", 0, "inventory"),
    ("1400", "VAT Input (Recoverable)", "Asset", "1000", 0, "vat_in"),
    ("2000", "Liabilities", "Liability", None, 1, None),
    ("2100", "Accounts Payable (Suppliers)", "Liability", "2000", 0, "ap"),
    ("2200", "VAT Output (Payable)", "Liability", "2000", 0, "vat_out"),
    ("2300", "Goods Received Not Invoiced", "Liability", "2000", 0, "grni"),
    ("3000", "Equity", "Equity", None, 1, None),
    ("3100", "Owner's Capital", "Equity", "3000", 0, "capital"),
    ("3200", "Retained Earnings", "Equity", "3000", 0, "retained"),
    ("3300", "Opening Balance Equity", "Equity", "3000", 0, "opening"),
    ("4000", "Income", "Income", None, 1, None),
    ("4100", "Sales", "Income", "4000", 0, "sales"),
    ("4200", "Sales Returns", "Income", "4000", 0, "sales_returns"),
    ("4900", "Other Income", "Income", "4000", 0, None),
    ("5000", "Expenses", "Expense", None, 1, None),
    ("5100", "Cost of Goods Sold", "Expense", "5000", 0, "cogs"),
    ("5200", "Inventory Adjustments", "Expense", "5000", 0, "stock_adj"),
    ("5300", "Purchase Price Variance", "Expense", "5000", 0, "ppv"),
    ("5400", "Bank Charges", "Expense", "5000", 0, None),
    ("5900", "General Expenses", "Expense", "5000", 0, None),
]


def seed_coa(db):
    if db.execute("SELECT 1 FROM coa LIMIT 1").fetchone():
        return
    ids = {}
    for code, name, typ, parent, is_group, key in DEFAULT_COA:
        ids[code] = db.execute("""INSERT INTO coa(code, name, type, parent_id, is_group, system_key, created_at)
                                  VALUES (?,?,?,?,?,?,?)""", (code, name, typ, ids.get(parent), is_group, key, now())).lastrowid


def coa_keys():
    return {r["system_key"]: r["id"] for r in get_db().execute("SELECT id, system_key FROM coa WHERE system_key IS NOT NULL")}


# The general ledger is materialised in gl_lines: every posting writes its own lines, so reports read an
# indexed table instead of rebuilding all entries. One set of rules below is the single source of truth;
# gl_refresh() rewrites the lines of one document / adjustment / voucher / journal, gl_rebuild() all of them.
GL_VERSION = "1"

# document type -> (system account, Debit / Credit side, amount, carries the party)
GL_DOC_RULES = [
    ("INV", "ar", "D", "total", 1), ("INV", "sales", "C", "taxable", 0), ("INV", "vat_out", "C", "vat", 0),
    ("SR", "sales_returns", "D", "taxable", 0), ("SR", "vat_out", "D", "vat", 0), ("SR", "ar", "C", "total", 1),
    ("SR", "inventory", "D", "vin", 0), ("SR", "cogs", "C", "vin", 0),
    ("PI", "grni", "D", "taxable", 0), ("PI", "vat_in", "D", "vat", 0), ("PI", "ap", "C", "total", 1),
    ("PR", "ap", "D", "total", 1), ("PR", "inventory", "C", "vout", 0), ("PR", "vat_in", "C", "vat", 0),
    ("PR", "ppv", "D", "ppv_dr", 0), ("PR", "ppv", "C", "ppv_cr", 0),      # returned value vs its stock value
    ("GRN", "inventory", "D", "vin", 0), ("GRN", "grni", "C", "vin", 0),
    ("DN", "cogs", "D", "vout", 0), ("DN", "inventory", "C", "vout", 0),
]
_rules = " UNION ALL ".join(f"SELECT {i} AS ord, '{t}' AS t, '{k}' AS k, '{s}' AS side, '{a}' AS amt, {p} AS party"
                            for i, (t, k, s, a, p) in enumerate(GL_DOC_RULES))
_doc_names = " ".join(f"WHEN '{k}' THEN '{v}'" for k, v in DOC_TYPES.items())

GL_SQL = {
    "doc": f"""
        WITH r AS ({_rules}),
        d AS (SELECT d.id, d.doc_type, d.doc_no, d.doc_date, d.created_at, d.customer_id,
                     d.base_total AS total, d.base_vat AS vat_amount, ROUND(d.base_total - d.base_vat, 2) AS taxable,
                     COALESCE((SELECT SUM(value) FROM stock_moves m WHERE m.document_id = d.id AND m.qty > 0), 0) AS vin,
                     COALESCE((SELECT SUM(value) FROM stock_moves m WHERE m.document_id = d.id AND m.qty < 0), 0) AS vout,
                     (CASE d.doc_type {_doc_names} END) || ' ' || d.doc_no || ' - ' || d.cust_name AS narr
              FROM documents d WHERE d.status = 'Submitted' AND d.doc_type IN ('INV', 'SR', 'PI', 'PR', 'GRN', 'DN') AND ({{w}})),
        x AS (SELECT d.*, r.ord, r.side, r.party, a.id AS account_id,
                     CASE r.amt WHEN 'total' THEN d.total WHEN 'taxable' THEN d.taxable WHEN 'vat' THEN d.vat_amount
                          WHEN 'vin' THEN d.vin WHEN 'vout' THEN d.vout
                          WHEN 'ppv_dr' THEN MAX(d.vout - d.taxable, 0) ELSE MAX(d.taxable - d.vout, 0) END AS amount
              FROM d JOIN r ON r.t = d.doc_type JOIN coa a ON a.system_key = r.k)
        SELECT doc_date, created_at, doc_type, 'doc', id, doc_no, narr, account_id,
               CASE side WHEN 'D' THEN ROUND(amount, 2) ELSE 0 END, CASE side WHEN 'C' THEN ROUND(amount, 2) ELSE 0 END,
               CASE WHEN party = 1 THEN customer_id END, NULL
        FROM x WHERE ROUND(amount, 2) != 0 ORDER BY id, ord""",
    "adj": """
        SELECT m.move_date, m.created_at, 'ADJ', 'adj', m.id, 'ADJ-' || m.id,
               'Stock adjustment ' || p.code || ' ' || p.name || ' ' || printf('%g', m.qty)
                   || CASE WHEN COALESCE(m.note, '') != '' THEN ' (' || m.note || ')' ELSE '' END,
               a.id, CASE WHEN s.side = 'D' THEN ROUND(m.value, 2) ELSE 0 END, CASE WHEN s.side = 'C' THEN ROUND(m.value, 2) ELSE 0 END,
               NULL, m.product_id
        FROM stock_moves m JOIN products p ON p.id = m.product_id
        JOIN (SELECT 1 AS dir, 'D' AS side, 'inventory' AS k UNION ALL SELECT 1, 'C', 'other'
              UNION ALL SELECT -1, 'D', 'stock_adj' UNION ALL SELECT -1, 'C', 'inventory') s
             ON s.dir = CASE WHEN m.qty > 0 THEN 1 ELSE -1 END
        JOIN coa a ON a.system_key = CASE WHEN s.k != 'other' THEN s.k
                                          WHEN lower(COALESCE(m.note, '')) LIKE '%opening%' THEN 'opening' ELSE 'stock_adj' END
        WHERE m.kind = 'ADJ' AND ROUND(m.value, 2) != 0 AND ({w}) ORDER BY m.id, s.side DESC""",
    "pay": """
        SELECT p.pay_date, p.created_at, upper(p.kind), 'pay', p.id, p.voucher_no,
               CASE p.kind WHEN 'receipt' THEN 'Receipt ' ELSE 'Payment ' END || p.voucher_no || ' - ' || c.name
                   || CASE WHEN COALESCE(p.reference, '') != '' THEN ' (' || p.reference || ')' ELSE '' END,
               a.id, CASE WHEN s.side = 'D' THEN p.amount ELSE 0 END, CASE WHEN s.side = 'C' THEN p.amount ELSE 0 END,
               CASE WHEN s.k IN ('ar', 'ap') THEN p.party_id END, NULL
        FROM payments p JOIN customers c ON c.id = p.party_id
        JOIN (SELECT 'receipt' AS kind, 'D' AS side, 'money' AS k UNION ALL SELECT 'receipt', 'C', 'ar'
              UNION ALL SELECT 'payment', 'D', 'ap' UNION ALL SELECT 'payment', 'C', 'money') s ON s.kind = p.kind
        JOIN coa a ON a.system_key = CASE WHEN s.k != 'money' THEN s.k WHEN p.mode = 'Cash' THEN 'cash' ELSE 'bank' END
        WHERE p.status = 'Posted' AND ({w}) ORDER BY p.id, s.side DESC""",
    "jv": """
        SELECT j.jv_date, j.created_at, 'JV', 'jv', j.id, j.jv_no, j.narration, l.account_id, l.debit, l.credit, l.party_id, NULL
        FROM journals j JOIN journal_lines l ON l.journal_id = j.id
        WHERE j.status = 'Posted' AND ({w}) ORDER BY j.id, l.id""",
    # stock in: Dr Inventory / Cr chosen account; stock out: Dr chosen account / Cr Inventory, at the moves' value
    "se": """
        SELECT e.se_date, e.created_at, 'S' || e.kind, 'se', e.id, e.se_no,
               CASE e.kind WHEN 'IN' THEN 'Stock in ' ELSE 'Stock out ' END || e.se_no || ' - ' || e.narration,
               CASE s.k WHEN 'inventory' THEN inv.id ELSE e.account_id END,
               CASE WHEN s.side = 'D' THEN e.v ELSE 0 END, CASE WHEN s.side = 'C' THEN e.v ELSE 0 END, NULL, NULL
        FROM (SELECT x.*, ROUND(COALESCE((SELECT SUM(m.value) FROM stock_moves m WHERE m.entry_id = x.id), 0), 2) AS v
              FROM stock_entries x) e
        JOIN (SELECT 'IN' AS kind, 'D' AS side, 'inventory' AS k UNION ALL SELECT 'IN', 'C', 'other'
              UNION ALL SELECT 'OUT', 'D', 'other' UNION ALL SELECT 'OUT', 'C', 'inventory') s ON s.kind = e.kind
        JOIN coa inv ON inv.system_key = 'inventory'
        WHERE e.status = 'Posted' AND e.v != 0 AND ({w}) ORDER BY e.id, s.side DESC""",
}
GL_ALIAS = {"doc": "d", "adj": "m", "pay": "p", "jv": "j", "se": "e"}
GL_INSERT = """INSERT INTO gl_lines(dt, seq, src, rk, rid, no, narration, account_id, debit, credit, party_id, link_id) """


def gl_refresh(rk, rid, db=None):
    """Rewrite the ledger lines of one posting (no lines if it is not posted / was cancelled / deleted)."""
    db = db or get_db()
    db.execute("DELETE FROM gl_lines WHERE rk = ? AND rid = ?", (rk, rid))
    db.execute(GL_INSERT + GL_SQL[rk].format(w=f"{GL_ALIAS[rk]}.id = ?"), (rid,))


def gl_rebuild(db=None):
    db = db or get_db()
    db.execute("DELETE FROM gl_lines")
    for rk in GL_SQL:
        db.execute(GL_INSERT + GL_SQL[rk].format(w="1 = 1"))


def gl_url(row):
    rk, rid = row["rk"], row["rid"]
    if rk == "doc":
        return url_for("doc_view", doc_id=rid)
    if rk == "pay":
        return url_for("voucher", vid=rid)
    if rk == "jv":
        return url_for("jv_view", jid=rid)
    if rk == "se":
        return url_for("stock_entry_view", eid=rid)
    return url_for("stock_ledger", pid=row["link_id"])


def account_totals(d_from="", d_to=""):
    """account id -> [opening (debit +), period debit, period credit]"""
    rows = get_db().execute("""SELECT account_id,
            SUM(CASE WHEN :f != '' AND dt < :f THEN debit - credit ELSE 0 END) AS opening,
            SUM(CASE WHEN :f = '' OR dt >= :f THEN debit ELSE 0 END) AS dr,
            SUM(CASE WHEN :f = '' OR dt >= :f THEN credit ELSE 0 END) AS cr
            FROM gl_lines WHERE :t = '' OR dt <= :t GROUP BY account_id""", {"f": d_from or "", "t": d_to or ""})
    return {r["account_id"]: [r["opening"] or 0, r["dr"] or 0, r["cr"] or 0] for r in rows}


PAGE = 100


def page_no():
    return max(1, request.args.get("page", 1, type=int))


@app.template_filter("drcr")
def drcr(v):
    v = r2(v or 0)
    return "0.00" if not v else f"{money(abs(v))} {'Dr' if v > 0 else 'Cr'}"


def coa_rows():
    """Chart of accounts in tree order (groups followed by their accounts)."""
    rows = [dict(r) for r in get_db().execute("SELECT * FROM coa ORDER BY code")]
    by_parent = {}
    for r in rows:
        by_parent.setdefault(r["parent_id"], []).append(r)
    out = []

    def walk(pid, depth):
        for r in by_parent.get(pid, []):
            out.append(dict(r, depth=depth))
            walk(r["id"], depth + 1)
    walk(None, 0)
    return out


@app.route("/ledger/accounts", methods=["GET", "POST"])
@login_required
def coa():
    db = get_db()
    edit = None
    if request.args.get("edit"):
        edit = db.execute("SELECT * FROM coa WHERE id = ?", (request.args["edit"],)).fetchone()
    if request.method == "POST":
        if g.user["role"] != "admin":
            abort(403)
        f = request.form
        code, name = f.get("code", "").strip(), f.get("name", "").strip()
        parent = db.execute("SELECT * FROM coa WHERE id = ? AND is_group = 1", (f.get("parent_id") or 0,)).fetchone()
        typ = parent["type"] if parent else f.get("type")
        dup = db.execute("SELECT 1 FROM coa WHERE code = ? AND id != ?", (code, f.get("id") or 0)).fetchone()
        if not code or not name or typ not in ACCOUNT_TYPES:
            flash("Code, name and type are required.", "error")
        elif dup:
            flash(f"Account code {code} is already used.", "error")
        elif f.get("id"):
            row = db.execute("SELECT * FROM coa WHERE id = ?", (f["id"],)).fetchone() or abort(404)
            # system accounts keep their type and place; only code / name / active can change
            if row["system_key"]:
                db.execute("UPDATE coa SET code = ?, name = ?, active = ? WHERE id = ?",
                           (code, name, 1 if f.get("active") else 0, row["id"]))
            else:
                db.execute("UPDATE coa SET code = ?, name = ?, type = ?, parent_id = ?, active = ? WHERE id = ?",
                           (code, name, typ, parent["id"] if parent else None, 1 if f.get("active") else 0, row["id"]))
            db.commit()
            log("COA EDIT", f"Edited account {code} {name}")
            flash(f"Account {code} updated.", "ok")
        else:
            db.execute("""INSERT INTO coa(code, name, type, parent_id, is_group, active, created_at) VALUES (?,?,?,?,?,?,?)""",
                       (code, name, typ, parent["id"] if parent else None, 1 if f.get("is_group") else 0, 1, now()))
            db.commit()
            log("COA ADD", f"Added {'group' if f.get('is_group') else 'account'} {code} {name} ({typ})")
            flash(f"Account {code} {name} added.", "ok")
        return redirect(url_for("coa"))
    tot = account_totals()
    rows = coa_rows()
    # balances roll up into their groups
    parent_of = {r["id"]: r["parent_id"] for r in rows}
    bal = {r["id"]: 0.0 if r["is_group"] else sum(tot.get(r["id"], [0, 0, 0])[i] * (1 if i < 2 else -1) for i in range(3))
           for r in rows}
    for r in rows:  # each account's balance also counts in all of its groups
        pid, v = r["parent_id"], (0 if r["is_group"] else bal[r["id"]])
        while pid and v:
            bal[pid] += v
            pid = parent_of[pid]
    groups = [r for r in rows if r["is_group"]]
    return render_template("coa.html", rows=rows, bal=bal, edit=edit, groups=groups, types=ACCOUNT_TYPES)


@app.route("/ledger/account/<int:aid>")
@login_required
def account_ledger(aid):
    db = get_db()
    a = db.execute("SELECT * FROM coa WHERE id = ?", (aid,)).fetchone() or abort(404)
    d_from, d_to = request.args.get("from", ""), request.args.get("to", "")
    prm = {"a": aid, "f": d_from, "t": d_to}
    period = "account_id = :a AND (:f = '' OR dt >= :f) AND (:t = '' OR dt <= :t)"
    opening = db.execute("SELECT COALESCE(SUM(debit - credit), 0) FROM gl_lines WHERE account_id = :a AND :f != '' AND dt < :f",
                         prm).fetchone()[0]
    tot = db.execute(f"SELECT COUNT(*), COALESCE(SUM(debit), 0), COALESCE(SUM(credit), 0) FROM gl_lines WHERE {period}", prm).fetchone()
    page = page_no()
    rows = db.execute(f"""SELECT * FROM (SELECT *, SUM(debit - credit) OVER (ORDER BY dt, seq, id) AS run FROM gl_lines WHERE {period})
                          ORDER BY dt, seq, id LIMIT {PAGE} OFFSET {(page - 1) * PAGE}""", prm).fetchall()
    lines = [dict(r, date=r["dt"], type=r["src"], url=gl_url(r), balance=opening + r["run"]) for r in rows]
    return render_template("account_ledger.html", a=a, lines=lines, opening=opening, closing=opening + tot[1] - tot[2],
                           total_dr=tot[1], total_cr=tot[2], d_from=d_from, d_to=d_to,
                           page=page, has_next=page * PAGE < tot[0], count=tot[0])


@app.route("/ledger/journal")
@login_required
def journal():
    db = get_db()
    d_from, d_to = request.args.get("from", ""), request.args.get("to", "")
    typ, q = request.args.get("type", ""), request.args.get("q", "").strip()
    prm = {"f": d_from, "t": d_to, "ty": typ, "q": f"%{q}%"}
    where = """(:f = '' OR dt >= :f) AND (:t = '' OR dt <= :t) AND (:ty = '' OR src = :ty)
               AND (:q = '%%' OR no LIKE :q OR narration LIKE :q)"""
    names = {r["id"]: f"{r['code']} {r['name']}" for r in db.execute("SELECT id, code, name FROM coa")}
    count, total = db.execute(f"""SELECT COUNT(DISTINCT rk || rid), COALESCE(SUM(debit), 0) FROM gl_lines WHERE {where}""", prm).fetchone()
    page = page_no()
    heads = db.execute(f"""SELECT rk, rid, MIN(dt) AS dt, MIN(seq) AS seq, src, no, narration, link_id FROM gl_lines WHERE {where}
                           GROUP BY rk, rid ORDER BY dt DESC, seq DESC, rid DESC LIMIT {PAGE} OFFSET {(page - 1) * PAGE}""",
                        prm).fetchall()
    entries = []
    for h in heads:  # newest first, one block per posting
        lines = db.execute("SELECT account_id, debit, credit, party_id FROM gl_lines WHERE rk = ? AND rid = ? ORDER BY id",
                           (h["rk"], h["rid"])).fetchall()
        entries.append(dict(date=h["dt"], type=h["src"], no=h["no"], narration=h["narration"], url=gl_url(h),
                            lines=[tuple(l) for l in lines]))
    return render_template("journal.html", entries=entries, names=names, total=total, d_from=d_from, d_to=d_to,
                           typ=typ, q=q, count=count, page=page, has_next=page * PAGE < count)


@app.route("/ledger/trial-balance")
@login_required
def trial_balance():
    d_from, d_to = request.args.get("from", ""), request.args.get("to", "")
    show_all = bool(request.args.get("all"))
    tot = account_totals(d_from, d_to)
    rows = []
    for r in coa_rows():
        t = tot.get(r["id"], [0.0, 0.0, 0.0])
        closing = r2(t[0] + t[1] - t[2])
        if r["is_group"] or show_all or any(abs(x) > 0.004 for x in t):
            rows.append(dict(r, opening=r2(t[0]), debit=r2(t[1]), credit=r2(t[2]), closing=closing))
    leaf = [r for r in rows if not r["is_group"]]
    sums = dict(op_dr=sum(r["opening"] for r in leaf if r["opening"] > 0), op_cr=-sum(r["opening"] for r in leaf if r["opening"] < 0),
                debit=sum(r["debit"] for r in leaf), credit=sum(r["credit"] for r in leaf),
                cl_dr=sum(r["closing"] for r in leaf if r["closing"] > 0), cl_cr=-sum(r["closing"] for r in leaf if r["closing"] < 0))
    sums = {k: r2(v) for k, v in sums.items()}
    # hide empty groups
    parent_of = {x["id"]: x["parent_id"] for x in rows}
    used_parents = set()
    for r in leaf:
        pid = r["parent_id"]
        while pid and pid not in used_parents:
            used_parents.add(pid)
            pid = parent_of.get(pid)
    rows = [r for r in rows if not r["is_group"] or r["id"] in used_parents or show_all]
    return render_template("trial_balance.html", rows=rows, sums=sums, d_from=d_from, d_to=d_to, show_all=show_all,
                           balanced=abs(sums["cl_dr"] - sums["cl_cr"]) < 0.01 and abs(sums["debit"] - sums["credit"]) < 0.01)


COST_OF_SALES = {"cogs", "stock_adj", "ppv"}  # expense accounts that sit above Gross Profit


def profit_and_loss(d_from, d_to):
    """Sections of the P&L for a period. Income shown as credit - debit, expenses as debit - credit."""
    tot = {r["account_id"]: (r["dr"], r["cr"]) for r in get_db().execute(
        """SELECT account_id, SUM(debit) AS dr, SUM(credit) AS cr FROM gl_lines
           WHERE (:f = '' OR dt >= :f) AND (:t = '' OR dt <= :t) GROUP BY account_id""", {"f": d_from or "", "t": d_to or ""})}
    sections = {"revenue": [], "cost": [], "other_income": [], "expenses": []}
    for a in get_db().execute("SELECT * FROM coa WHERE is_group = 0 AND type IN ('Income', 'Expense') ORDER BY code"):
        dr, cr = tot.get(a["id"], (0.0, 0.0))
        if a["type"] == "Income":
            amount = r2(cr - dr)
            key = "revenue" if a["system_key"] in ("sales", "sales_returns") else "other_income"
        else:
            amount = r2(dr - cr)
            key = "cost" if a["system_key"] in COST_OF_SALES else "expenses"
        if amount:
            sections[key].append(dict(a, amount=amount))
    s = {k: r2(sum(x["amount"] for x in v)) for k, v in sections.items()}
    gross = r2(s["revenue"] - s["cost"])
    net = r2(gross + s["other_income"] - s["expenses"])
    return dict(sections=sections, totals=s, gross=gross, net=net,
                gross_pct=round(gross / s["revenue"] * 100, 1) if s["revenue"] > 0 else None,
                net_pct=round(net / s["revenue"] * 100, 1) if s["revenue"] > 0 else None)


def month_start(d):
    return d.replace(day=1)


@app.route("/ledger/profit-loss")
@login_required
def profit_loss():
    today = date.today()
    preset = request.args.get("p", "")
    d_from, d_to = request.args.get("from", ""), request.args.get("to", "")
    if preset == "month":
        d_from, d_to = month_start(today).isoformat(), today.isoformat()
    elif preset == "last_month":
        last_end = month_start(today) - timedelta(days=1)
        d_from, d_to = month_start(last_end).isoformat(), last_end.isoformat()
    elif preset == "year":
        d_from, d_to = today.replace(month=1, day=1).isoformat(), today.isoformat()
    elif preset == "all":
        d_from = d_to = ""
    pl = profit_and_loss(d_from, d_to)
    prev = None
    if request.args.get("compare") and d_from:
        # the same number of days immediately before this period
        start = date.fromisoformat(d_from)
        end = date.fromisoformat(d_to) if d_to else today
        p_end = start - timedelta(days=1)
        p_start = p_end - (end - start)
        prev = dict(profit_and_loss(p_start.isoformat(), p_end.isoformat()), d_from=p_start.isoformat(), d_to=p_end.isoformat())
        # amounts by account for the comparison column
        prev["by_id"] = {x["id"]: x["amount"] for sec in prev["sections"].values() for x in sec}
        # accounts that only moved in the previous period still need a row
        for key, sec in prev["sections"].items():
            have = {x["id"] for x in pl["sections"][key]}
            pl["sections"][key] += [dict(x, amount=0) for x in sec if x["id"] not in have]
            pl["sections"][key].sort(key=lambda x: x["code"])
    return render_template("profit_loss.html", pl=pl, prev=prev, d_from=d_from, d_to=d_to, preset=preset,
                           compare=bool(request.args.get("compare")))


def next_jv_no():
    s = get_settings()
    n = int(s["jv_next"] or 1)
    while True:
        no = f"{s['jv_prefix']} {n:06d}"
        if not get_db().execute("SELECT 1 FROM journals WHERE jv_no = ?", (no,)).fetchone():
            return no, n
        n += 1


@app.route("/ledger/jv/new", methods=["GET", "POST"])
@login_required
def jv_new():
    db = get_db()
    accounts_ = db.execute("SELECT * FROM coa WHERE is_group = 0 AND active = 1 ORDER BY code").fetchall()
    if request.method == "POST":
        f = request.form
        valid = {a["id"] for a in accounts_}
        lines = []
        for aid, dr, cr, nar in zip(f.getlist("account_id"), f.getlist("debit"), f.getlist("credit"), f.getlist("line_narration")):
            dr, cr = r2(to_float(dr)), r2(to_float(cr))
            if not aid and not dr and not cr:
                continue
            if not aid.isdigit() or int(aid) not in valid or (dr and cr) or dr < 0 or cr < 0 or not (dr or cr):
                flash("Each line needs an account and either a debit or a credit amount.", "error")
                return redirect(request.url)
            lines.append((int(aid), dr, cr, nar.strip()))
        tdr, tcr = r2(sum(l[1] for l in lines)), r2(sum(l[2] for l in lines))
        narration = f.get("narration", "").strip()
        if len(lines) < 2 or not tdr or tdr != tcr:
            flash(f"A journal needs at least two lines and must balance (debit {money(tdr)} vs credit {money(tcr)}).", "error")
            return redirect(request.url)
        if not narration:
            flash("Narration is required.", "error")
            return redirect(request.url)
        no, n = next_jv_no()
        jid = db.execute("INSERT INTO journals(jv_no, jv_date, narration, created_by, created_at) VALUES (?,?,?,?,?)",
                         (no, f.get("jv_date") or date.today().isoformat(), narration, g.user["id"], now())).lastrowid
        db.executemany("INSERT INTO journal_lines(journal_id, account_id, debit, credit, narration) VALUES (?,?,?,?,?)",
                       [(jid, *l) for l in lines])
        gl_refresh("jv", jid)
        set_setting("jv_next", str(n + 1))
        db.commit()
        log("JOURNAL CREATE", f"Journal {no} - {narration} - {get_settings()['currency']} {money(tdr)}")
        flash(f"Journal {no} posted.", "ok")
        return redirect(url_for("jv_view", jid=jid))
    return render_template("jv_form.html", accounts=accounts_, today=date.today().isoformat(), preview_no=next_jv_no()[0])


@app.route("/ledger/jv/<int:jid>")
@login_required
def jv_view(jid):
    db = get_db()
    j = db.execute("""SELECT j.*, u.username, x.username AS cancelled_name FROM journals j LEFT JOIN users u ON u.id = j.created_by
                      LEFT JOIN users x ON x.id = j.cancelled_by WHERE j.id = ?""", (jid,)).fetchone() or abort(404)
    lines = db.execute("""SELECT l.*, a.code, a.name FROM journal_lines l JOIN coa a ON a.id = l.account_id
                          WHERE l.journal_id = ? ORDER BY l.id""", (jid,)).fetchall()
    return render_template("jv_view.html", j=j, lines=lines)


@app.route("/ledger/jv/<int:jid>/cancel", methods=["POST"])
@admin_required
def jv_cancel(jid):
    db = get_db()
    j = db.execute("SELECT * FROM journals WHERE id = ?", (jid,)).fetchone() or abort(404)
    reason = request.form.get("reason", "").strip()
    if j["status"] != "Posted" or not reason:
        flash("Give a reason to cancel a posted journal.", "error")
        return redirect(url_for("jv_view", jid=jid))
    db.execute("UPDATE journals SET status = 'Cancelled', cancel_reason = ?, cancelled_by = ?, cancelled_at = ? WHERE id = ?",
               (reason, g.user["id"], now(), jid))
    gl_refresh("jv", jid)
    db.commit()
    log("JOURNAL CANCEL", f"Cancelled journal {j['jv_no']}: {reason}")
    flash(f"{j['jv_no']} cancelled.", "ok")
    return redirect(url_for("jv_view", jid=jid))


# ---------------------------------------------------------------- settings

def save_image(file, key, ent):
    """Save an uploaded logo / stamp of an entity; returns the value to store in its settings, or None if not an image."""
    ext = os.path.splitext(secure_filename(file.filename))[1].lower()
    if ext not in (".png", ".jpg", ".jpeg", ".gif", ".webp"):
        return None
    os.makedirs(UPLOAD_DIR, exist_ok=True)
    # files of the first entity keep their old names; others are named after their entity
    name = f"{key}{ext}" if ent["db_file"] == "billing.db" else f"{ent['code'].lower()}_{key}{ext}"
    file.save(os.path.join(UPLOAD_DIR, name))
    return f"{name}?v={int(datetime.now().timestamp())}"


# the business profile: who the entity is, printed on its documents (entered when an entity is created, then in Settings)
PROFILE_KEYS = ("company_name", "company_name_ar", "address_lines", "trn", "bank_iban", "bank_bic", "bank_name",
                "footer_note", "footer_address", "email", "website", "phone", "mobile")


@app.route("/settings", methods=["GET", "POST"])
@admin_required
def settings():
    if request.method == "POST":
        s = get_settings()
        changed = []
        for key in DEFAULT_SETTINGS:
            if key in ("logo", "stamp"):
                continue
            if key in request.form and request.form[key] != s.get(key):
                set_setting(key, request.form[key])
                changed.append(key)
        for key in ("logo", "stamp"):
            file = request.files.get(key)
            if file and file.filename:
                stored = save_image(file, key, g.entity)
                if stored is None:
                    flash(f"{key.title()} must be an image file.", "error")
                    continue
                set_setting(key, stored)
                changed.append(key)
            elif request.form.get(f"remove_{key}"):
                set_setting(key, "")
                changed.append(key)
        get_db().commit()
        if "company_name" in changed and get_settings()["company_name"].strip():  # the entity is listed by its company name
            main_db().execute("UPDATE entities SET name = ? WHERE id = ?", (get_settings()["company_name"].strip(), g.entity["id"]))
            main_db().commit()
        if changed:
            log("SETTINGS UPDATE", "Changed: " + ", ".join(changed))
        flash("Settings saved.", "ok")
        return redirect(url_for("settings"))
    return render_template("settings.html")


# ---------------------------------------------------------------- admin panel

@app.route("/admin/unlock", methods=["GET", "POST"])
@admin_required
def admin_unlock():
    if request.method == "POST":
        if check_password_hash(g.user["password_hash"], request.form.get("password", "")):
            session["admin_unlocked_at"] = datetime.now().timestamp()
            log("ADMIN UNLOCK", "Opened Admin Panel with password")
            nxt = request.args.get("next", "")
            return redirect(nxt if nxt.startswith("/") else url_for("admin_users"))
        log("ADMIN UNLOCK FAILED", "Wrong password for Admin Panel")
        flash("Wrong password.", "error")
    return render_template("admin_unlock.html")


@app.route("/admin/lock")
@login_required
def admin_lock():
    session.pop("admin_unlocked_at", None)
    log("ADMIN LOCK", "Locked Admin Panel")
    return redirect(url_for("dashboard"))


@app.route("/admin", methods=["GET", "POST"])
@admin_panel_required
def admin_users():
    """User setup: who the user is, how they log in, which entities and modules they work in."""
    mdb = main_db()
    roles = {r["id"]: r for r in mdb.execute("SELECT * FROM roles ORDER BY is_admin DESC, name")}
    edit = None
    if request.args.get("edit"):
        edit = mdb.execute("SELECT * FROM users WHERE id = ?", (request.args["edit"],)).fetchone()
    if request.method == "POST":
        f = request.form
        uid = f.get("id", type=int)
        back = url_for("admin_users", edit=uid) if uid else url_for("admin_users", new=1)
        role = roles.get(f.get("role_id", type=int))
        if role is None:
            flash("Choose the role.", "error")
            return redirect(back)
        valid = {e["id"] for e in all_entities()}
        ents = sorted({int(x) for x in f.getlist("entity") if x.isdigit() and int(x) in valid})
        perms = perms_from_form(f)
        mods = [m for m in MODULE_KEYS if any(perms[k] for k, fm, _, _ in FEATURES if fm == m)]
        if not role["is_admin"] and not ents:
            flash("Tick at least one business entity the user can work in.", "error")
            return redirect(back)
        if not role["is_admin"] and not mods:
            flash("Give the user access to at least one function.", "error")
            return redirect(back)
        full_name = f.get("full_name", "").strip()
        if not full_name:
            flash("Enter the user name (the person's full name).", "error")
            return redirect(back)
        vals = dict(full_name=full_name, email=f.get("email", "").strip(), mobile=f.get("mobile", "").strip(),
                    role_id=role["id"], role="admin" if role["is_admin"] else "user", modules=",".join(mods),
                    perms=json.dumps(perms),
                    active=1 if f.get("active") else 0, must_change_pw=1 if f.get("must_change_pw") else 0)
        pw = f.get("password", "")
        if pw and password_problem(pw):
            flash(password_problem(pw), "error")
            return redirect(back)
        notes = []
        if uid:
            old = mdb.execute("SELECT * FROM users WHERE id = ?", (uid,)).fetchone() or abort(404)
            if uid == g.user["id"] and (not role["is_admin"] or not vals["active"]):
                flash("You cannot remove your own admin rights or deactivate yourself.", "error")
                return redirect(back)
            if pw:
                vals.update(password_hash=generate_password_hash(pw), pw_changed_at=now(), failed_logins=0, locked_at=None)
                notes.append("password reset" + (", must change at next login" if vals["must_change_pw"] else ""))
            if f.get("unlock") and old["locked_at"]:
                vals.update(failed_logins=0, locked_at=None)
                notes.append("unlocked")
            mdb.execute(f"UPDATE users SET {', '.join(k + ' = ?' for k in vals)} WHERE id = ?", (*vals.values(), uid))
            username, action = old["username"], "USER EDIT"
        else:
            username = f.get("username", "").strip()
            if not re.fullmatch(r"[A-Za-z0-9._@-]{2,30}", username):
                flash("User ID: 2-30 letters, digits or . _ @ - (no spaces).", "error")
                return redirect(back)
            if mdb.execute("SELECT 1 FROM users WHERE lower(username) = lower(?)", (username,)).fetchone():
                flash(f"User ID {username} already exists.", "error")
                return redirect(back)
            if not pw:
                flash("Enter a password for the new user.", "error")
                return redirect(back)
            vals.update(username=username, password_hash=generate_password_hash(pw), pw_changed_at=now(),
                        created_at=now(), created_by=g.user["id"])
            uid = mdb.execute(f"INSERT INTO users({', '.join(vals)}) VALUES ({', '.join('?' * len(vals))})",
                              tuple(vals.values())).lastrowid
            action = "USER ADD"
        photo = request.files.get("photo")
        if photo and photo.filename:
            stored = save_user_photo(photo, uid)
            if stored is None:
                flash("The photo must be an image file.", "error")
            else:
                mdb.execute("UPDATE users SET photo = ? WHERE id = ?", (stored, uid))
        elif f.get("remove_photo"):
            mdb.execute("UPDATE users SET photo = '' WHERE id = ?", (uid,))
        mdb.execute("DELETE FROM user_entities WHERE user_id = ?", (uid,))
        mdb.executemany("INSERT INTO user_entities(user_id, entity_id) VALUES (?, ?)", [(uid, e) for e in ents])
        mdb.commit()
        sync_users()
        codes = [e["code"] for e in all_entities() if e["id"] in ents]
        log(action, f"{'Created' if action == 'USER ADD' else 'Edited'} user '{username}' ({full_name}): role {role['name']}, "
            + ("all entities, full access" if role["is_admin"] else f"entities {', '.join(codes)}, access {perms_text(perms)}")
            + f", {'active' if vals['active'] else 'disabled'}" + "".join(", " + n for n in notes))
        flash(f"User {username} {'created' if action == 'USER ADD' else 'updated'}.", "ok")
        return redirect(url_for("admin_users", edit=uid))
    users = mdb.execute("SELECT u.*, r.name AS role_name FROM users u LEFT JOIN roles r ON r.id = u.role_id "
                        "ORDER BY u.active DESC, u.username").fetchall()
    access = {}
    for r in mdb.execute("SELECT user_id, entity_id FROM user_entities"):
        access.setdefault(r["user_id"], set()).add(r["entity_id"])
    role_perms = {r["id"]: user_perms(dict(r, role="admin" if r["is_admin"] else "user")) for r in roles.values()}
    return render_template("admin_users.html", users=users, edit=edit, new=bool(request.args.get("new")) or not edit,
                           edit_perms=user_perms(edit) if edit else None, role_perms=role_perms,
                           access=access, entities=all_entities(), roles=list(roles.values()),
                           locked_until=lambda u: (datetime.strptime(u["locked_at"], "%Y-%m-%d %H:%M:%S")
                                                   + timedelta(minutes=LOCK_MINUTES)).strftime("%Y-%m-%d %H:%M")
                           if u["locked_at"] else None)


@app.route("/admin/roles", methods=["GET", "POST"])
@admin_panel_required
def admin_roles():
    """Roles: a named set of modules (or full administration) given to users in their user setup."""
    mdb = main_db()
    nxt = request.values.get("next", "")
    nxt = nxt if nxt.startswith("/") else ""
    edit = None
    if request.args.get("edit"):
        edit = mdb.execute("SELECT * FROM roles WHERE id = ?", (request.args["edit"],)).fetchone()
    if request.method == "POST":
        f = request.form
        rid = f.get("id", type=int)
        if f.get("delete") and rid:
            used = mdb.execute("SELECT COUNT(*) FROM users WHERE role_id = ?", (rid,)).fetchone()[0]
            if used:
                flash(f"This role is given to {used} user(s): change their role first.", "error")
            else:
                name = mdb.execute("SELECT name FROM roles WHERE id = ?", (rid,)).fetchone()["name"]
                mdb.execute("DELETE FROM roles WHERE id = ?", (rid,))
                mdb.commit()
                log("ROLE DELETE", f"Deleted role '{name}'")
                flash(f"Role {name} deleted.", "ok")
            return redirect(url_for("admin_roles"))
        name = f.get("name", "").strip()
        is_admin = 1 if f.get("is_admin") else 0
        perms = perms_from_form(f) if not is_admin else {k: FULL for k in FEATURE_KEYS}
        mods = [m for m in MODULE_KEYS if any(perms[k] for k, fm, _, _ in FEATURES if fm == m)]
        back = url_for("admin_roles", edit=rid, next=nxt or None)
        if not name or not mods:
            flash("Enter the role name and give it access to at least one function.", "error")
            return redirect(back)
        if mdb.execute("SELECT 1 FROM roles WHERE lower(name) = lower(?) AND id != ?", (name, rid or 0)).fetchone():
            flash(f"A role named {name} already exists.", "error")
            return redirect(back)
        if rid and not is_admin and g.user["role_id"] == rid:
            flash("This is your own role: you can't take administration away from it.", "error")
            return redirect(back)
        vals = (name, f.get("description", "").strip(), is_admin, ",".join(mods), json.dumps(perms))
        if rid:
            mdb.execute("UPDATE roles SET name = ?, description = ?, is_admin = ?, modules = ?, perms = ? WHERE id = ?",
                        (*vals, rid))
            mdb.execute("UPDATE users SET role = ? WHERE role_id = ?", ("admin" if is_admin else "user", rid))
            if f.get("apply_users"):  # give the users of this role its new matrix
                mdb.execute("UPDATE users SET perms = ?, modules = ? WHERE role_id = ?", (vals[4], vals[3], rid))
        else:
            rid = mdb.execute("INSERT INTO roles(name, description, is_admin, modules, perms, created_at) VALUES (?,?,?,?,?,?)",
                              (*vals, now())).lastrowid
        mdb.commit()
        sync_users()
        log("ROLE SAVE", f"Role '{name}': " + ("administrator (full access)" if is_admin else perms_text(perms))
            + (", applied to its users" if f.get("apply_users") else ""))
        flash(f"Role {name} saved." + (" Its users now have this access." if f.get("apply_users") else ""), "ok")
        return redirect(nxt or url_for("admin_roles"))
    roles = mdb.execute("""SELECT r.*, (SELECT COUNT(*) FROM users u WHERE u.role_id = r.id) AS users
                           FROM roles r ORDER BY r.is_admin DESC, r.name""").fetchall()
    as_perms = lambda r: user_perms(dict(r, role="admin" if r["is_admin"] else "user"))
    return render_template("admin_roles.html", roles=roles, edit=edit, nxt=nxt, as_perms=as_perms,
                           edit_perms=as_perms(edit) if edit else {k: NO for k in FEATURE_KEYS})


@app.route("/admin/entities", methods=["GET", "POST"])
@admin_panel_required
def admin_entities():
    mdb = main_db()
    if request.method == "POST":
        f = request.form
        if f.get("id"):  # rename / switch on or off
            ent = mdb.execute("SELECT * FROM entities WHERE id = ?", (f["id"],)).fetchone() or abort(404)
            name, active = f.get("name", "").strip() or ent["name"], 1 if f.get("active") else 0
            if not active and ent["id"] == g.entity["id"]:
                flash("You can't switch off the entity you are working in. Switch to another one first.", "error")
                return redirect(url_for("admin_entities"))
            mdb.execute("UPDATE entities SET name = ?, active = ? WHERE id = ?", (name, active, ent["id"]))
            mdb.commit()
            log("ENTITY EDIT", f"Business entity {ent['code']}: name '{name}', {'active' if active else 'inactive'}")
            flash(f"{ent['code']} updated.", "ok")
            return redirect(url_for("admin_entities"))
        code = f.get("code", "").strip().upper()
        name = f.get("company_name", "").strip()
        currency = f.get("currency", "").strip().upper() or base_currency()
        if not re.fullmatch(r"[A-Z0-9]{2,10}", code) or not name:
            flash("Enter a code of 2-10 letters / digits and the company name.", "error")
            return redirect(url_for("admin_entities"))
        if not re.fullmatch(r"[A-Z]{3}", currency):
            flash("The base currency is a 3-letter code, e.g. AED.", "error")
            return redirect(url_for("admin_entities"))
        if mdb.execute("SELECT 1 FROM entities WHERE code = ?", (code,)).fetchone() or                 os.path.exists(os.path.join(ENTITY_DIR, code.lower() + ".db")):
            flash(f"Business entity code {code} is already used.", "error")
            return redirect(url_for("admin_entities"))
        copy = set(f.getlist("copy"))
        profile = {k: f.get(k, "").strip() for k in PROFILE_KEYS}
        images = {k: request.files[k] for k in ("logo", "stamp") if request.files.get(k) and request.files[k].filename}
        bad = [k for k, file in images.items()
               if os.path.splitext(secure_filename(file.filename))[1].lower() not in (".png", ".jpg", ".jpeg", ".gif", ".webp")]
        if bad:
            flash(f"{' and '.join(k.title() for k in bad)} must be an image file.", "error")
            return redirect(url_for("admin_entities"))
        eid = create_entity(code, profile, currency, g.entity, copy)
        if images:
            ent = mdb.execute("SELECT * FROM entities WHERE id = ?", (eid,)).fetchone()
            edb = sqlite3.connect(entity_path(ent))
            edb.executemany("INSERT OR REPLACE INTO settings(key, value) VALUES (?, ?)",
                            [(k, save_image(file, k, ent)) for k, file in images.items()])
            edb.commit()
            edb.close()
        log("ENTITY ADD", f"Created business entity {code} · {name} ({currency})"
            + (f", copied {', '.join(sorted(copy))} from {g.entity['code']}" if copy else ""))
        flash(f"Business entity {code} · {name} created. Switch to it from the entity box at the top of the menu.", "ok")
        return redirect(url_for("admin_entities"))
    counts = {}
    for r in mdb.execute("SELECT entity_id, COUNT(*) FROM user_entities GROUP BY entity_id"):
        counts[r[0]] = r[1]
    return render_template("admin_entities.html", entities=all_entities(), counts=counts)


BILLING_ACTIONS = "(" + " OR ".join(f"action LIKE '{t} %'" for t in (*DOC_TYPES, "CUSTOMER", "SUPPLIER", "PRODUCT", "STOCK", "RECEIPT", "PAYMENT", "JOURNAL", "COA")) + ")"


def query_logs(args, billing_only=False, page=None):
    sql = "SELECT * FROM logs WHERE 1=1"
    params = []
    if billing_only:
        sql += " AND " + BILLING_ACTIONS
        groups = {"SALES": (*SALES_FLOW, "CUSTOMER"), "PURCHASE": (*PURCHASE_FLOW, "SUPPLIER")}
        prefixes = groups.get(args.get("type")) or ((args["type"],) if args.get("type") else ())
        if prefixes:
            sql += " AND (" + " OR ".join("action LIKE ?" for _ in prefixes) + ")"
            params += [f"{t} %" for t in prefixes]
    if args.get("user"):
        sql += " AND username = ?"
        params.append(args["user"])
    if args.get("action"):
        sql += " AND action LIKE ?"
        params.append(f"%{args['action']}%")
    if args.get("from"):
        sql += " AND created_at >= ?"
        params.append(args["from"])
    if args.get("to"):
        sql += " AND created_at <= ?"
        params.append(args["to"] + " 23:59:59")
    if args.get("q"):
        sql += " AND details LIKE ?"
        params.append(f"%{args['q']}%")
    limit = f" LIMIT {PAGE + 1} OFFSET {(page - 1) * PAGE}" if page else ""
    return get_db().execute(sql + " ORDER BY id DESC" + limit, params).fetchall()


@app.route("/billing/log")
@login_required
def billing_log():
    """Transaction log of billing entries; normal users only see their own."""
    args = request.args.to_dict()
    if g.user["role"] != "admin":
        args["user"] = g.user["username"]
    export = bool(request.args.get("export"))
    page = page_no()
    rows = query_logs(args, billing_only=True, page=None if export else page)
    users = [r["username"] for r in get_db().execute("SELECT DISTINCT username FROM logs ORDER BY username")]
    if export:
        out = io.StringIO()
        w = csv.writer(out)
        w.writerow(["Date/Time", "User", "Action", "Details"])
        for r in rows:
            w.writerow([r["created_at"], r["username"], r["action"], r["details"]])
        return Response("\ufeff" + out.getvalue(), mimetype="text/csv",
                        headers={"Content-Disposition": "attachment; filename=transaction_log.csv"})
    return render_template("billing_log.html", rows=rows[:PAGE], users=users, a=args, page=page, has_next=len(rows) > PAGE)


@app.route("/admin/logs")
@admin_panel_required
def admin_logs():
    page = page_no()
    rows = query_logs(request.args, page=page)
    users = [r["username"] for r in get_db().execute("SELECT DISTINCT username FROM logs ORDER BY username")]
    summary = get_db().execute("""SELECT username, COUNT(*) AS n, MAX(created_at) AS last
                                  FROM logs GROUP BY username ORDER BY n DESC""").fetchall()
    return render_template("logs.html", rows=rows[:PAGE], users=users, summary=summary, a=request.args,
                           page=page, has_next=len(rows) > PAGE)


@app.route("/admin/logs.csv")
@admin_panel_required
def admin_logs_csv():
    out = io.StringIO()
    w = csv.writer(out)
    w.writerow(["Date/Time", "User", "Action", "Details", "IP"])
    for r in query_logs(request.args):
        w.writerow([r["created_at"], r["username"], r["action"], r["details"], r["ip"]])
    log("LOG EXPORT", "Exported activity log to CSV")
    return Response("\ufeff" + out.getvalue(), mimetype="text/csv",
                    headers={"Content-Disposition": "attachment; filename=activity_log.csv"})


if __name__ == "__main__":
    init_all()
    host = os.environ.get("BILLING_HOST", "127.0.0.1")
    print(f"\n  Azzi Soft running at http://{'127.0.0.1' if host == '0.0.0.0' else host}:5000\n")
    try:
        # production web server: serves several users at once
        from waitress import serve
        serve(app, host=host, port=5000, threads=8)
    except ImportError:
        app.run(host=host, port=5000, debug=False, threaded=True)
