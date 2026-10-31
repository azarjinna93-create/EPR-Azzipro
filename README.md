# Azzi Soft

Local billing software with A4 print, users, and a per-user activity log:
- **Sales:** Sales Order → Delivery Note → Tax Invoice
- **Purchase:** Purchase Order → GRN (Goods Received Note) → Purchase Invoice

## Start
Double-click `run.bat` (installs Flask + qrcode on first run, then opens http://127.0.0.1:5000).

First login: **admin / admin123**. Change it from the user name menu at the top right.

To use from other PCs on the office network, run `set BILLING_HOST=0.0.0.0` before `python app.py`, then open `http://<this-PC-IP>:5000`.

## Workflow
1. **Billing → New Sales Order** → Save as Draft or **Submit**.
2. On a submitted Sales Order, the **Create Delivery Note** button is enabled (disabled while Draft). Customer, details and items are copied.
3. On a submitted Delivery Note, the **Create Tax Invoice** button is enabled.
   The purchase flow works the same way: **Purchase → New Purchase Order** → submit → **Create GRN** → submit → **Create Purchase Invoice**.
4. Submitted documents are locked for normal users; admins can still edit and delete them. A document can't be deleted while a later document was created from it.

## Menus
- **Billing**: Sales Orders, Delivery Notes, Tax Invoices, Customers, Transaction Log
- **Purchase**: Purchase Orders, GRNs, Purchase Invoices, Suppliers, Transaction Log
- **Settings** (admin): company header, Arabic name, logo, stamp, bank, footer, numbering (e.g. `SALT 000677`), VAT %, defaults
- **Admin Panel** (admin): Users (add, disable, reset password, role) and Activity Log (filter by user, action or date; export to CSV)

Every login, logout, create, edit, submit, print, delete and settings/user change is logged with the user, time and IP address.

## Data
Everything is stored in `billing.db` (SQLite). Uploaded logo and stamp images go in `static/uploads/`. Back up both regularly.
