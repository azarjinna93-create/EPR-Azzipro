#!/bin/sh
# Nightly backup of every entity database (safe while the app runs), kept for 30 days.
# Install: chmod +x /opt/azzi/deploy/backup.sh
#          echo "30 1 * * * root /opt/azzi/deploy/backup.sh" > /etc/cron.d/azzi-backup
set -e
cd /opt/azzi
dest=/opt/azzi-backups/$(date +%Y-%m-%d)
mkdir -p "$dest/entities"
sqlite3 billing.db ".backup '$dest/billing.db'"
for f in entities/*.db; do
    [ -e "$f" ] && sqlite3 "$f" ".backup '$dest/$f'"
done
cp -r static/uploads "$dest/" 2>/dev/null || true
find /opt/azzi-backups -mindepth 1 -maxdepth 1 -type d -mtime +30 -exec rm -rf {} +
