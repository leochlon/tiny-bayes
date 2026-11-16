#!/bin/sh
# Copies the weight modules exact/CON/W into both induction developments (namespace PRO in lower_bound).
set -e
cd "$(dirname "$0")"
rm -rf upper_bound/CON/W lower_bound/PRO/W
cp -R ../exact/CON/W upper_bound/CON/W
cp -R ../exact/CON/W lower_bound/PRO/W
perl -pi -e 's/\bCON\b/PRO/g' lower_bound/PRO/W/*.lean
