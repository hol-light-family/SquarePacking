#!/bin/bash
# Build one case in a fresh HOL Light session:
#
#     HOLLIGHT_DIR=<HOL Light directory> shared/build.sh n12/make.ml
#
# The make file is piped into HOL Light's own launcher, $HOLLIGHT_DIR/hol.sh, phrase by phrase:
# an error in one phrase does not stop the rest and is visible in the log.  The log is written
# next to the make file (n12/make.ml -> n12/make.log); the important lines are printed at the end.
# There is no time limit (use e.g. `timeout` around this script if you want one).
# The Python oracles (shared/tools/*.py) are run with $SQ_PYTHON, else .venv/bin/python, else python3.
#
# Exit status: 0 if the log contains a "STATEMENT CHECKED" line (printed only after the
# mechanical check of the statement has passed) and no error line (an OCaml "Error",
# an uncaught "Exception", or a "FAILED"/"STAGEFAIL" report); 1 otherwise.
set -e
: "${HOLLIGHT_DIR:?set HOLLIGHT_DIR to the HOL Light directory (the one containing hol.sh)}"
[ $# -eq 1 ] || { echo "usage: shared/build.sh n<N>/make.ml" >&2; exit 2; }
cd "$(dirname "$0")/.."
log="${1%.ml}.log"
# hol.sh wraps the toplevel in $LINE_EDITOR (default ledit), which is only useful on a terminal.
(cat "$1"; echo 'print_string "BUILD_END\n";;') |
  LINE_EDITOR=env "$HOLLIGHT_DIR/hol.sh" 2>&1 | sed 's/\x1b\[[0-9;]*m//g' > "$log"
errors='^(# )?(Error|Exception)|FAILED|STAGEFAIL'
grep -aE "^(# )?FINAL|STATEMENT CHECKED|$errors" "$log" | grep -v "FINAL add" | tail -40 || true
if grep -aqE "$errors" "$log"; then
  echo "BUILD FAILED: errors in $log" >&2; exit 1
elif ! grep -aq "STATEMENT CHECKED" "$log"; then
  echo "BUILD FAILED: no STATEMENT CHECKED line in $log" >&2; exit 1
fi
echo "BUILD OK: $log"
