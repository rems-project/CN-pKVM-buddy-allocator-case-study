#/usr/bin/env bash
set -euo pipefail -o noclobber

cn verify --no-vip page_alloc.c --solver-logging=solver_logs &> final_results.txt &
tail --pid $! -fn +1 sovler_logs/z3_send_0.smt
cat final_results.txt

