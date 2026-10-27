#!/usr/bin/env bash
set -euo pipefail
export PATH="/home/sebastian/.elan/bin:${PATH}"
unset http_proxy https_proxy HTTP_PROXY HTTPS_PROXY ALL_PROXY all_proxy
cd /home/sebastian/BalabanCoercivityLemma
export MAX_LEAN=4
export LEAN_NUM_THREADS=1
export MIN_AVAIL_GB=16
exec /home/sebastian/.bb-machines/bb-s6.mesh.srtv.cl/runtime/node_modules/bb-app/host-daemon/dist/bb heavy run -- ./REPRODUCE.sh
