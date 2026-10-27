#!/usr/bin/env python3
"""Run the required Lean wrapper in an 8-GiB memory-capped systemd scope.
Virtual/data limits cannot be used: frozen mathlib imports map >8 GiB of oleans.
"""
import json
from pathlib import Path
import resource
import subprocess
import sys
import time

root = Path(__file__).resolve().parents[4]
target = Path(sys.argv[1]).resolve()
allowed = [root / 'AHP/round12/noncancel/r1', root / 'AHP/round12/shared']
assert target.suffix == '.lean' and any(target.is_relative_to(p) for p in allowed)
cap = 8 * 1024**3
start = time.monotonic()
rc = subprocess.run(['systemd-run', '--user', '--scope', '--quiet',
    '-p', 'MemoryMax=8G', '-p', 'MemorySwapMax=0', '--',
    'bb', 'heavy', 'run', '--', 'AHP/round3/lean1.sh', str(target)], cwd=root).returncode
rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
Path(str(target) + '.resources.json').write_text(json.dumps({
    'exit': rc, 'max_child_rss_KiB': rss, 'seconds': time.monotonic()-start,
    'scope_memory_limit_bytes': cap, 'rss_below_8_GiB': rss < cap // 1024,
}, indent=2) + '\n')
assert rss < cap // 1024, 'RSS exceeded the per-command budget'
sys.exit(rc)
