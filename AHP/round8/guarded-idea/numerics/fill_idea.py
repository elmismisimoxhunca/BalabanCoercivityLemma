#!/usr/bin/env python3
"""Insert section 6 (NUMERICS_TEXT.md + summarise.py tables) into IDEA.md."""
import subprocess, sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
tables = subprocess.run([sys.executable, str(HERE / 'summarise.py')], capture_output=True, text=True, timeout=300).stdout
(HERE / 'tables.md').write_text(tables)
parts = tables.split('\n\n')
sep, vac = parts[0].strip(), parts[1].strip()
txt = (HERE / 'NUMERICS_TEXT.md').read_text().replace('SEPARATION_TABLE', sep).replace('VACUUM_TABLE', vac)
idea = HERE.parent / 'IDEA.md'
s = idea.read_text()
start = s.index('## 6. Numerical evidence')
end = s.index('## 7. Files, commands and verification')
s = s[:start] + '## 6. Numerical evidence\n\n' + txt.strip() + '\n\n' + s[end:]
idea.write_text(s)
print('filled; Q4_SEP present:', 'Q4_SEP' in s)
