#!/usr/bin/env python3
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
s=(ROOT/'AHP/round15/dictionary/r2/Support.lean').read_text()
k=(ROOT/'AHP/round15/dictionary/r2/KData.lean').read_text()
k=k.replace('import DrEquiv\n','',1)
marker='theorem q1_raw_stencil'
pre,ex=s.split(marker,1)
(ROOT/'AHP/round15/dictionary/r2/Stencil.lean').write_text(pre+'\n'+k+'\n'+marker+ex)
print('wrote Stencil.lean',len(s)+len(k))
