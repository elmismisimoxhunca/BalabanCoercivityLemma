#!/usr/bin/env python3
"""Read-only publication audit, after the dictionary worker finishes compilation."""
from pathlib import Path
import re,json,hashlib
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
p=ROOT/'AHP/round10/shared/dictionary/R2_SourceDictionary.lean'
s=p.read_text();lp=Path(str(p)+'.log'); ep=Path(str(p)+'.exit'); log=lp.read_text()
rr=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log,re.S)
checks={part:(ROOT/'AHP/round10/dictionary/r2'/part).read_text().removeprefix('import DrEquiv\n') in s for part in ['PhaseSource.lean','KKT.lean','SourceAppendix.lean']}
standard=bool(rr) and all(set(a.strip() for a in ax.split(','))<={'propext','Classical.choice','Quot.sound'} for n,ax in rr)
current=p.stat().st_mtime<=lp.stat().st_mtime<=ep.stat().st_mtime
clean=not re.search('error:|warning:|sorryAx',log)
status=ep.read_text().strip()=='0' and standard and current and clean and all(checks.values())
report={'pass':status,'path':str(p.relative_to(ROOT)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
    'exit':ep.read_text().strip(),'axiom_records':len(rr),'only_standard_axioms':standard,'timestamps_current':current,
    'no_diagnostics':clean,'read_parts_verbatim':checks,
    'actual_source_derivative_stencil_proved':status,'physical_one_dimensional_source_certificate_proved':False,
    'cofinal_coupling_proved':False}
(HERE/'DICTIONARY_REVIEW.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
raise SystemExit(not status)
