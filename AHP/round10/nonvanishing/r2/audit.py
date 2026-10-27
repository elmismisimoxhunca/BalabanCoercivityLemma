#!/usr/bin/env python3
"""Artifact audit, not mathematical evidence for GoalNeg2 or the dictionary."""
import hashlib,json,re
from pathlib import Path
p=Path(__file__).resolve().parent
shared=p.parents[1]/'shared'/'nonvanishing'/'R2_SourceFamily.lean'
allowed={'propext','Classical.choice','Quot.sound'}
rows=[]
for f in [p/'DirichletResponse.lean',p/'TridiagonalResponse.lean',p/'SourceFamily.lean',shared]:
    s=f.read_text(); log=Path(str(f)+'.log'); ex=Path(str(f)+'.exit')
    l=log.read_text()
    records=re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]",l,re.S)
    deps=[set(x.strip() for x in r.split(',') if x.strip()) for _,r in records]
    decls=re.findall(r'^(?:noncomputable )?(?:def|theorem|lemma)\s+(\w+)',s,re.M)
    printed={name.rsplit('.',1)[-1] for name,_ in records}
    row={
        'path':str(f.relative_to(p.parents[3])),
        'sha256':hashlib.sha256(s.encode()).hexdigest(),
        'lines':len(s.splitlines()),'declaration_count':len(decls),'axiom_records':len(records),
        'exit':int(ex.read_text().strip()),
        'imports':re.findall(r'^import (.+)$',s,re.M),
        'every_declaration_audited':set(decls)<=printed,
        'standard_axioms_only':bool(records) and all(d<=allowed for d in deps),
        'no_prohibited_devices':re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b',s) is None,
        'no_diagnostics':not re.search(r'\berror:|\berror\(|\bwarning:|sorryAx',l),
        'timestamps_ok':f.stat().st_mtime<=log.stat().st_mtime<=ex.stat().st_mtime,
    }
    row['pass']=all([row['exit']==0,row['imports']==['D1IVT'],row['every_declaration_audited'],
        row['standard_axioms_only'],row['no_prohibited_devices'],row['no_diagnostics'],row['timestamps_ok']])
    rows.append(row)
result={
    'goalNeg2_proved':False,'round9_premise_proved':False,
    'actual_source_dictionary_proved':False,'actual_crossing_jet_nonzero_proved':False,
    'fixed_source_coupling_nonzero_proved':False,
    'finite_model_all_source_nonvanishing_proved':True,
    'published_byte_equal':(p/'SourceFamily.lean').read_bytes()==shared.read_bytes(),
    'tridiagonal_assembly_equal':(p/'TridiagonalResponse.lean').read_text()==(p/'DirichletResponse.lean').read_text()+(p/'TridiagonalPart.lean.txt').read_text(),
    'full_assembly_equal':(p/'SourceFamily.lean').read_text()==(p/'TridiagonalResponse.lean').read_text()+(p/'SourceFamilyPart.lean.txt').read_text(),
    'files':rows,
}
result['pass']=all(r['pass'] for r in rows) and result['published_byte_equal'] and result['tridiagonal_assembly_equal'] and result['full_assembly_equal']
(p/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
raise SystemExit(0 if result['pass'] else 1)
