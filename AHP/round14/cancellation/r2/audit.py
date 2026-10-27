#!/usr/bin/env python3
"""Final source/log/publication audit for cancellation R2."""
from pathlib import Path
import json,re,hashlib
OUT=Path(__file__).resolve().parent
SHARED=OUT.parents[1]/'shared/cancellation/R2_AreaStructure.lean'
local=OUT/'AreaStructure.lean'
allowed={'propext','Classical.choice','Quot.sound'}
records=[]
for path in [local,SHARED]:
 source=path.read_text()
 exit_code=Path(str(path)+'.exit').read_text().strip()
 log=Path(str(path)+'.log').read_text()
 assert exit_code=='0',(path,exit_code)
 assert not re.search(r'\b(warning|error|sorryAx)\b',log),path
 assert not re.search(r'\b(sorry|admit|native_decide|unsafe|implemented_by|extern|opaque)\b',source),path
 assert not re.search(r'\baxiom\b',source),path
 found=re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",log,re.S)
 for name,body in found:
  axioms={x.strip() for x in body.replace('\n',' ').split(',')}
  assert axioms<=allowed,(path,name,axioms)
  if 'AdalyFormal.Round14.Cancellation.' in name: records.append((str(path),name,sorted(axioms)))
 assert len(found)==298,(path,len(found))
 assert not re.search(r'\b(lake build|REPRODUCE)\b',source),path
assert local.read_bytes()==SHARED.read_bytes()
sha=hashlib.sha256(local.read_bytes()).hexdigest()
assert sha=='8f82949c0a5a92817ab1343ceab8218c96a41730b9a22787954dfae2ba040b0f'
for name in ['row_profile_right_q1_R20_p40_tail72','row_profile_right_q1_R20_p80_early80',
             'structure_right_q1_R22_p40','analyze']:
 assert (OUT/f'{name}.exit').read_text().strip()=='0',name
profile=json.loads((OUT/'PROFILE_ANALYSIS.json').read_text())
assert profile['row_profile']['row_count']==84
assert profile['row_profile']['all_rows_positive']
assert profile['row_profile']['early_precision_check']['exit']=='0'
notes=(OUT/'NOTES.md').read_text()
for phrase in ['P3, CofinalP3, and GoalNeg2 are not proved','areaSum_affine',
               'chargedArea_eventually_pos_of_matrix_limit','Exact statements still missing']:
 assert phrase in notes,phrase
result={'local':str(local),'shared':str(SHARED),'sha256':sha,'exit_codes':[0,0],
 'axiom_records_each':298,'new_declaration_records':len(records),
 'new_declarations':sorted({name for _,name,_ in records}),
 'all_axioms_permitted':True,'logs_warning_free':True,'forbidden_mechanisms_absent':True,
 'local_shared_byte_identical':True,'numerical_auxiliary_exits_zero':True,
 'row_profile_count':84,'early_precision_check_max_relative_error':
   profile['row_profile']['early_precision_check']['max_relative_error'],
 'p3_closed':False,'cofinalP3_closed':False,'goalNeg2_closed':False}
(OUT/'AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
