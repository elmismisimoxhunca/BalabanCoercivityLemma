#!/usr/bin/env python3
"""Static and numerical-evidence audit for Round-15 dictionary R1."""
from pathlib import Path
import hashlib,json,re,fractions
H=Path(__file__).resolve().parent
LOCAL=H/'Collar.lean'; SHARED=H.parents[1]/'shared/dictionary/R1_Collar.lean'
GAPLOCAL=H/'PhysicalGap.lean'; GAPSHARED=H.parents[1]/'shared/dictionary/R1_PhysicalGap.lean'
ALLOWED={'propext','Classical.choice','Quot.sound'}
checks={}
checks['source_shared_byte_identity']=LOCAL.read_bytes()==SHARED.read_bytes()
checks['log_shared_byte_identity']=(LOCAL.with_suffix('.lean.log').read_bytes()==
  SHARED.with_suffix('.lean.log').read_bytes())
checks['local_exit_zero']=LOCAL.with_suffix('.lean.exit').read_text().strip()=='0'
checks['shared_exit_zero']=SHARED.with_suffix('.lean.exit').read_text().strip()=='0'
source=LOCAL.read_text()
checks['main_declaration_present']='theorem collar_dictionary' in source
checks['inverse_present']='theorem transfer_inverse' in source
checks['recurrence_present']='theorem dominant_recurrence' in source
checks['eigenpairs_present']='theorem dominant_eigenpairs' in source
forbidden=re.compile(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b')
checks['no_forbidden_mechanisms']=not bool(forbidden.search(source))
checks['only_frozen_import']=source.startswith('import DrEquiv\n') and '\nimport ' not in source[len('import DrEquiv\n'):]
records=[]
for path in (LOCAL.with_suffix('.lean.log'),SHARED.with_suffix('.lean.log')):
    text=path.read_text()
    checks[f'clean_{path.name}']=('warning' not in text.lower() and 'error' not in text.lower()
      and 'sorryAx' not in text)
    found=re.findall(r"depends on axioms: \[([^\]]*)\]",text)
    checks[f'axiom_records_{path.name}']=bool(found) and all(
      {x.strip() for x in rec.split(',')}<=ALLOWED for rec in found)
    records.append({'file':str(path),'count':len(found)})
checks['same_axiom_record_count']=records[0]['count']==records[1]['count'] and records[0]['count']>=20
checks['physical_gap_source_shared_byte_identity']=GAPLOCAL.read_bytes()==GAPSHARED.read_bytes()
checks['physical_gap_log_shared_byte_identity']=(GAPLOCAL.with_suffix('.lean.log').read_bytes()==
  GAPSHARED.with_suffix('.lean.log').read_bytes())
checks['physical_gap_local_exit_zero']=GAPLOCAL.with_suffix('.lean.exit').read_text().strip()=='0'
checks['physical_gap_shared_exit_zero']=GAPSHARED.with_suffix('.lean.exit').read_text().strip()=='0'
gap_source=GAPLOCAL.read_text()
checks['physical_gap_declaration_present']='def Q1C10PhysicalDictionary : Prop :=' in gap_source
checks['physical_gap_not_claimed_proved']='theorem Q1C10PhysicalDictionary' not in gap_source
checks['physical_gap_no_forbidden_mechanisms']=not bool(forbidden.search(gap_source))
gap_records=[]
for path in (GAPLOCAL.with_suffix('.lean.log'),GAPSHARED.with_suffix('.lean.log')):
    text=path.read_text()
    checks[f'clean_{path.name}']=('warning' not in text.lower() and 'error' not in text.lower()
      and 'sorryAx' not in text)
    found=re.findall(r"depends on axioms: \[([^\]]*)\]",text)
    checks[f'axiom_records_{path.name}']=bool(found) and all(
      {x.strip() for x in rec.split(',')}<=ALLOWED for rec in found)
    gap_records.append({'file':str(path),'count':len(found)})
checks['physical_gap_same_axiom_record_count']=(gap_records[0]['count']==gap_records[1]['count']
  and gap_records[0]['count']>=2)
factor=json.loads((H/'FACTOR_AUDIT.json').read_text())
checks['factor_audit_pass']=factor['pass'] and max(r['charpoly_relative_error'] for r in factor['records'])<1e-7
for R in (20,22):
    x=json.loads((H/f'crossing_q1_R{R}_c1_0.json').read_text())
    checks[f'crossing_R{R}_sector_matches']=float(x['sector_relative_error'])<(1e-15 if R==20 else 1e-20)
    checks[f'crossing_R{R}_recurrence']=float(x['max_deep_recurrence_relative_error'])<1e-12
    checks[f'crossing_R{R}_modal_one_step']=float(x['modal_one_step_relative_error'])<1e-12
# Recheck the exact companion inverse from the retained Gaussian-rational data.
def frac(s):
    p=s.split('/')
    return fractions.Fraction(int(p[0]),int(p[1]) if len(p)==2 else 1)
def cval(z):return complex(frac(z[0]),frac(z[1]))
data=json.loads((H/'exact_transfer.json').read_text())
T=[[cval(z) for z in row] for row in data['T']]
Ti=[[cval(z) for z in row] for row in data['Tinverse']]
ident=[[1.0 if i==j else 0.0 for j in range(16)] for i in range(16)]
def mm(A,B):
    return [[sum(A[i][k]*B[k][j] for k in range(16)) for j in range(16)] for i in range(16)]
def maxdiff(A,B):return max(abs(A[i][j]-B[i][j]) for i in range(16) for j in range(16))
checks['exact_inverse_left']=maxdiff(mm(T,Ti),ident)<1e-10
checks['exact_inverse_right']=maxdiff(mm(Ti,T),ident)<1e-10
for name in ('factor_audit','build_lean','build_physical_gap','interface_c10','crossing_c10','crossing_c10_R22'):
    checks[f'{name}_exit_zero']=(H/f'{name}.exit').read_text().strip()=='0'
for iy in range(4):
    for iz in range(4):
        checks[f'full_c{iy}{iz}_exit_zero']=(H/f'full_c{iy}{iz}.exit').read_text().strip()=='0'
checks['all']=all(checks.values())
result={'pass':checks['all'],'checks':checks,'axiom_records':records,
  'source_sha256':hashlib.sha256(LOCAL.read_bytes()).hexdigest(),
  'shared_sha256':hashlib.sha256(SHARED.read_bytes()).hexdigest(),
  'factor_worst_relative_error':max(r['charpoly_relative_error'] for r in factor['records']),
  'physical_gap_axiom_records':gap_records,
  'physicalGapDeclaration':'AdalyFormal.Round15.Dictionary.Q1C10PhysicalDictionary',
  'mainDeclaration':'AdalyFormal.Round15.Dictionary.collar_dictionary',
  'qualification':'Exact compiled model certificate plus non-interval numerical evidence. The frozen right-star physical identification and area seed remain open.'}
(H/'AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
(H/'audit.exit').write_text('0\n' if result['pass'] else '1\n')
print(json.dumps({'pass':result['pass'],'checks_failed':[k for k,v in checks.items() if not v],
  'axiom_records':records,'source_sha256':result['source_sha256']},indent=2))
raise SystemExit(0 if result['pass'] else 1)
