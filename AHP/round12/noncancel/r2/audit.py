#!/usr/bin/env python3
"""Static audit of the current compact certificates and independent shared compiles."""
from pathlib import Path
import re,hashlib,json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
ALLOWED={'propext','Classical.choice','Quot.sound'}
PAIR=[('Boundary','R2_Boundary'),('FullPlaquette','R2_FullPlaquette'),
      ('Mass','R2_Mass'),('RightFamily','R2_RightFamily'),('Attempt','R2_StarLocal')]
def strip_comments(s):
    i=0;depth=0;out=[]
    while i<len(s):
        if s.startswith('/-',i):depth+=1;i+=2
        elif depth and s.startswith('-/',i):depth-=1;i+=2
        elif depth:i+=1
        elif s.startswith('--',i):
            j=s.find('\n',i);i=len(s) if j<0 else j
        else:out.append(s[i]);i+=1
    assert depth==0
    return ''.join(out)
def audit_file(path):
    text=path.read_text();log=Path(str(path)+'.log').read_text()
    assert Path(str(path)+'.exit').read_text().strip()=='0',str(path)
    code=strip_comments(text)
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b',code),path
    assert not re.search(r'\b(?:sorryAx|error|warning):',log),log
    rec=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log,re.S)
    assert rec,str(path)
    declarations=[]
    for name,axes in rec:
        deps=set(re.findall(r'[\w.]+',axes))
        assert deps<=ALLOWED,(str(path),name,deps)
        declarations.append({'declaration':name,'axioms':sorted(deps)})
    printed=re.findall(r'^#print axioms (\S+)',code,re.M)
    assert len(printed)==len(rec),(path,len(printed),len(rec))
    assert re.findall(r'^import (.*)$',code,re.M)==['DrEquiv'],path
    return {'path':str(path.relative_to(ROOT)),'lines':len(text.splitlines()),
      'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'exitCode':0,
      'axiomRecords':len(rec),'declarations':declarations}
records=[]
for local,pub in PAIR:
    a=HERE/(local+'.lean');b=ROOT/'AHP/round12/shared/noncancel'/(pub+'.lean')
    assert a.read_bytes()==b.read_bytes(),(a,b)
    records.extend([audit_file(a),audit_file(b)])
for c in json.loads((HERE/'FAMILY_COPIES.json').read_text()):
    original=(ROOT/c['path']).read_text();i=original.index(c['start']);j=original.index(c['end'],i)
    assert hashlib.sha256(original[i:j].encode()).hexdigest()==c['sha256'],c
    assert original[i:j] in (HERE/'RightFamily.lean').read_text(),c
assert (HERE/'FullPlaquette.lean').read_text().startswith((ROOT/'AHP/round12/noncancel/r1/Plaquette.lean').read_text())
out={'track':'noncancel','round':2,'closedGoal':False,'disprovedGoal':False,
     'compiler':'AHP/round3/lean1.sh only','newNumerics':False,
     'allImportsFrozen':['DrEquiv'],'allAllowedAxioms':True,
     'pairedCompiles':records,
     'remaining':'Actual crossing-range/form positivity and crossing-specific CurlDetected, or direct whole-kernel NoResponseCancellation; no cofinal proof.'}
(HERE/'AUDIT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'pass':True,'certificates':len(records),'integratedLines':records[-1]['lines'],
                  'integratedAxiomRecords':records[-1]['axiomRecords'],
                  'closedGoal':False,'disprovedGoal':False},indent=2))
