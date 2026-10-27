#!/usr/bin/env python3
"""Audit only compact detection artifacts and retained numerical evidence."""
from pathlib import Path
from decimal import Decimal, localcontext
import hashlib, json, re, resource
resource.setrlimit(resource.RLIMIT_AS, (2*1024**3, 2*1024**3))
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(text): return hashlib.sha256(text.encode()).hexdigest()
compiles=[]
for name in ['FlatUnit','JetBridge','Transfer','ColorTrace']:
    local=HERE/(name+'.lean')
    shared=ROOT/'AHP/round13/shared/detection'/('R1_'+name+'.lean')
    assert local.read_bytes()==shared.read_bytes(), (name,'publication mismatch')
    for p in [local,shared]:
        source=p.read_text(); log=Path(str(p)+'.log').read_text()
        rc=int(Path(str(p)+'.exit').read_text())
        assert rc==0, (p,rc)
        assert not re.search(r'\berror(?:\(|:)|sorryAx',log),p
        assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b',source),p
        recs=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log)
        assert recs,p
        for n,a in recs:
            assert {x.strip() for x in a.split(',')}<=ALLOWED,(p,n,a)
        compiles.append(dict(path=str(p.relative_to(ROOT)),exit=rc,lines=len(source.splitlines()),
            sha256=sha(source),logSha256=sha(log),axiomRecords=len(recs),
            newRecords=[dict(declaration=n,axioms=[x.strip() for x in a.split(',')])
                for n,a in recs if n.startswith('AdalyFormal.Round13.Detection.')]))
copies=[]
for manifest in ['FLAT_UNIT_COPIES.json','JET_BRIDGE_COPIES.json','COLOR_TRACE_COPIES.json']:
    for r in json.loads((HERE/manifest).read_text()):
        source=(ROOT/r['path']).read_text()
        if r.get('entireFile'):
            text=source
        else:
            a=source.index(r['start']); b=source.index(r['end'],a) if r.get('end') else len(source)
            text=source[a:b]
        assert sha(text)==r['sha256'],(manifest,r['path'],r.get('start'))
        copies.append(dict(manifest=manifest,path=r['path'],sha256=r['sha256']))
# A read-only check of prior round evidence; no new eigenproblem is solved here.
# max(abs(cell)) > abs(sum(cells)) excludes a common cell sign at that precision.
evidence=[]
with localcontext() as ctx:
    ctx.prec=180
    for precision in [120,155]:
        path=ROOT/f'AHP/round12/kernel/r2/star_right_q2_R20_p{precision}.json'
        d=json.loads(path.read_text())
        sums=[Decimal(s) for s in d['first_physical_top_jet_sums']]
        maxima=[Decimal(s) for s in d['max_abs_first_top_jet']]
        ratios=[m/abs(s) for s,m in zip(sums,maxima)]
        assert all(r>1 for r in ratios)
        evidence.append(dict(path=str(path.relative_to(ROOT)),sha256=sha(path.read_text()),
            maxOverAbsSum=[str(x) for x in ratios],
            conclusion='Retained floating-point data has mixed cell signs in all three directions; NOT a Lean physical sign certificate.'))
result=dict(status='P3 OPEN; compact supporting certificates only',compiles=compiles,
    copyChecks=copies,retainedNumericalEvidence=evidence)
(HERE/'AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(compiles=len(compiles),copyChecks=len(copies),allPermitted=True,
    retainedMaxOverAbsSum=[[float(x) for x in e['maxOverAbsSum']] for e in evidence]),indent=2))
