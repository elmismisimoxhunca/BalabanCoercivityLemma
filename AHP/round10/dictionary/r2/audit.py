#!/usr/bin/env python3
"""Audit final source, wrapper exits, dependency records and copied declarations."""
from pathlib import Path
import hashlib, json, re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
paths=[HERE/'PhaseSource.lean',HERE/'KKT.lean',HERE/'Source.lean',ROOT/'AHP/round10/shared/dictionary/R2_SourceDictionary.lean']
allowed={'propext','Classical.choice','Quot.sound'}
results=[]
for path in paths:
    source=path.read_text()
    log=Path(str(path)+'.log').read_text()
    exitpath=Path(str(path)+'.exit')
    code=int(exitpath.read_text())
    records=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.S)
    empty=re.findall(r"'([^']+)' does not depend on any axioms",log)
    recordmap={n:{x.strip() for x in a.split(',') if x.strip()} for n,a in records}
    recordmap.update({n:set() for n in empty})
    printed=re.findall(r'^#print axioms (\S+)\s*$',source,re.M)
    # Source.lean is a concatenation, so match short names against actual qualified log names.
    missing=[n for n in printed if not any(k==n or k.endswith('.'+n) for k in recordmap)]
    new_names=[]
    in_new=False
    for line in source.splitlines():
        if line.startswith('namespace AdalyFormal.Round10.Dictionary'): in_new=True
        if in_new:
            m=re.match(r'(?:(?:noncomputable )?(?:def|abbrev)|theorem) (\w+)',line)
            if m: new_names.append(m[1])
        if line.startswith('end AdalyFormal.Round10.Dictionary'): in_new=False
    unprinted=[n for n in new_names if not any(k.endswith('.'+n) and k.startswith('AdalyFormal.Round10.Dictionary.') for k in recordmap)]
    prohibited=re.findall(r'\b(?:sorry|admit|native_decide|unsafe|implemented_by|extern)\b|^\s*(?:axiom|opaque)\s+',source,re.M)
    bad={n:sorted(a-allowed) for n,a in recordmap.items() if not a<=allowed}
    diagnostics=[s for s in log.splitlines() if re.search(r'\b(?:error|warning)(?:\(|:)',s)]
    imports=re.findall(r'^import (.+)$',source,re.M)
    fresh=path.stat().st_mtime <= Path(str(path)+'.log').stat().st_mtime <= exitpath.stat().st_mtime
    ok=code==0 and not missing and not unprinted and not prohibited and not bad and not diagnostics and imports==['DrEquiv'] and fresh
    results.append(dict(path=str(path.relative_to(ROOT)),lines=len(source.splitlines()),sha256=hashlib.sha256(source.encode()).hexdigest(),exitCode=code,
      dependencyRecords=len(recordmap),dictionaryDeclarations=len(new_names),newDictionaryDeclarations=len([n for n in new_names if n != 'half_rotation_matrix']),unprintedNewDeclarations=unprinted,missingPrints=missing,
      nonstandardAxioms=bad,diagnostics=diagnostics,prohibitedTokens=prohibited,imports=imports,fresh=fresh,passAudit=ok))
manifest=json.loads((HERE/'COPIES.json').read_text())
copychecks=[]
for item in manifest:
    src=(ROOT/item['source']).read_text()
    if 'name' in item:
        m=re.search(r'^(?:(?:noncomputable )?(?:def|abbrev)|theorem) '+re.escape(item['name'])+r'\b',src,re.M)
        assert m
        nxt=re.search(r'\n(?:(?:noncomputable )?(?:def |abbrev )|theorem |open |end |namespace |#print |/[-!])',src[m.end():])
        e=m.end()+nxt.start()+1 if nxt else len(src)
        val=src[m.start():e].rstrip()+'\n'
    else:
        st=src.index('namespace AdalyFormal.Round2.Guarded.Pin')
        en=src.index('end AdalyFormal.Round2.Guarded.Pin')+len('end AdalyFormal.Round2.Guarded.Pin')
        val=src[st:en]+'\n'
    copychecks.append(hashlib.sha256(val.encode()).hexdigest()==item['sha256'] and val in (HERE/'Source.lean').read_text())
identical=(HERE/'Source.lean').read_bytes()==paths[-1].read_bytes()
result=dict(passAudit=all(r['passAudit'] for r in results) and all(copychecks) and identical,
  goalNeg2_proved=False,round9_coupling_premise_proved=False,actual_tridiagonal_source_identification_proved=False,
  actual_source_derivative_stencil_proved=True,actual_Hstar_source_neutral_proved=True,
  sourceCertificate_is_conditional=True,published_identical=identical,copied_fragments_verified=len(copychecks),results=results)
(HERE/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
raise SystemExit(0 if result['passAudit'] else 1)
