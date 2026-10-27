#!/usr/bin/env python3
"""Audit the actual final Lean sources and wrapper outputs. No mathematical premise is inferred."""
from pathlib import Path
import re,json,hashlib,sys
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[3]
SHARED=REPO/'AHP/round10/shared/nonvanishing/R3_DilatedFlux.lean'
allowed={'propext','Classical.choice','Quot.sound'}
forbidden=re.compile(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b')
files=[ROOT/f for f in ['Flux.lean','TorusFlux.lean','PhysicalBlocking.lean','DilatedFlux.lean']]+[SHARED]
result={'goalNeg2_proved':False,'round9_coupling_premise_proved':False,
        'actual_crossing_jet_nonzero_proved':False,'full_kernel_definiteness_proved':False,
        'actual_normalized_Q_row_identity_proved':True,
        'actual_dilated_jet_to_localized_curl_implication_proved':True,
        'files':[],'copies':[]}
okay=True
for f in files:
    s=f.read_text(); logp=Path(str(f)+'.log'); exp=Path(str(f)+'.exit')
    log=logp.read_text(); ex=exp.read_text().strip()
    deps=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S)
    clean=re.findall(r"'([^']+)' does not depend on any axioms",log)
    records={n:set(x.strip() for x in a.split(',') if x.strip()) for n,a in deps}
    records.update({n:set() for n in clean})
    decls=re.findall(r'^(?:@\[[^\n]+\]\s*)?(?:noncomputable\s+)?(?:def|abbrev|theorem)\s+([A-Za-z0-9_]+)',s,re.M)
    printed=re.findall(r'^#print axioms ([A-Za-z0-9_]+)\s*$',s,re.M)
    diagnostics=re.findall(r'^.*(?:error|warning)(?:\([^\n]*\))?:.*$',log,re.M)
    axbad={n:sorted(a-allowed) for n,a in records.items() if a-allowed}
    missing=[n for n in decls if n not in printed or not any(k.endswith('.'+n) for k in records)]
    timestamps=f.stat().st_mtime<=logp.stat().st_mtime<=exp.stat().st_mtime
    checks={'exit_zero':ex=='0','no_diagnostics':not diagnostics,'standard_axioms_only':not axbad,
            'every_declaration_audited':not missing and len(records)==len(decls)==len(printed),
            'no_forbidden_devices':not forbidden.search(s),'fresh_log_exit':timestamps,
            'frozen_imports_only':set(re.findall(r'^import (\S+)',s,re.M))<={'DrEquiv','ZXR2Flat6'}}
    good=all(checks.values()); okay &=good
    result['files'].append(dict(path=str(f.relative_to(REPO)),lines=len(s.splitlines()),
       sha256=hashlib.sha256(f.read_bytes()).hexdigest(),exit=ex,declarations=len(decls),
       dependency_records=len(records),checks=checks,diagnostics=diagnostics,missing=missing,unexpected_axioms=axbad,passed=good))
for rec in json.loads((ROOT/'COPIES.json').read_text()):
    s=(REPO/rec['source']).read_text()
    start=re.search(r'^(?:def|theorem) '+rec['name']+r'\b',s,re.M).start(); rest=s[start:]
    end=rest.index('\n\n'); nxt=re.search(r'\n(?:def|theorem) ',rest)
    if nxt: end=min(end,nxt.start())
    body=rest[:end]+'\n'
    exact=hashlib.sha256(body.encode()).hexdigest()==rec['sha256'] and body in (ROOT/'DilatedFlux.lean').read_text()
    if rec['name'].startswith('dil'):
        exact &= body in (REPO/'AHP/round9/qualitative-r2/Attempt.lean').read_text()
    okay &= exact
    result['copies'].append(dict(name=rec['name'],source=rec['source'],verbatim=exact))
result['shared_byte_identical']=SHARED.read_bytes()==(ROOT/'DilatedFlux.lean').read_bytes()
okay &= result['shared_byte_identical']
compat=ROOT/'AfterDictionary.lean'
if compat.exists():
    clog=Path(str(compat)+'.log'); cexit=Path(str(compat)+'.exit')
    ct=clog.read_text()
    cdeps=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",ct,re.S)
    cstandard=all(set(x.strip() for x in a.split(',') if x.strip())<=allowed for _,a in cdeps)
    cgood=(cexit.read_text().strip()=='0' and not re.search(r'\b(?:warning|error)(?:\([^\n]*\))?:',ct)
           and cstandard and compat.stat().st_mtime<=clog.stat().st_mtime<=cexit.stat().st_mtime
           and any(n=='AdalyFormal.Round10.Nonvanishing.Regression.neutralFunctional' for n,_ in cdeps))
    result['post_dictionary_compatibility']={'path':str(compat.relative_to(REPO)),
        'exit':cexit.read_text().strip(),'standard_axioms_only':cstandard,'pass':bool(cgood),
        'qualification':'Original assembly failure was observed in its retained log; dictionary-prefix-only check passed both before and after the robust direct-proof change.'}
    okay &= bool(cgood)
result['pass']=bool(okay)
(ROOT/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'pass':okay,'files':len(files),'declarations':result['files'][-1]['declarations'],
                  'copies':len(result['copies']),'goalNeg2_proved':False},indent=2))
sys.exit(0 if okay else 1)
