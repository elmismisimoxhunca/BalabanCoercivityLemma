#!/usr/bin/env python3
"""Read-only proof/source audit; writes only this round's report."""
from pathlib import Path
import hashlib, json, re, sys
sys.dont_write_bytecode=True
import prune_goal as build
ROOT=build.ROOT; HERE=build.OUT
ALLOWED={'propext','Classical.choice','Quot.sound'}

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rel(p):return str(p.relative_to(ROOT))
def compilation(p):
    log=Path(str(p)+'.log'); exitfile=Path(str(p)+'.exit')
    assert exitfile.read_text().strip()=='0',p
    text=log.read_text()
    assert not re.search(r'\berror(?:\(|:)',text),p
    records=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text)
    free=re.findall(r"'([^']+)' does not depend on any axioms",text)
    assert records or free,p
    for n,axs in records:
        assert set(x.strip() for x in axs.split(',') if x.strip()) <= ALLOWED,(p,n,axs)
    code=build.mask(p.read_text())
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b',code),p
    imports=re.findall(r'^import (\S+)',code,re.M)
    assert all((ROOT/'lean/src'/Path(i.replace('.','/')).with_suffix('.lean')).exists() for i in imports),(p,imports)
    return dict(source=rel(p),source_sha256=sha(p),log_sha256=sha(log),exit=0,imports=imports,
                records=[dict(name=n,axioms=[x.strip() for x in axs.split(',') if x.strip()]) for n,axs in records],
                axiom_free=free,warnings=len(re.findall(r': warning:',text)))

local=HERE/'P2Goal.lean'; shared=ROOT/'AHP/round13/shared/assembly/R2_P2Goal.lean'
assert local.read_bytes()==shared.read_bytes()
compiles=[compilation(p) for p in [local,shared,HERE/'PhysicalGoal.lean',ROOT/'AHP/round13/shared/assembly/R2_PhysicalGoal.lean',HERE/'GoalBridge.lean',ROOT/'AHP/round13/assembly/r1/RepairedJoin.lean']]
for p in [local,shared]:
    printed=re.sub(r'\s+',' ',Path(str(p)+'.log').read_text())
    for exact in [
      'AdalyFormal.Round13.Assembly.R2.goalNeg2_of_P2_P3 : AdalyFormal.Round13.Assembly.R1.P2 → AdalyFormal.Round13.Assembly.R1.P3 → AdalyFormal.Round2.Guarded.Pin.GoalNeg2',
      'AdalyFormal.Round13.Assembly.R2.goalNeg2_of_cofinalP2P3 : AdalyFormal.Round13.Assembly.R1.CofinalP2P3 → AdalyFormal.Round2.Guarded.Pin.GoalNeg2',
      'AdalyFormal.Round13.Assembly.R2.goalNeg2_of_P3 : AdalyFormal.Round13.Assembly.R1.P3 → AdalyFormal.Round2.Guarded.Pin.GoalNeg2',
      'AdalyFormal.Round13.Assembly.R2.goalNeg2_of_cofinalP3 : AdalyFormal.Round13.Assembly.R2.CofinalP3 → AdalyFormal.Round2.Guarded.Pin.GoalNeg2',
      '@AdalyFormal.Round13.Assembly.R2.p2 : AdalyFormal.Round13.Assembly.R1.P2',
      '@AdalyFormal.Round13.Assembly.R2.rightStar_kernelLine : ∀ {q R : ℕ} (hq : 0 < q), 2 ∣ R → 18 ≤ R →']: 
        assert exact in printed,(p,exact)
# Audit every verbatim selected declaration chunk against its source snapshot.
manifest=json.loads((HERE/'P2Goal_COPIES.json').read_text())
source=local.read_text()
for c in manifest:
    lines=(ROOT/c['source']).read_text().splitlines(keepends=True)
    body=''.join(lines[c['first']-1:c['last']])
    assert hashlib.sha256(body.encode()).hexdigest()==c['sha256'],c
    assert body in source,c

# Reconstruct the authorized historical repair, without rerunning its compile or modifying R1.
old=(ROOT/'AHP/round10/assembly/r4/Attempt.lean').read_text()
d=(ROOT/'AHP/round10/shared/dictionary/R4_ColorResponse.lean').read_text()
header=d[d.index('namespace AdalyFormal.Round10.Dictionary.FreeSource\n'):d.index('theorem circulation_congr_boundary')]
helpers=[]
for start,stop in [('theorem phase_axis_fixed','theorem sourceLinear_U1'),('theorem half_twice','/-- Actual carrier Q intertwines')]:
    a=d.index(start);helpers.append(d[a:d.index(stop,a)])
insert=header+'\n'.join(helpers)+'\n#print axioms phase_axis_fixed\n#print axioms half_twice\n#print axioms half_average\nend AdalyFormal.Round10.Dictionary.FreeSource\n\n'
repair=(ROOT/'AHP/round13/assembly/r1/RepairedJoin.lean').read_text()
assert old.replace('noncomputable section\nnamespace AdalyFormal.Round10.Dictionary.Color\n',insert+'noncomputable section\nnamespace AdalyFormal.Round10.Dictionary.Color\n')==repair

# Same original pin and exact P1/P2/P3, checked by declaration bodies (not text labels).
def decls(p):return {c['full']:c for c in build.parse(p) if c['full']}
main=decls(local); pin=decls(ROOT/'AHP/round3/guarded/pin/Statement.lean')
spine=decls(ROOT/'AHP/round13/shared/assembly/R1_P1Spine.lean')
interfaces=[]
for n in ['PlaqSel','selIn','selAll','dataS','P428Target8SG','GoalPos2','GoalNeg2']:
    f='AdalyFormal.Round2.Guarded.Pin.'+n
    assert main[f]['raw']==pin[f]['raw'],f
    interfaces.append(f)
for n in ['P1','P2','P3','CofinalP2P3','cofinalNoCancellation_of_cofinalP2P3']:
    f='AdalyFormal.Round13.Assembly.R1.'+n
    assert main[f]['raw']==spine[f]['raw'],f
    interfaces.append(f)
for f in ['AdalyFormal.Round9.Guarded.Qualitative.vacA','AdalyFormal.Round9.Guarded.QualitativeR2.vacEdge',
          'AdalyFormal.Round10.Assembly.R2.KernelLine','AdalyFormal.Round10.Dictionary.FreeSource.CurlDetected',
          'AdalyFormal.Round10.Assembly.R4.NoResponseCancellation','AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation']:
    assert main[f]['raw']==spine[f]['raw'],f
    interfaces.append(f)
# Nonidentical deduplicated chunks differ only in comments/scoped Classical opening.
all_sources={p:decls(ROOT/p) for p in ['AHP/round13/assembly/r1/RepairedJoin.lean','AHP/round13/shared/assembly/R1_P1Spine.lean','AHP/round13/shared/positivity/R2_P2.lean']}
for c in json.loads((HERE/'P2Goal_DEDUP.json').read_text()):
    if not c['identical']:
        a,b=(all_sources[p][c['name']]['raw'] for p in [c['kept'],c['skipped']])
        norm=lambda t: re.sub(r'\s+','',build.mask(t).replace('open Classical in',''))
        assert norm(a)==norm(b),c

# Read-only sibling publication checks; do not treat builder executions as independent review.
siblings=[]
for track in ['trial','positivity','detection']:
    for p in sorted((ROOT/f'AHP/round13/shared/{track}').glob('R[12]_*.lean')):
        if Path(str(p)+'.exit').exists() and Path(str(p)+'.exit').read_text().strip()=='0':
            siblings.append(compilation(p))
report=dict(status='PASS',claim='Unconditional whole KernelLine and real nullity two; conditional exact GoalNeg2 with P3 only',
            compiles=compiles,verbatim_chunks=len(manifest),interfaces=interfaces,
            original_repair_rechecked=True,publication_byte_identical=True,
            sibling_publications=siblings,new_main_declarations=[
              'AdalyFormal.Round13.Assembly.R2.rightStar_kernelLine',
              'AdalyFormal.Round13.Assembly.R2.cofinal_rightStar_kernelLine',
              'AdalyFormal.Round13.Assembly.R2.goalNeg2_of_P3',
              'AdalyFormal.Round13.Assembly.R2.goalNeg2_of_cofinalP3'])
(HERE/'AUDIT.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS:',len(manifest),'verbatim declarations;',len(interfaces),'exact interfaces;',len(siblings),'sibling publications;',len(compiles),'clean compilation artifacts')
