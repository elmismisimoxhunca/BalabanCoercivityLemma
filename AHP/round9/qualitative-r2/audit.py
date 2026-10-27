#!/usr/bin/env python3
"""Artifact audit for AHP/round9/qualitative-r2/<file>.lean (default Attempt.lean).

Structure checked (byte level):
  round-8 Attempt.lean (which starts with the round-3 pin and the round-5 ivt-r2 attempt)
  + round-9.1 qualitative Appendix.lean
  + Appendix.lean            (round 9.2 part 1; together with the above = history/Attempt.r2a.lean)
  + snap/AnalyticR1_Appendix.lean, snap/AnalyticR2_Appendix.lean   (analytic route, verbatim,
                                                                   sha256 in snap/SHA256SUMS)
  + Appendix2.lean           (round 9.2 part 2, namespace QualitativeR2Joint)
Also: sole frozen import DrEquiv; forbidden tokens in the raw source (comments included);
wrapper exit 0 and source <= log <= exit timestamps; no error or warning lines in the log; no
sorryAx; every dependency record (line wraps re-joined) is a subset of {propext,
Classical.choice, Quot.sound}; every declaration of Appendix.lean and Appendix2.lean has its own
record, with exactly these three axioms.  Writes CHECKS.json (or CHECKS.<file>.json).
This audits artifacts; it proves nothing mathematical.
"""
import hashlib
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
AHP = HERE.parents[1]
name = sys.argv[1] if len(sys.argv) > 1 else 'Attempt.lean'
src = HERE / name
log = HERE / (name + '.log')
ext = HERE / (name + '.exit')
pin = AHP / 'round3/guarded/pin/Statement.lean'
ivt = AHP / 'round5/guarded/ivt-r2/Attempt.lean'
r8 = AHP / 'round8/guarded-idea/Attempt.lean'
r91 = AHP / 'round9/qualitative-r1/Appendix.lean'
app1 = HERE / 'Appendix.lean'
r2a = HERE / 'history/Attempt.r2a.lean'
sa1 = HERE / 'snap/AnalyticR1_Appendix.lean'
sa2 = HERE / 'snap/AnalyticR2_Appendix.lean'
app2 = HERE / 'Appendix2.lean'
live_a1 = AHP / 'round9/analytic-r1/Appendix.lean'
live_a2 = AHP / 'round9/analytic-r2/Appendix.lean'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

S = src.read_bytes()
checks = {}
checks['file'] = str(src.relative_to(AHP.parent))
checks['sha256'] = hashlib.sha256(S).hexdigest()
checks['pinVerbatimBytePrefix'] = S.startswith(pin.read_bytes())
checks['ivtR2VerbatimBytePrefix'] = S.startswith(ivt.read_bytes())
checks['round8VerbatimBytePrefix'] = S.startswith(r8.read_bytes())
checks['round91AppendixFollowsRound8'] = S.startswith(r8.read_bytes() + r91.read_bytes())
checks['r2aEqualsRound8PlusR91PlusAppendix'] = (
    r2a.read_bytes() == r8.read_bytes() + r91.read_bytes() + app1.read_bytes())
checks['r2aBytePrefix'] = S.startswith(r2a.read_bytes())
sums = {}
for line in (HERE / 'snap/SHA256SUMS').read_text().splitlines():
    h, f = line.split()
    sums[f] = h
checks['snapAnalyticR1Sha256Recorded'] = sums.get('AnalyticR1_Appendix.lean') == sha(sa1)
checks['snapAnalyticR2Sha256Recorded'] = sums.get('AnalyticR2_Appendix.lean') == sha(sa2)
checks['snapAnalyticR1EqualsLiveRound9AnalyticR1'] = live_a1.exists() and sha(live_a1) == sha(sa1)
checks['snapAnalyticR2EqualsLiveRound9AnalyticR2 (informational)'] = (
    live_a2.exists() and sha(live_a2) == sha(sa2))
checks['equalsR2aPlusAnalyticSnapshotsPlusAppendix2'] = (
    S == r2a.read_bytes() + sa1.read_bytes() + sa2.read_bytes() + app2.read_bytes())
text = S.decode()
checks['imports'] = re.findall(r'^import\s+(\S+)', text, re.M)
forbidden = ['sorry', 'admit', 'native_decide', 'unsafe', 'implemented_by', 'extern', 'opaque']
hits = {w: len(re.findall(r'\b' + w + r'\b', text)) for w in forbidden}
hits['axiom-command'] = len(re.findall(r'^\s*axiom\b', text, re.M))
checks['forbiddenTokenHits'] = hits
checks['forbiddenClean'] = all(v == 0 for v in hits.values())
checks['exitCode'] = int(ext.read_text().strip()) if ext.exists() else None
if log.exists() and ext.exists():
    checks['timestampOrder'] = src.stat().st_mtime <= log.stat().st_mtime <= ext.stat().st_mtime + 1
L = log.read_text() if log.exists() else ''
checks['errorLines'] = [l for l in L.splitlines() if ': error' in l]
checks['warningLines'] = [l for l in L.splitlines() if ': warning' in l]
flat = re.sub(r'\s+', ' ', L)
recs = re.findall(r"'(.+?)' depends on axioms: \[([^\]]*)\]", flat)
noax = re.findall(r"'(.+?)' does not depend on any axioms", flat)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
bad = [(n, a) for n, a in recs if not set(x.strip() for x in a.split(',') if x.strip()) <= allowed]
checks['dependencyRecords'] = len(recs) + len(noax)
checks['badDependencyRecords'] = bad
checks['sorryAxInLog'] = 'sorryAx' in L
printed = {n for n, _ in recs} | set(noax)
recmap = dict(recs)
pat = r'^(?:theorem|def|lemma|noncomputable def|noncomputable abbrev|abbrev)\s+(\S+)'
own = []
for f, ns in ((app1, 'AdalyFormal.Round9.Guarded.QualitativeR2.'),
              (app2, 'AdalyFormal.Round9.Guarded.QualitativeR2Joint.')):
    own += [ns + d for d in re.findall(pat, f.read_text(), re.M)]
missing = [d for d in own if d not in printed]
checks['ownDeclarations'] = len(own)
checks['ownDeclarationsMissingRecord'] = missing
checks['ownRecordsExactlyStandard'] = all(
    d in recmap and set(x.strip() for x in recmap[d].split(',')) == allowed for d in own)
checks['appendix2Records'] = {d: recmap.get(d) for d in own
                              if d.startswith('AdalyFormal.Round9.Guarded.QualitativeR2Joint.')}
checks['pass'] = (checks['pinVerbatimBytePrefix'] and checks['ivtR2VerbatimBytePrefix']
                  and checks['round8VerbatimBytePrefix'] and checks['round91AppendixFollowsRound8']
                  and checks['r2aEqualsRound8PlusR91PlusAppendix'] and checks['r2aBytePrefix']
                  and checks['snapAnalyticR1Sha256Recorded'] and checks['snapAnalyticR2Sha256Recorded']
                  and checks['equalsR2aPlusAnalyticSnapshotsPlusAppendix2']
                  and checks['imports'] == ['DrEquiv'] and checks['forbiddenClean']
                  and checks['exitCode'] == 0 and not checks['errorLines']
                  and not checks['warningLines']
                  and not bad and not checks['sorryAxInLog'] and not missing
                  and checks['ownRecordsExactlyStandard']
                  and checks.get('timestampOrder', False))
out = HERE / ('CHECKS.json' if name == 'Attempt.lean' else 'CHECKS.' + name.replace('/', '_') + '.json')
out.write_text(json.dumps(checks, indent=2) + '\n')
print(json.dumps({k: v for k, v in checks.items()
                  if k not in ('appendix2Records', 'warningLines')}, indent=1))
sys.exit(0 if checks['pass'] else 1)
