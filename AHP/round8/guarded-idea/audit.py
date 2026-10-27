#!/usr/bin/env python3
"""Artifact audit for AHP/round8/guarded-idea/<file>.lean (default Attempt.lean).

Checks: verbatim pin prefix and verbatim round-5 IVT prefix; sole frozen
import; forbidden tokens in the raw source (comments included); wrapper exit 0
and source < log <= exit timestamps; no error lines in the log; every
dependency record (line-wrapped records re-joined) is a subset of
{propext, Classical.choice, Quot.sound}; every declaration of the new appendix
has its own record.  Writes CHECKS.json.  This audits artifacts; it proves
nothing mathematical.
"""
import hashlib, json, os, re, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
AHP = HERE.parents[1]
name = sys.argv[1] if len(sys.argv) > 1 else 'Attempt.lean'
src = HERE / name
log = HERE / (name + '.log')
ext = HERE / (name + '.exit')
pin = AHP / 'round3/guarded/pin/Statement.lean'
ivt = AHP / 'round5/guarded/ivt-r2/Attempt.lean'
app = HERE / 'Appendix.lean'

S = src.read_bytes()
checks = {}
checks['file'] = str(src.relative_to(AHP.parent))
checks['sha256'] = hashlib.sha256(S).hexdigest()
checks['pinVerbatimBytePrefix'] = S.startswith(pin.read_bytes())
checks['ivtR2VerbatimBytePrefix'] = S.startswith(ivt.read_bytes())
checks['equalsIvtR2PlusAppendix'] = S == ivt.read_bytes() + app.read_bytes()
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
# declarations of the new appendix
A = app.read_text()
ns = 'AdalyFormal.Round8.Guarded.SignFree.'
decls = re.findall(r'^(?:theorem|def|lemma|noncomputable def|abbrev)\s+(\S+)', A, re.M)
printed = {n for n, _ in recs} | set(noax)
missing = [d for d in decls if ns + d not in printed]
checks['appendixDeclarations'] = [ns + d for d in decls]
checks['appendixDeclarationsMissingRecord'] = missing
checks['appendixRecords'] = {n: a for n, a in recs if n.startswith(ns)}
checks['pass'] = (checks['pinVerbatimBytePrefix'] and checks['ivtR2VerbatimBytePrefix']
                  and checks['imports'] == ['DrEquiv'] and checks['forbiddenClean']
                  and checks['exitCode'] == 0 and not checks['errorLines']
                  and not bad and not checks['sorryAxInLog'] and not missing
                  and checks.get('timestampOrder', False))
out = HERE / ('CHECKS.json' if name == 'Attempt.lean' else 'CHECKS.' + name + '.json')
out.write_text(json.dumps(checks, indent=2) + '\n')
print(json.dumps({k: v for k, v in checks.items() if k not in ('appendixRecords', 'warningLines')}, indent=1))
print('warnings:', len(checks['warningLines']))
sys.exit(0 if checks['pass'] else 1)
