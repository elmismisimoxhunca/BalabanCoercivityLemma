#!/usr/bin/env python3
"""Assemble the round-9 analytic-r2 sources.
dev   : dev/Dev.lean = frozen-pin copy + dev-only definition copies + parts   (fast iteration)
final : Appendix.lean = parts;  Attempt.lean = round-1 Attempt.lean + Appendix.lean
full  : dev/Full.lean = the final Attempt.lean content (pre-flight compile; Attempt.lean untouched)
"""
import sys, os
here = os.path.dirname(os.path.abspath(__file__))
parts = sorted(f for f in os.listdir(os.path.join(here, 'parts')) if f.endswith('.lean'))
sel = [a for a in sys.argv[2:]]
if sel:
    parts = [p for p in parts if any(p.startswith(s) for s in sel)]
body = ''.join(open(os.path.join(here, 'parts', p)).read() + '\n' for p in parts)
mode = sys.argv[1] if len(sys.argv) > 1 else 'dev'
if mode == 'dev':
    head = ''.join(open(os.path.join(here, 'dev', h)).read() + '\n' for h in ['H0_pin.lean', 'H1_dil.lean', 'H2_r1defs.lean'])
    open(os.path.join(here, 'dev', 'Dev.lean'), 'w').write(head + body)
    print('dev/Dev.lean', len((head + body).splitlines()), 'lines', parts)
elif mode in ('final', 'full'):
    import re
    hdr = open(os.path.join(here, 'parts_header.lean')).read()
    fparts = sorted(f for f in os.listdir(os.path.join(here, 'final_parts')) if f.endswith('.lean'))
    body += ''.join(open(os.path.join(here, 'final_parts', p)).read() + '\n' for p in fparts)
    decls = re.findall(r'^(?:theorem|def|lemma|noncomputable def|noncomputable abbrev|abbrev)\s+(\S+)', body, re.M)
    ns = 'AdalyFormal.Round9.Guarded.AnalyticR2.'
    prints = ''.join('#print axioms ' + ns + d + '\n' for d in decls)
    app = hdr + body + '\n' + prints
    r1 = open(os.path.join(here, '..', 'analytic-r1', 'Attempt.lean')).read()
    if mode == 'full':
        # same content as the final Attempt.lean, written to dev/Full.lean (Attempt.lean untouched)
        open(os.path.join(here, 'dev', 'Full.lean'), 'w').write(r1 + app)
        print('dev/Full.lean', len((r1 + app).splitlines()), 'lines')
    else:
        open(os.path.join(here, 'Appendix.lean'), 'w').write(app)
        open(os.path.join(here, 'Attempt.lean'), 'w').write(r1 + app)
        print('Attempt.lean', len((r1 + app).splitlines()), 'lines')
