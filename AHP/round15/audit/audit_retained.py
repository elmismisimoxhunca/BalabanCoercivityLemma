#!/usr/bin/env python3
"""Read-only source/log audit after workflow timeout; does NOT run Lean.
Writes only the report JSON named with --output. No stored exit marker is
trusted independently of the source/log, complete axiom records and errors.
"""
import argparse
import datetime
import hashlib
import json
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[3]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
RECORD = re.compile(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", re.S)
START = re.compile(r"'[^']+' (?:depends on axioms:|does not depend on any axioms)")
FORBIDDEN = re.compile(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b')


def mask_comments_strings(text):
    # Preserve newlines/positions. Lean block comments nest; strings have escapes.
    chars = list(text)
    i = depth = 0
    line_comment = string = False
    while i < len(text):
        c = text[i]
        if line_comment:
            if c == '\n':
                line_comment = False
            else:
                chars[i] = ' '
            i += 1
        elif depth:
            if text.startswith('/-', i):
                chars[i:i+2] = '  '
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                chars[i:i+2] = '  '
                depth -= 1
                i += 2
            else:
                if c != '\n': chars[i] = ' '
                i += 1
        elif string:
            if c == '\\' and i + 1 < len(text):
                chars[i:i+2] = '  '
                i += 2
            else:
                if c == '"': string = False
                if c != '\n': chars[i] = ' '
                i += 1
        elif text.startswith('--', i):
            chars[i:i+2] = '  '
            line_comment = True
            i += 2
        elif text.startswith('/-', i):
            chars[i:i+2] = '  '
            depth = 1
            i += 2
        elif c == '"':
            chars[i] = ' '
            string = True
            i += 1
        else:
            i += 1
    return ''.join(chars)


def file_meta(p):
    if not p.exists(): return None
    b = p.read_bytes()
    return {'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest(),
            'mtime_utc': datetime.datetime.fromtimestamp(p.stat().st_mtime, datetime.timezone.utc).isoformat()}


def audit(relative):
    p = ROOT / relative
    logp, exitp = pathlib.Path(str(p)+'.log'), pathlib.Path(str(p)+'.exit')
    source = p.read_text()
    code = mask_comments_strings(source)
    log = logp.read_text() if logp.exists() else ''
    exit_text = exitp.read_text().strip() if exitp.exists() else None
    bad_tokens = [{'token':m[0], 'line':code.count('\n', 0, m.start())+1} for m in FORBIDDEN.finditer(code)]
    errors = [{'line':i, 'text':ln} for i,ln in enumerate(log.splitlines(),1) if re.search(r'\berror:',ln)]
    records = []
    for m in RECORD.finditer(log):
        ax = set(filter(None, re.split(r'\s*,\s*', (m[2] or '').strip())))
        name = m[1]
        short = name.split('.')[-1]
        declarations = list(re.finditer(r'(?m)\b(def|theorem|lemma|structure|abbrev)\s+(?:_root_\.)?'+re.escape(short)+r'(?=\s|:|\{|\()', code))
        positions = [{'line':code.count('\n',0,d.start())+1,'kind':d[1]} for d in declarations]
        records.append({'name':name, 'axioms':sorted(ax), 'allowed':ax <= ALLOWED,
                        'log_line':log.count('\n',0,m.start())+1, 'record':' '.join(m[0].split()),
                        'source_declarations':positions})
    starts = len(list(START.finditer(log)))
    clean = exit_text == '0' and not errors and not bad_tokens and bool(records) and len(records)==starts and all(r['allowed'] for r in records)
    stale = logp.exists() and exitp.exists() and (p.stat().st_mtime > exitp.stat().st_mtime or logp.stat().st_mtime > exitp.stat().st_mtime)
    # Assembly R2 was restored to its previously compiled byte-identical source.
    restored = relative.endswith('assembly/r2/AreaGoal.lean') and file_meta(p)['sha256']=='a6d141eb46842741e72e9b8dd758fa1203c0dfa53c6b07a64ef6d86bf1ced5dc'
    attested_regeneration = False
    if relative in ['AHP/round15/seed/r2/Leading.lean', 'AHP/round15/shared/seed/R2_Leading.lean']:
        manifest = json.loads((ROOT/'AHP/round15/seed/r2/AUDIT.json').read_text())
        base = (ROOT/'AHP/round15/seed/r1/Seed.lean').read_text()
        fragment = (ROOT/'AHP/round15/seed/r2/R2Declarations.lean').read_text()
        attested_regeneration = (manifest['source_sha256'] == file_meta(p)['sha256']
            and manifest['log_sha256'] == file_meta(logp)['sha256']
            and source == base.rstrip()+'\n'+fragment)
    status = 'B: retained builder compilation, not independently replayed' if clean and (not stale or restored or attested_regeneration) else 'C: not accepted from retained evidence'
    r15 = [r for r in records if '.Round15.' in r['name'] or (relative.endswith('/KData.lean') and r['name'].startswith('q1'))]
    return {'source':relative, 'source_meta':file_meta(p), 'log_meta':file_meta(logp), 'exit_meta':file_meta(exitp),
            'exit_text':exit_text, 'stale_exit_marker':stale, 'restored_source_hash_exception':restored,
            'builder_manifest_attests_regenerated_source_and_log':attested_regeneration,
            'status':status, 'errors':errors, 'forbidden_code_tokens':bad_tokens,
            'axiom_record_starts':starts, 'complete_axiom_records':len(records),
            'nonstandard_axiom_records':[r for r in records if not r['allowed']],
            'round15_records':r15}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--output',required=True)
    ap.add_argument('--workflow-history',required=True)
    args=ap.parse_args()
    paths = [
        'AHP/round15/dictionary/r1/Collar.lean',
        'AHP/round15/dictionary/r1/PhysicalGap.lean',
        'AHP/round15/seed/r1/Seed.lean',
        'AHP/round15/seed/r2/Leading.lean',
        'AHP/round15/assembly/r1/AreaGoal.lean',
        'AHP/round15/assembly/r2/AreaGoal.lean',
        'AHP/round15/dictionary/r2/KData.lean',
        'AHP/round15/dictionary/r2/DeepCollar.lean',
        'AHP/round15/dictionary/r2/Transport.lean',
        'AHP/round15/dictionary/r2/Support.lean',
        'AHP/round15/dictionary/r2/Stencil.lean',
    ]
    files=[audit(p) for p in paths]
    publications=[]
    pairs=[('dictionary/r1/Collar.lean','dictionary/R1_Collar.lean'),
           ('dictionary/r1/PhysicalGap.lean','dictionary/R1_PhysicalGap.lean'),
           ('seed/r1/Seed.lean','seed/R1_Seed.lean'),('seed/r2/Leading.lean','seed/R2_Leading.lean'),
           ('assembly/r1/AreaGoal.lean','assembly/R1_AreaGoal.lean'),('assembly/r2/AreaGoal.lean','assembly/R2_AreaGoal.lean')]
    for local,shared in pairs:
        a,b=ROOT/'AHP/round15'/local,ROOT/'AHP/round15/shared'/shared
        publications.append({'local':str(a.relative_to(ROOT)), 'shared':str(b.relative_to(ROOT)),
                             'sources_identical':a.read_bytes()==b.read_bytes(),
                             'shared_audit':audit(str(b.relative_to(ROOT)))})
    history=[json.loads(ln) for ln in pathlib.Path(args.workflow_history).read_text().splitlines()]
    run=next(r for r in history if r['type']=='run')
    calls=[{k:c.get(k) for k in ['callIndex','label','status','childThreadId','error','resultAvailable']} for c in history if c['type']=='call']
    accepted={r['name']:r for f in files if f['status'].startswith('B:') for r in f['round15_records']}
    data={'scope':'Static audit of retained sources, logs and exit files; no Lean compilation or numerical solve. B does not mean independent verification. Numerical evidence does not close a proposition.',
          'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'workflow':{k:run.get(k) for k in ['id','status','error','phase','startedAt','finishedAt']},
          'calls':calls,'files':files,'publications':publications,
          'unique_round15_names_with_retained_builder_axiom_evidence':len(accepted),
          'accepted_names':sorted(accepted),
          'physical_seed_proved':False,'P3_proved':False,'GoalNeg2_proved':False}
    out=pathlib.Path(args.output)
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(data,indent=2)+'\n')
    print('Wrote',out)
    for f in files:
        print(f['status'].split(':')[0], f['source'], 'records',f['complete_axiom_records'],'R15',len(f['round15_records']),'errors',len(f['errors']),'stale',f['stale_exit_marker'])
    print('Unique R15 names with retained builder evidence:',len(accepted))
    print('Publication sources identical:',all(x['sources_identical'] for x in publications))
    assert all(x['sources_identical'] for x in publications)
    assert not any(f['nonstandard_axiom_records'] for f in files if f['status'].startswith('B:'))
    assert next(f for f in files if f['source'].endswith('/Stencil.lean'))['status'].startswith('C:')

if __name__=='__main__': main()
