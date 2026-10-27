#!/usr/bin/env python3
"""Read-only certificate audit except own JSON report; no compiler or numerical solve."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[4]
OUT=Path(__file__).resolve().parent
SH=ROOT/'AHP/round13/shared/detection'
allowed={'propext','Classical.choice','Quot.sound'}
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def lean_code(text):
    # Strip nested block comments and line comments; no strings in the new bodies.
    out=[]; i=0; depth=0
    while i<len(text):
        if text[i:i+2]=='/-': depth+=1; i+=2
        elif depth and text[i:i+2]=='-/': depth-=1; i+=2
        elif depth: i+=1
        elif text[i:i+2]=='--':
            j=text.find('\n',i); i=len(text) if j<0 else j
        else: out.append(text[i]); i+=1
    assert depth==0
    return ''.join(out)
reports=[]
for stem in ['Area','ColorArea','PhysicalArea']:
    for p in [OUT/f'{stem}.lean',SH/f'R2_{stem}.lean']:
        source=p.read_text(); log=Path(str(p)+'.log'); ex=Path(str(p)+'.exit')
        assert ex.read_text().strip()=='0',str(ex)
        text=log.read_text()
        assert not re.search(r'\berror(?:\([^\n]*\))?:',text),str(log)
        records=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text,re.S)
        records += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",text)]
        assert records,str(log)
        for n,axioms in records:
            assert set(filter(None,re.split(r'[\s,]+',axioms)))<=allowed,(n,axioms)
        code=lean_code(source)
        bad=re.findall(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b',code)
        assert not bad,(p,bad)
        imports=re.findall(r'^import (.+)$',code,re.M)
        assert imports and all((ROOT/'lean/src'/f'{module}.lean').is_file()
                               for module in imports),(p,imports)
        assert set(imports)<= {'DrEquiv','ZXR2Flat6'},(p,imports)
        own={n:sorted(set(filter(None,re.split(r'[\s,]+',a)))) for n,a in records
             if n.startswith(('AdalyFormal.Round13.Detection.Area.',
                              'AdalyFormal.Round13.Detection.ColorArea.',
                              'AdalyFormal.Round13.Detection.PhysicalArea.'))}
        reports.append({'file':str(p.relative_to(ROOT)),'sourceSha256':digest(p),
                        'logSha256':digest(log),'exit':0,'lines':len(source.splitlines()),
                        'records':len(records),'newRecords':own,
                        'warnings':len(re.findall(r'\bwarning:',text)),
                        'forbiddenTokens':bad,'imports':imports})
    assert (OUT/f'{stem}.lean').read_bytes()==(SH/f'R2_{stem}.lean').read_bytes(),stem
copy_reports=[]
for row in json.loads((OUT/'COPIES.json').read_text()):
    piece=(ROOT/row['source']).read_text()[row['start']:row['end']]
    assert hashlib.sha256(piece.encode()).hexdigest()==row['sha256'],row
    consumers=[r['file'] for r in reports if piece in (ROOT/r['file']).read_text()]
    assert consumers,row
    copy_reports.append({**row,'verbatimIn':consumers})
new_declarations=[]
for file,ns in [('Area.lean','Area'),('ColorAreaAppendix.lean.txt','ColorArea'),
                ('PhysicalAreaAppendix.lean.txt','PhysicalArea')]:
    code=lean_code((OUT/file).read_text())
    for kind,n in re.findall(r'^(?:@\[[^\]]*\]\s+)?(def|theorem|lemma)\s+([^\s({:]+)',code,re.M):
        fq='AdalyFormal.Round13.Detection.'+ns+'.'+n
        assert any(fq in r['newRecords'] for r in reports),fq
        new_declarations.append(fq)
result={'status':'pass','closedGoal':'none; P3 and GoalNeg2 remain open',
        'compilations':reports,'verbatimCopies':copy_reports,
        'newDeclarationCount':len(new_declarations),'newDeclarations':new_declarations,
        'publicationByteIdentity':True,
        'qualification':'Builder and publication executions, not independent review. Exact operator identities and conditional handoff only; no nonvanishing, cofinal kernel/curl family, or GoalNeg2 inhabitant.'}
(OUT/'AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
(SH/'R2_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'pass','compiles':len(reports),'copies':len(copy_reports),
                  'newDeclarations':len(new_declarations),
                  'records':[r['records'] for r in reports],
                  'warnings':[r['warnings'] for r in reports]}))
