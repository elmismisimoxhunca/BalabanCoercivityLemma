"""Read-only proof/source audit; writes only the track's audit reports."""
from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parent
shared=Path('AHP/round13/shared/positivity')
allowed={'propext','Classical.choice','Quot.sound'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
report={'scope':'Builder plus separate publication-path executions, not independent review',
        'files':[],'copies':[],'directEarlierCopies':[],'newDeclarations':[]}
for stem in ['StarGeometry','P2']:
    local=root/f'{stem}.lean'
    pub=shared/f'R2_{stem}.lean'
    assert local.read_bytes()==pub.read_bytes(),stem
    for p in [local,pub]:
        source=p.read_text()
        log=Path(str(p)+'.log')
        text=log.read_text()
        ex=Path(str(p)+'.exit').read_text().strip()
        assert ex=='0',(str(p),ex)
        assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b',source),p
        assert not re.search(r'\b(?:error|warning)\b',text),p
        records=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S)
        independent=re.findall(r"'([^']+)' does not depend on any axioms",text)
        assert records
        for name,axes in records:
            assert {x.strip() for x in axes.split(',') if x.strip()}<=allowed,(name,axes)
        imports=re.findall(r'^import (.*)$',source,re.M)
        assert imports==['DrEquiv'],imports
        report['files'].append(dict(path=str(p.relative_to(Path.cwd())) if p.is_absolute() else str(p),
            lines=len(source.splitlines()),sourceSha256=sha(p),logSha256=sha(log),exitCode=int(ex),
            axiomRecords=len(records),axiomFreeRecords=len(independent),imports=imports))
for item in json.loads((root/'COPIES.json').read_text()):
    text=''.join(Path(item['source']).read_text().splitlines(True)[item['start']-1:item['end']])
    assert hashlib.sha256(text.encode()).hexdigest()==item['sha256'],item
    assert text in (root/'P2.lean').read_text(),item
    report['copies'].append(item|{'verbatim':True})
for file,start,end in [
    ('AHP/round12/shared/noncancel/R2_FullPlaquette.lean',1,453),
    ('AHP/round12/shared/noncancel/R2_Mass.lean',8,91),
    ('AHP/round12/shared/noncancel/R2_Boundary.lean',8,135),
    ('AHP/round12/shared/noncancel/R2_RightFamily.lean',8,693),
    ('AHP/round13/shared/detection/R1_FlatUnit.lean',230,1096),
]:
    text=''.join(Path(file).read_text().splitlines(True)[start-1:end])
    assert text in (root/'P2.lean').read_text(),file
    report['directEarlierCopies'].append(dict(source=file,start=start,end=end,
        sha256=hashlib.sha256(text.encode()).hexdigest(),verbatim=True))
for part in ['Geometry','Estimates','Arms','Sum','Join']:
    text=(root/f'{part}.lean.txt').read_text()
    names=re.findall(r'^(?:theorem|def)\s+(\w+)',text,re.M)
    log=(root/'P2.lean.log').read_text()
    for short in names:
        name='AdalyFormal.Round13.Positivity.Physical.'+short
        pattern=rf"'{re.escape(name)}' depends on axioms:\s*\[([^\]]*)\]"
        match=re.search(pattern,log,re.S)
        assert match,(part,name)
        axes=[x.strip() for x in match[1].split(',') if x.strip()]
        assert set(axes)<=allowed
        report['newDeclarations'].append(dict(name=name,part=part,axioms=axes))
# Verbatim P2 requested in round-12 GAPS, stripped only of indentation.
gaps=Path('AHP/round12/shared/GAPS.md').read_text()
wanted=gaps.split('-- Every physical field in the zero fiber of the central charged coordinate.\n')[1].split('\n\n-- Detection')[0]
actual=(root/'Join.lean.txt').read_text().split('theorem rightStar_P2 :\n')[1].split(' := by')[0]
normalize=lambda s:re.sub(r'\s+','',s)
assert normalize(wanted)==normalize(actual),(wanted,actual)
report['exactOriginalP2Statement']=True
report['mainDeclaration']='AdalyFormal.Round13.Positivity.Physical.rightStar_P2'
report['status']='P2 proved; no P3 or GoalNeg2 claim'
report['passed']=True
payload=json.dumps(report,indent=2)+'\n'
(root/'AUDIT.json').write_text(payload)
(shared/'R2_AUDIT.json').write_text(payload)
print(json.dumps({'passed':True,'compiles':len(report['files']),'verbatimCopies':len(report['copies']),
                  'directEarlierCopies':len(report['directEarlierCopies']),
                  'newDeclarations':len(report['newDeclarations']),'exactOriginalP2Statement':True},indent=2))
