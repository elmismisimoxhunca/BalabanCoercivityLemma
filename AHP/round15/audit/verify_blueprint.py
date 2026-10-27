#!/usr/bin/env python3
"""Focused parent audit of round-15 documentation, not a Lean/TeX build."""
import collections
import datetime
import hashlib
import json
import pathlib
import re

from audit_retained import ROOT, RECORD, mask_comments_strings


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def declaration_positions(path):
    """Resolve names in these sources' explicit namespace/section blocks.

    This is a documentation cross-check, not a Lean parser or elaborator.
    """
    text=mask_comments_strings(path.read_text())
    stack=[]
    found={}
    ns=[]
    for i,line in enumerate(text.splitlines(),1):
        s=line.strip()
        m=re.match(r'namespace\s+([^\s]+)',s)
        if m:
            stack.append(('namespace',list(ns)))
            name=m[1]
            ns=name[len('_root_.'):].split('.') if name.startswith('_root_.') else ns+name.split('.')
            continue
        if re.match(r'(?:noncomputable\s+)?section(?:\s|$)',s):
            stack.append(('section',list(ns)))
            continue
        if re.match(r'end(?:\s|$)',s):
            assert stack,(str(path),i,s)
            _,ns=stack.pop()
            continue
        m=re.search(r'\b(def|theorem|lemma|structure|abbrev)\s+([^\s({:\[]+)',s)
        if not m: continue
        # Only declaration commands, not words inside a theorem's tactic body.
        before=s[:m.start()]
        if before and not re.fullmatch(r'(?:(?:private|protected|noncomputable)\s+|@\[[^\]]*\]\s*)*',before):
            continue
        name=m[2]
        full=name[len('_root_.'):] if name.startswith('_root_.') else '.'.join(ns+[name])
        found[i]=(full,m[1])
    return found


def main():
    manifest=json.loads((ROOT/'AHP/round15/audit/TIMEOUT_AUDIT.json').read_text())
    mdpath=ROOT/'AHP/round15/BLUEPRINT.md'
    texpath=ROOT/'AHP/round15/blueprint/content.tex'
    oldmd=(ROOT/'AHP/round14/BLUEPRINT.md').read_bytes()
    oldtex=(ROOT/'AHP/round14/blueprint/content.tex').read_bytes()
    mdb=mdpath.read_bytes(); texb=texpath.read_bytes()
    assert mdb.endswith(oldmd) and texb.endswith(oldtex), 'Inherited checkpoints changed'
    md=mdb[:-len(oldmd)].decode(); tex=texb[:-len(oldtex)].decode()
    allmd=mdb.decode(); alltex=texb.decode()
    for f in manifest['files']:
        assert digest(ROOT/f['source'])==f['source_meta']['sha256'],f['source']
        for suffix,key in [('.log','log_meta'),('.exit','exit_meta')]:
            if f[key]: assert digest(ROOT/(f['source']+suffix))==f[key]['sha256'],f['source']+suffix
    entries={f['source']:f for f in manifest['files']}
    maps={p:declaration_positions(ROOT/p) for p,f in entries.items() if f['status'].startswith('B:')}
    mdblocks={}
    for block in re.split(r'(?m)(?=^<a id="r15-)',md)[1:]:
        label=re.match(r'<a id="([^"]+)"></a>',block)[1]
        assert label not in mdblocks,label
        mdblocks[label]=block
    texblocks={}
    for m in re.finditer(r'\\begin\{(definition|theorem)\}\[(r15-[^\]]+)\](.*?)\\end\{\1\}',tex,re.S):
        assert m[2] not in texblocks,m[2]
        texblocks[m[2]]=(m[1],m[3])
    assert set(mdblocks)==set(texblocks) and len(mdblocks)==119
    names=[]; kinds=collections.Counter(); statuses=collections.Counter(); secondary_count=0
    for label,block in mdblocks.items():
        status=re.search(r'\*\*Status:\*\* ([A-Z])',block)[1]
        statuses[status]+=1
        kind,tblock=texblocks[label]
        assert re.search(r'\\par Status: '+status+r':',tblock),label
        markers=len(re.findall(r'(?m)^\\leanok\s*$',tblock))
        assert markers==(1 if status=='B' else 0),(label,status,markers)
        if status!='B': continue
        name=re.search(r'^#### '+re.escape(label)+r' — `([^`]+)`',block,re.M)[1]
        names.append(name)
        assert '\\lean{'+name+'}' in tblock,label
        path,line=re.search(r'\*\*Source:\*\* `([^`]+\.lean):(\d+)`',block).groups()
        line=int(line)
        assert entries[path]['status'].startswith('B:'),label
        resolved,src_kind=maps[path][line]
        assert resolved==name,(label,name,resolved,path,line)
        assert kind==('theorem' if src_kind in ('theorem','lemma') else 'definition'),label
        kinds[kind]+=1
        assert path+':'+str(line) in tblock,label
        logpath,logline,printed=re.search(r'\*\*Axioms:\*\* `([^`]+):(\d+)`: `([^`]+)`',block).groups()
        candidates=[r for r in entries[path]['round15_records'] if r['name']==name and r['log_line']==int(logline)]
        assert candidates and candidates[0]['record']==printed,(label,'manifest axiom mismatch')
        assert printed in tblock and logpath+':'+logline in tblock,label
        actual=(ROOT/logpath).read_text()
        records={actual.count('\n',0,m.start())+1:' '.join(m[0].split()) for m in RECORD.finditer(actual)}
        assert records[int(logline)]==printed,(label,'actual log mismatch')
        # Validate every secondary location with namespace qualification, not short-name matching.
        for p,ln,lp,ll in re.findall(r'`([^`]+\.lean):(\d+); log ([^`]+\.log):(\d+)`',block):
            assert maps[p][int(ln)][0]==name,(label,p,ln,maps[p][int(ln)])
            recs=entries[p]['round15_records']
            assert any(r['name']==name and r['log_line']==int(ll) for r in recs),(label,p,ll)
            assert f'{p}:{ln}; log {lp}:{ll}' in tblock,label
            secondary_count+=1
    assert len(names)==len(set(names))==101
    assert set(names)==set(manifest['accepted_names'])
    assert dict(kinds)=={'definition':39,'theorem':62},kinds
    assert dict(statuses)=={'B':101,'O':8,'N':5,'C':4,'U':1},statuses
    labels=re.findall(r'\\label\{([^}]+)\}',alltex)
    assert len(labels)==len(set(labels)),'Duplicate full TeX label'
    labelset=set(labels)
    refs=re.findall(r'\\ref\{([^}]+)\}',tex)
    for uses in re.findall(r'\\uses\{([^}]*)\}',tex):
        refs.extend(x.strip() for x in uses.split(',') if x.strip())
    assert set(refs)<=labelset,sorted(set(refs)-labelset)
    anchors=re.findall(r'<a id="([^"]+)"></a>',allmd)
    assert len(anchors)==len(set(anchors)),'Duplicate Markdown anchor'
    mdrefs=re.findall(r'\]\(#([^)]*)\)',md)
    assert set(mdrefs)<=set(anchors),sorted(set(mdrefs)-set(anchors))
    # Balanced literal environment delimiters in the newly authored fragment.
    stack=[]
    for m in re.finditer(r'\\(begin|end)\{([^}]+)\}',tex):
        if m[1]=='begin': stack.append(m[2])
        else:
            assert stack and stack.pop()==m[2],('Unbalanced environment',m[0])
    assert not stack
    assert 'conjectured false' in md and 'conjectured false' in tex
    assert 'No unconditional closure was obtained' in md and 'No unconditional closure was obtained' in tex
    result={
        'status':'pass',
        'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'scope':'Parent static documentation/source/log cross-check; not Lean/TeX compilation, a new independent proof replay, or a full dependency-DAG audit.',
        'new_nodes':119,'status_counts':dict(statuses),'accepted_kinds':dict(kinds),
        'canonical_source_and_axiom_citations_checked':101,
        'secondary_qualified_source_citations_checked':secondary_count,
        'inherited_markdown_byte_identical':True,'inherited_tex_byte_identical':True,
        'audited_lean_sources_and_logs_unchanged':True,
        'unique_labels_and_resolved_references':True,'new_tex_environments_balanced':True,
        'proof_markers_only_for_B':True,
        'corrections':['Removed an unrelated PhaseSource.phase line 461 from the secondary citation for Round15.Dictionary.phase; correct line is 5379.',
                       'Clarified that collarTestLeadingConstant names a theorem about chargedArea, not a real-valued constant.',
                       'Replaced no-inhabitant wording by no-supplied-inhabitant wording where found in new front matter.'],
        'sha256':{'AHP/round15/BLUEPRINT.md':digest(mdpath),'AHP/round15/blueprint/content.tex':digest(texpath)},
    }
    out=ROOT/'AHP/round15/audit/BLUEPRINT_VALIDATION.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
