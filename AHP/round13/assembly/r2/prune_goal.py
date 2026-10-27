#!/usr/bin/env python3
"""Conservative verbatim source slicing; the Lean kernel checks every result.
No source declaration body is changed, and no dependency is trusted from Python.
"""
from pathlib import Path
import re, json, hashlib, sys
ROOT=Path(__file__).resolve().parents[4]
OUT=Path(__file__).resolve().parent

def mask(s):
    """Mask nested comments and strings, preserving line and character offsets."""
    a=list(s); i=0; depth=0; string=False
    while i<len(s):
        if depth:
            if s[i:i+2]=='/-': a[i:i+2]='  '; depth+=1; i+=2
            elif s[i:i+2]=='-/': a[i:i+2]='  '; depth-=1; i+=2
            else:
                if s[i]!='\n': a[i]=' '
                i+=1
        elif string:
            if s[i]=='"': string=False
            if s[i]=='\\' and i+1<len(s): a[i:i+2]='  '; i+=2
            else:
                if s[i]!='\n': a[i]=' '
                i+=1
        elif s[i:i+2]=='/-': a[i:i+2]='  '; depth=1; i+=2
        elif s[i:i+2]=='--':
            j=s.find('\n',i)
            if j<0:j=len(s)
            a[i:j]=' '*(j-i); i=j
        elif s[i]=='"': a[i]=' '; string=True; i+=1
        else:i+=1
    return ''.join(a)

command=re.compile(r'^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|structure|inductive|instance|section|end|namespace|open|variable|universe|set_option|attribute|local|include|omit|import|export|#print|#check|#eval)\b')
decl=re.compile(r'^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma|def|abbrev|structure|inductive|instance)\s+([^\s:({\[]+)')

def parse(source):
    s=source.read_text(); lines=s.splitlines(keepends=True); ml=mask(s).splitlines(keepends=True)
    starts=[i for i,l in enumerate(ml) if command.match(l)]
    for k,i in enumerate(starts):
        j=i-1
        while j>=0 and not ml[j].strip():j-=1
        if j>=0 and ml[j].startswith('@['): starts[k]=j
    # Scoped directives belong to their following declaration, not to the file.
    starts=[i for i in starts if not (i>0 and any(ml[j].rstrip().endswith(' in') and ml[j].startswith(('include ', 'omit ', 'open ', 'set_option ')) for j in [max((z for z in range(i) if ml[z].strip()),default=0)]))]
    starts.append(len(lines)); chunks=[]; scopes=[]
    for a,b in zip(starts,starts[1:]):
        raw=''.join(lines[a:b]); txt=''.join(ml[a:b]); stripped=txt.strip()
        scoped=re.match(r'^(?:include|omit|open|set_option) .+? in\s+',stripped)
        m=decl.match(stripped[scoped.end():] if scoped else stripped)
        if m:
            last=max(j for j in range(a,b) if ml[j].strip())+1
            raw=''.join(lines[a:last]); txt=''.join(ml[a:last]); b=last
        entry=dict(source=str(source.relative_to(ROOT)),a=a+1,b=b,raw=raw,txt=txt,name=None,kind=None,full=None)
        if m:
            kind,name=m.groups()
            full='.'.join([n for k,n in scopes if k=='namespace']+[name])
            entry.update(name=name,kind=kind,full=full)
        else:
            head=stripped.splitlines()[0] if stripped else ''
            ns=re.match(r'namespace\s+(\S+)',head)
            sec=re.match(r'(?:noncomputable\s+)?section(?:\s+(\S+))?',head)
            if ns:scopes.append(('namespace',ns.group(1)))
            elif sec:scopes.append(('section',sec.group(1) or ''))
            elif re.match(r'end(?:\s|$)',head):
                assert scopes,(source,a,head)
                scopes.pop()
        chunks.append(entry)
    assert all(k=='section' for k,n in scopes),(source,scopes)
    return chunks

def slice_chunks(chunks,seed):
    byname={}
    for i,c in enumerate(chunks):
        if c['name']:
            ns=c['name'].split('.')
            for k in range(len(ns)):byname.setdefault('.'.join(ns[k:]),set()).add(i)
    tokens=re.compile(r"[\w\u2080-\u209f]+(?:\.[\w\u2080-\u209f]+)*(?:')*")
    def references(txt):
        result=set()
        for t in tokens.findall(txt):
            parts=t.split('.')
            for a in range(len(parts)):
                for b in range(a+1,len(parts)+1):
                    n='.'.join(parts[a:b])
                    if n in byname:result |= byname[n]
        return result
    keep=set().union(*(byname[n] for n in seed))
    for i,c in enumerate(chunks):
        if c['kind']=='instance' or (c['name'] or '').startswith(('AnM.','AnR.')):keep.add(i)
        if not c['name'] and not c['txt'].lstrip().startswith('#'):keep |= references(c['txt'])
    while True:
        old=len(keep)
        for i in list(keep):keep |= references(chunks[i]['txt'])
        if len(keep)==old:break
    return [c for i,c in enumerate(chunks) if (not c['name'] or i in keep) and not c['txt'].lstrip().startswith('#')]

def output(chunks,name,prints):
    out=[]; manifest=[]; imports=set()
    for c in chunks:
        if c['txt'].lstrip().startswith('import '):
            imports.update(re.findall(r'^import (\S+)',c['txt'],re.M));continue
        if c['name']:
            out.append(c['raw'])
            manifest.append(dict(source=c['source'],first=c['a'],last=c['b'],name=c['full'],sha256=hashlib.sha256(c['raw'].encode()).hexdigest()))
        else:out.append(c['txt'])
    text=''.join('import '+i+'\n' for i in sorted(imports))+'\n'+''.join(out)
    text+='\n'+''.join('#print axioms '+p+'\n#check @'+p+'\n' for p in prints)
    (OUT/(name+'.lean')).write_text(text)
    (OUT/(name+'_COPIES.json')).write_text(json.dumps(manifest,indent=2)+'\n')
    print(name,':',len(manifest),'verbatim declarations;',len(text.splitlines()),'lines')

if __name__=='__main__':
    p2join='--p2' in sys.argv
    joined='--joined' in sys.argv or p2join
    sources=['AHP/round13/assembly/r1/RepairedJoin.lean']
    seed={'goalNeg2_of_cofinalAnyPathNoResponseCancellation'}
    prints=['AdalyFormal.Round10.Assembly.R4.goalNeg2_of_cofinalAnyPathNoResponseCancellation']
    if joined:
        sources+=['AHP/round13/shared/assembly/R1_P1Spine.lean','AHP/round13/assembly/r2/GoalAppendix.lean.txt']
        seed={'goalNeg2_of_P2_P3','goalNeg2_of_cofinalP2P3'}
        prints+=['AdalyFormal.Round13.Assembly.R2.'+n for n in sorted(seed)]
    if p2join:
        sources+=['AHP/round13/shared/positivity/R2_P2.lean','AHP/round13/assembly/r2/P2Appendix.lean.txt']
        added={'p2','rightStar_kernelLine','cofinal_rightStar_kernelLine','cofinalNoCancellation_of_P3',
          'goalNeg2_of_P3','CofinalP3','cofinalP2P3_of_cofinalP3','cofinalNoCancellation_of_cofinalP3','goalNeg2_of_cofinalP3'}
        seed |= added
        prints+=['AdalyFormal.Round13.Assembly.R2.'+n for n in sorted(added)]
    allchunks=[]; seen={}; duplicates=[]
    for p in sources:
        for c in parse(ROOT/p):
            if c['full'] in seen:
                prev=seen[c['full']]
                duplicates.append(dict(name=c['full'],kept=prev['source'],skipped=c['source'],identical=c['raw']==prev['raw']))
                continue
            if c['full']:seen[c['full']]=c
            allchunks.append(c)
    chunks=slice_chunks(allchunks,seed)
    name='P2Goal' if p2join else ('PhysicalGoal' if joined else 'GoalBridge')
    output(chunks,name,prints)
    (OUT/(name+'_DEDUP.json')).write_text(json.dumps(duplicates,indent=2)+'\n')
