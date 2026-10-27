from pathlib import Path
import json,re
from source_utils import signature_end
D=Path('AHP/round4/guarded/mine')
# Lexically remove comments while preserving every line number.
def uncomment(s):
    out=[]; depth=0; i=0
    while i<len(s):
        if s[i:i+2]=='/-': depth+=1;out.extend('  ');i+=2
        elif depth and s[i:i+2]=='-/': depth-=1;out.extend('  ');i+=2
        elif depth: out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif s[i:i+2]=='--':
            j=s.find('\n',i);j=len(s) if j<0 else j;out.extend(' '*(j-i));i=j
        else:out.append(s[i]);i+=1
    return ''.join(out)
idx={}
for f in sorted(Path('lean/src').rglob('*.lean')):
    if 'BalabanCompact' in f.parts or 'R7Fork' in f.parts or f.name.startswith('Compact'):continue
    raw=f.read_text(); clean=uncomment(raw); lines=clean.splitlines(); stack=[]
    for i,line in enumerate(lines):
        if m:=re.match(r'^namespace\s+(\S+)',line):stack.append(('namespace',m[1]))
        elif m:=re.match(r'^section(?:\s+(\S+))?\s*$',line):stack.append(('section',m[1] or ''))
        elif re.match(r'^end(?:\s+\S+)?\s*$',line):
            if stack:stack.pop()
        elif m:=re.match(r'^(?:(?:noncomputable|protected)\s+)*(theorem|lemma|def|abbrev|structure)\s+([^\s({:\[]+)',line):
            n='.'.join([x[1] for x in stack if x[0]=='namespace']+[m[2]])
            start=sum(len(x)+1 for x in lines[:i]); rest=clean[start:]
            cut=signature_end(rest)
            header=rest[:cut] if cut is not None else rest.split('\n\n')[0]
            idx[n]={'name':n,'file':str(f),'line':i+1,'kind':m[1], 'header':header.strip()}
graph={}
for line in (D/'Trace.lean.log').read_text().splitlines():
    if line.startswith('DEPENDENCY|'):
        _,n,deps=line.split('|',2);graph[n]=[x for x in deps.split(',') if x]
roots=['AdalyFormal.Total.p428Target8Total','MXP.Total.p428Target8Mixed','MXQ.Total.p428Target8FamilyTorus','AdalyFormal.M2RightInv.p428Target8','AdalyFormal.D1Residual.P428Target8SG_iff_pencilT']
def closure(root):
    seen=set();todo=[root]
    while todo:
        n=todo.pop()
        if n in seen:continue
        seen.add(n);todo+=graph.get(n,[])
    return seen
cls={r:closure(r) for r in roots}
for n,d in idx.items():d['roots']=[r for r,c in cls.items() if n in c]
(D/'index.json').write_text(json.dumps(idx,ensure_ascii=False,indent=2))
(D/'graph.json').write_text(json.dumps(graph,ensure_ascii=False))
pat=re.compile(r'Ginv|G1inv|Delta2|delta2|coer|wellDef|WellDef|isUnit|IsUnit|[Cc]2.*(?:[Cc]ongr|[Bb]ound|[Ll]ocal)|[Ss]econd|[Jj]et.*(?:[Ll]ocal|[Bb]ound)|[Gg]ap|[Ll]ower|[Hh]1?[Bb]all|[Hh]1?.*[Dd]ecay|[Pp]si.*class|rightInv|units|p428Target|strong_core|thin_core')
rows=[]
for n,d in idx.items():
    if d['roots'] and pat.search(n):rows.append(d)
rows.sort(key=lambda d:(d['file'],d['line']))
(D/'reachable-candidates.txt').write_text('\n'.join(f"{d['file']}:{d['line']} {d['name']} [{','.join(r.split('.')[-2] for r in d['roots'])}]" for d in rows)+'\n')
print('index',len(idx),'traced',len(graph),'mapped traced',len(set(graph)&set(idx)),'candidates',len(rows))
print('roots', {r:len(c) for r,c in cls.items()})
