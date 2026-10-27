#!/usr/bin/env python3
"""List modules under lean/src containing sorry, admit, native_decide, sorryAx, axiom, unsafe,
implemented_by or extern, after stripping comments and string literals.  One line per module."""
import os,re,sys
root=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','lean','src')
def strip(t):
    out=[];i=0;n=len(t);dep=0
    while i<n:
        if t.startswith('/-',i): dep+=1;i+=2;continue
        if dep and t.startswith('-/',i): dep-=1;i+=2;continue
        if dep: i+=1;continue
        if t.startswith('--',i):
            j=t.find('\n',i); i=n if j<0 else j; continue
        if t[i]=="'" and i+2<n and t[i+2]=="'" and t[i+1]!='\\':   # char literal such as '"'
            i+=3; continue
        if t[i]=='"':
            j=i+1
            while j<n and t[j]!='"': j+=2 if t[j]=='\\' else 1
            i=j+1; continue
        out.append(t[i]); i+=1
    return ''.join(out)
pat=re.compile(r'\b(sorry|admit|native_decide|sorryAx|axiom|unsafe|implemented_by|extern)\b')
# Second pass on the RAW text (no comment or string stripping): any attribute list mentioning
# implemented_by or extern, i.e. @[... implemented_by f ...], @[extern "c"], attribute [extern ...].
# Comment mentions would show up too (reported, not hidden).
attr=re.compile(r'(?:@\[|attribute\s*\[)[^\]]*\b(implemented_by|extern)\b')
res=[]
attr_res=[]
for dp,dn,fn in os.walk(root):
    for f in fn:
        if f.endswith('.lean'):
            p=os.path.join(dp,f)
            h=sorted(set(pat.findall(strip(open(p,errors='replace').read()))))
            raw=open(p,errors='replace').read()
            ah=sorted(set(m.group(1) for m in attr.finditer(raw)))
            if ah: attr_res.append('ATTR\t'+os.path.relpath(p,root)[:-5].replace('/','.')+'\t'+','.join(ah))
            if h: res.append(os.path.relpath(p,root)[:-5].replace('/','.')+'\t'+','.join(h))
print('\n'.join(sorted(res)+sorted(attr_res)))
