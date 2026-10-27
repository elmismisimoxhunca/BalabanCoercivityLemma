#!/usr/bin/env python3
"""Exact Gaussian-rational analysis of the numerical 12-component collar pencil.

The matrix entries are rounded from the retained 50-digit extraction only after
checking that every non-integer residual is below 1e-40.  The resulting exact
arithmetic is evidence for a later Lean statement, not itself a proof that the
frozen operator has this matrix.
"""
from fractions import Fraction as F
import json,itertools
from pathlib import Path
OUT=Path(__file__).resolve().parent
D=json.loads((OUT/'collar_q1_R22_c0_1.json').read_text())
G0=(F(0),F(0)); G1=(F(1),F(0)); GI=(F(0),F(1))
def ga(x): return (F(x),F(0))
def gb(x): return (F(0),F(x))
def gadd(a,b): return (a[0]+b[0],a[1]+b[1])
def gneg(a): return (-a[0],-a[1])
def gsub(a,b): return gadd(a,gneg(b))
def gmul(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def gdiv(a,b):
    den=b[0]*b[0]+b[1]*b[1]
    return ((a[0]*b[0]+a[1]*b[1])/den,(a[1]*b[0]-a[0]*b[1])/den)
def gstr(a):
    if a[1]==0: return str(a[0])
    if a[0]==0: return f'({a[1]})*I'
    return f'({a[0]})+({a[1]})*I'
def exact(s):
    if not isinstance(s,str):
        z=complex(s); re,im=z.real,z.imag
    else:
        z=complex(s.replace(' ','')); re,im=z.real,z.imag
    if abs(re)<1e-40: re=0
    if abs(im)<1e-40: im=0
    assert abs(re-round(re))<1e-40 and abs(im-round(im))<1e-40,(s,re,im)
    return (F(round(re)),F(round(im)))
def trim(p):
    while len(p)>1 and p[-1]==G0: p.pop()
    return p
def add(a,b):
    c=[G0]*max(len(a),len(b))
    for i,x in enumerate(a): c[i]=gadd(c[i],x)
    for i,x in enumerate(b): c[i]=gadd(c[i],x)
    return trim(c)
def neg(a): return [gneg(x) for x in a]
def sub(a,b): return add(a,neg(b))
def mul(a,b):
    c=[G0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]=gadd(c[i+j],gmul(x,y))
    return trim(c)
def div(a,b):
    if len(a)<len(b): return [G0],a
    q=[G0]*max(1,len(a)-len(b)+1); r=a[:]
    while len(r)>=len(b) and not (len(r)==1 and r[0]==G0):
        k=len(r)-len(b); c=gdiv(r[-1],b[-1]);q[k]=c
        term=[G0]*k+[c]
        r=trim(sub(r,mul(term,b)))
    return trim(q),r
def degree(p): return len(p)-1
def evalp(p,x):
    out=G0
    for c in reversed(p): out=gadd(gmul(out,x),c)
    return out
def det_bareiss(M):
    M=[row[:] for row in M]; n=len(M); prev=[G1]; sign=1
    for k in range(n-1):
        pivot=next((i for i in range(k,n) if M[i][k]!=[G0]),None)
        if pivot is None: return [G0]
        if pivot!=k:
            M[k],M[pivot]=M[pivot],M[k];sign=-sign
        p=M[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                num=sub(mul(M[i][j],p),mul(M[i][k],M[k][j]))
                q,r=div(num,prev)
                assert r==[G0],('nonexact',k,i,j,num,prev,r)
                M[i][j]=q
            M[i][k]=[G0]
        prev=p
    return [ga(sign)] and mul([ga(sign)],M[-1][-1])
def fmtpoly(p):
    terms=[]
    for i,c in enumerate(p):
        if c==G0:continue
        terms.append(f'({gstr(c)})*x^{i}')
    return ' + '.join(terms) if terms else '0'

def main():
    M=D['reduced12_operator_blocks']
    km=[[exact(v) for v in row] for row in M['-1']]
    k0=[[exact(v) for v in row] for row in M['0']]
    kp=[[exact(v) for v in row] for row in M['1']]
    X=[G0,G1];X2=[G0,G0,G1]
    P=[[add(add([km[i][j]],mul([k0[i][j]],X)),mul([kp[i][j]],X2)) for j in range(12)] for i in range(12)]
    poly=det_bareiss(P)
    print('DEGREE',degree(poly))
    print('POLY',fmtpoly(poly))
    # Reciprocal and zero-content checks.
    print('PALINDROMIC',poly==list(reversed(poly)))
    print('EVAL_0',gstr(evalp(poly,G0)))
    print('EVAL_1',gstr(evalp(poly,G1)))
    H=[ga(1),ga(-28),ga(286),ga(-1288),ga(2387),ga(-1288),ga(286),ga(-28),ga(1)]
    Q10=[ga(1),ga(-10),ga(25),ga(-10),ga(1)]
    Q18=[ga(1),ga(-18),ga(81),ga(-18),ga(1)]
    assert mul(H,H)==poly[4:]
    assert mul(Q10,Q18)==H
    print('SQUARE_FACTOR',fmtpoly(H))
    print('QUARTIC_FACTORS',fmtpoly(Q10),fmtpoly(Q18))
    # Independent scalar evaluation of det at x=1 and x=-1 by the same Bareiss code.
    for x in [G1,ga(-1)]:
        direct=det_bareiss([[add(add([km[i][j]],[gmul(k0[i][j],x)]),[gmul(kp[i][j],gmul(x,x))]) for j in range(12)] for i in range(12)])
        print('DIRECT',gstr(x),gstr(direct[0]),'PENCIL',gstr(evalp(poly,x)))
    (OUT/'transfer_polynomial.txt').write_text(
      f'degree = {degree(poly)}\np(x) = {fmtpoly(poly)}\n'
      f'H(x) = {fmtpoly(H)}\np(x) = x^4 * H(x)^2\n'
      f'Q10(x) = {fmtpoly(Q10)}\nQ18(x) = {fmtpoly(Q18)}\nH(x) = Q10(x)*Q18(x)\n')

if __name__=='__main__':main()
