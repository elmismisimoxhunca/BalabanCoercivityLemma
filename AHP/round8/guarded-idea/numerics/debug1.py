import sys
sys.dont_write_bytecode=True
sys.path.insert(0,'/home/sebastian/BalabanCoercivityLemma/AHP/round6/probe')
from probe import *
from positivity import draw, corrected_aug
sys.path.insert(0,'.')
from sepcheck import boundary_schur, eigs, lam, carrier_lift
mp.mp.dps=40
q,R,eps=1,6,mp.mpf('1e-3')
f=Family(q,R,eps,0,0,1).assemble()
S,X=boundary_schur(f,f.aug)
nf=Family(q,R,eps,0,0,0).assemble(); hj,_=nf.hj()
D,_=draw(f,hj); ca=corrected_aug(f,D)
SC,XC=boundary_schur(f,ca)
th0=f.theta(0); th1=f.theta(mp.pi/2)
theta=lambda t: mp.cos(t)*th0+mp.sin(t)*th1
tB=mp.findroot(lambda t: lam(S+theta(t)),(mp.mpf('.5'),mp.mpf('.7')),solver='secant',tol=mp.mpf(10)**-35,verify=False)
ev,V=eigs(S+theta(tB)); y=V[:,0]
full,nrm=carrier_lift(f,S,X,y)
v=full[:f.n]; u=full[f.n:f.n+f.H.n]; w=f.dressed(v,u)
pc,_=f.correction(w,hj)
pD=sum(conj(w[i])*val*w[j] for i,row in enumerate(D.r) for j,val in row.items())
print('pairing correction()', mp.nstr(pc,12),' sparse D form', mp.nstr(pD,12))
# augmented-form D on full vector
diff=f.aug.plus(Sp(f.aug.n,f.aug.n))
# (aug - ca) z
az=f.aug.apply(full); cz=ca.apply(full)
dz=[a-b for a,b in zip(az,cz)]
print('z*(aug-ca)z', mp.nstr(sum(conj(a)*b for a,b in zip(full,dz)),12))
# hermiticity of aug and ca
def herm_err(A):
    m=0
    for i,row in enumerate(A.r):
        for j,val in row.items():
            m=max(m,abs(val-conj(A.r[j].get(i,0))))
    return m
print('aug herm err',mp.nstr(herm_err(f.aug),5),' ca herm err',mp.nstr(herm_err(ca),5), 'D herm', mp.nstr(herm_err(D),5))
print('<y,(SC-S)y>', mp.nstr(mp.re((y.H*(SC-S)*y)[0]),12), ' -nrm^2 pc', mp.nstr(-nrm**2*pc,12))
# exact second order: SC - S vs -S Y S with Y from XC-X
Cm=mp.matrix([[col[i] for col in X] for i in f.boundary]); CmC=mp.matrix([[col[i] for col in XC] for i in f.boundary])
Y=CmC-Cm
print('herm Y', mp.nstr(mp.norm(Y-Y.H),5))
print('-<Sy,Y Sy>', mp.nstr(-mp.re(((S*y).H*Y*(S*y))[0]),12))
# first-order Y from D: Y1 = X_b^* (aug-ca) X_b  restricted
Y1=mp.matrix(len(f.boundary),len(f.boundary))
dcols=[]
for k in range(len(X)):
    a=f.aug.apply(X[k]); c=ca.apply(X[k]); dcols.append([p-r for p,r in zip(a,c)])
for i in range(len(X)):
    for j in range(len(X)):
        Y1[i,j]=sum(conj(a)*b for a,b in zip(X[i],dcols[j]))
print('|Y-Y1|',mp.nstr(mp.norm(Y-Y1),5),' |Y|',mp.nstr(mp.norm(Y),5))
print('-<Sy,Y1 Sy>', mp.nstr(-mp.re(((S*y).H*Y1*(S*y))[0]),12))
