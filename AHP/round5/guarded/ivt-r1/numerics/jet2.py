"""Order-two directional Taylor arithmetic; no differencing for C2.
The zeroth-order log arguments are near identity in this probe. The analytic
log/exp scalar factors are evaluated by 14-term power series. Floating point,
not interval arithmetic or a formal operator dictionary.
"""
import math
import numpy as np
from assembly import E, I, coords


def mul(a, b):
    return np.array([sum(a[i]*b[n-i] for i in range(n+1)) for n in range(3)])


def matmul(a, b):
    return np.array([sum(a[i]@b[n-i] for i in range(n+1)) for n in range(3)])


def conj(a):
    return a.swapaxes(-1, -2).conj()


def const(a):
    z=np.zeros((3,)+np.shape(a),dtype=np.result_type(a))
    z[0]=a
    return z


def polynomial(s, coefficients):
    ans=const(np.zeros_like(s[0]))
    for c in reversed(coefficients):
        ans=mul(ans,s)
        ans[0]+=c
    return ans


def exp(v):
    s=mul(v,v).sum(axis=-1)
    co=polynomial(s,[(-1.)**n/math.factorial(2*n) for n in range(14)])
    si=polynomial(s,[(-1.)**n/math.factorial(2*n+1) for n in range(14)])
    vv=mul(si[...,None],v)
    return co[...,None,None]*I+np.einsum('k...a,aij->k...ij',vv,E)


def log(g):
    # For SU(2) with positive real trace: log(g)=asin(|Im g|)/|Im g| Im g.
    assert np.min(np.trace(g[0],axis1=-2,axis2=-1).real/2)>.95
    v=coords((g-conj(g))/2)
    s=mul(v,v).sum(axis=-1)
    coeff=[math.comb(2*n,n)/(4**n*(2*n+1)) for n in range(14)]
    return mul(polynomial(s,coeff)[...,None],v)


def raw_jet(raw, a):
    """Returns q(0), q'(0), q''(0)/2 for a full fine-bond direction."""
    shape=a.shape[:-1] if a.ndim>1 else ()
    v=np.zeros((3,)+shape+(raw.lat.nB,3));v[1]=a.reshape(shape+(raw.lat.nB,3))
    u=matmul(exp(v),const(np.broadcast_to(raw.u,shape+raw.u.shape)))
    def hol(vals,path):
        ans=const(np.broadcast_to(I,shape+I.shape))
        for i in path: ans=matmul(ans,vals[...,i,:,:])
        return ans
    ubg=const(np.broadcast_to(raw.u,shape+raw.u.shape))
    result=[]
    for (base,legs),bg in zip(raw.data,raw.bg):
        b=hol(u,base)
        sm=const(np.zeros(shape+(3,)));sp=sm.copy();ss=sm.copy()
        for left,mid,right in legs:
            ll=hol(u,left);rr=hol(u,right)
            ss+=log(matmul(matmul(matmul(ll,hol(u,mid)),conj(rr)),conj(b)))/8
            sm+=log(matmul(ll,conj(hol(ubg,left))))/8
            sp+=log(matmul(rr,conj(hol(ubg,right))))/8
        blocked=matmul(exp(ss),b)
        word=matmul(matmul(matmul(exp(-sm),blocked),exp(sp)),const(np.broadcast_to(bg.conj().T,shape+bg.shape)))
        result.append(log(word)/2)
    return np.stack(result,axis=-2).reshape((3,)+shape+(-1,))
