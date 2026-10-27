#!/usr/bin/env python3
"""Generate exact K/Schur Lean declarations. Numerical data is evidence only."""
import json
from fractions import Fraction as F
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
D=json.loads((ROOT/'AHP/round15/dictionary/r1/full_q1_R20_c1_0_x220.json').read_text())
class G:
 def __init__(self,a=0,b=0): self.a,self.b=F(a),F(b)
 def __add__(x,y): return G(x.a+y.a,x.b+y.b)
 def __sub__(x,y): return G(x.a-y.a,x.b-y.b)
 def __neg__(x): return G(-x.a,-x.b)
 def __mul__(x,y): return G(x.a*y.a-x.b*y.b,x.a*y.b+x.b*y.a)
 def __truediv__(x,y):
  d=y.a*y.a+y.b*y.b
  return G((x.a*y.a+x.b*y.b)/d,(x.b*y.a-x.a*y.b)/d)
I=G(0,1)
def val(v):
 if isinstance(v,(int,float)): return G(v)
 s=str(v).replace('(','').replace(')','').replace(' ','')
 if 'j' in s:
  if s.startswith('-1.0'): return G(-1,1 if '+1.0j' in s else -1)
  return I if '+1.0j' in s else -I
 return G(F(s))
def mm(A,B): return [[sum((A[i][k]*B[k][j] for k in range(len(B))),G()) for j in range(len(B[0]))] for i in range(len(A))]
def inv(A):
 n=len(A); M=[row[:]+[G(int(i==j)) for j in range(n)] for i,row in enumerate(A)]
 for c in range(n):
  piv=next(r for r in range(c,n) if M[r][c].a or M[r][c].b)
  M[c],M[piv]=M[piv],M[c]
  z=M[c][c]; M[c]=[v/z for v in M[c]]
  for r in range(n):
   if r==c: continue
   z=M[r][c]
   if z.a or z.b: M[r]=[v-z*w for v,w in zip(M[r],M[c])]
 return [row[n:] for row in M]
def sub(A,B): return [[x-y for x,y in zip(ra,rb)] for ra,rb in zip(A,B)]
order=[(a,d) for d in range(3) for a in range(4)]
def mat(dx):
 raw=D['blocks'][str(dx)]
 return [[val(raw[3*a+d][3*b+e]) for b,e in order] for a,d in order]
Kp,K0,Km=mat(1),mat(0),mat(-1)
b00=[r[:4] for r in K0[:4]]
bi=inv(b00)
wB=mm([r[:4] for r in K0[4:]],bi)
wC=mm([r[:4] for r in Km[4:]],bi)
def lean_num(v):
 def rat(x): return str(x)
 if v.b==0: return f'({rat(v.a)} : ℂ)'
 if v.a==0: return f'({rat(v.b)} : ℂ) * Complex.I'
 return f'({rat(v.a)} : ℂ) + ({rat(v.b)} : ℂ) * Complex.I'
def matdecl(name,M):
 rows=[','.join(lean_num(v) for v in row) for row in M]
 body=';\n    '.join(rows)
 return f'noncomputable def {name} : Matrix (Fin {len(M)}) (Fin {len(M[0])}) ℂ :=\n    !![{body}]\n\n'
# rectangular matrices use separate row/column dimensions
def matdecl_rc(name,M):
 rows=[','.join(lean_num(v) for v in row) for row in M]
 body=';\n    '.join(rows)
 return f'noncomputable def {name} : Matrix (Fin {len(M)}) (Fin {len(M[0])}) ℂ :=\n    !![{body}]\n\n'
parts=[]
parts.append(matdecl('q1Kplus',Kp))
parts.append(matdecl('q1Kzero',K0))
parts.append(matdecl('q1Kminus',Km))
parts.append(matdecl('q1B00',b00))
parts.append(matdecl('q1B00Inv',bi))
parts.append(matdecl_rc('q1A01',[r[4:] for r in Kp[:4]]))
parts.append(matdecl_rc('q1B01',[r[4:] for r in K0[:4]]))
parts.append(matdecl_rc('q1C01',[r[4:] for r in Km[:4]]))
parts.append(matdecl_rc('q1A11',[r[4:] for r in Kp[4:]]))
parts.append(matdecl_rc('q1B11',[r[4:] for r in K0[4:]]))
parts.append(matdecl_rc('q1C11',[r[4:] for r in Km[4:]]))
parts.append(matdecl_rc('q1B10',[r[:4] for r in K0[4:]]))
parts.append(matdecl_rc('q1C10',[r[:4] for r in Km[4:]]))
parts.append(matdecl_rc('q1WeightB',wB))
parts.append(matdecl_rc('q1WeightC',wC))
# R1's collar model is copied unchanged, followed by these declarations.
collar=(ROOT/'AHP/round15/dictionary/r1/Collar.lean').read_text()
collar_body=collar.split('import DrEquiv\n',1)[1]
header='import DrEquiv\n\n/-! Exact full-collar matrices and Schur-complement identities. -/\nset_option autoImplicit false\nset_option maxHeartbeats 4000000\nset_option maxRecDepth 16000\n\n'
# Keep the original R1 namespace and declarations, then add K identities.
extra='''\n/-- The four-by-four central inverse is exact. -/\ntheorem q1B00_inv :\n    q1B00 * q1B00Inv = 1 ∧ q1B00Inv * q1B00 = 1 := by\n  constructor\n  · ext i j\n    fin_cases i <;> fin_cases j <;>\n      simp [q1B00, q1B00Inv, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      field_simp <;> ring_nf <;> norm_num [pow_two, Complex.I_mul_I] <;> ring
  · ext i j\n    fin_cases i <;> fin_cases j <;>
      simp [q1B00, q1B00Inv, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      field_simp <;> ring_nf <;> norm_num [pow_two, Complex.I_mul_I] <;> ring

/-- The Schur complement of the full direction-zero elimination is R1's `collarA`. -/\ntheorem q1_schurA :\n    q1A11 - q1B10 * q1B00Inv * q1A01 = collarA := by\n  ext i j\n  fin_cases i <;> fin_cases j <;>
    simp [q1A11, q1B10, q1B00Inv, q1A01, collarA,\n      Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> ring_nf <;> norm_num [pow_two, Complex.I_mul_I] <;> ring

/-- The central-plus-forward Schur complement is R1's `collarB`. -/\ntheorem q1_schurB :\n    q1B11 - q1B10 * q1B00Inv * q1B01 - q1C10 * q1B00Inv * q1A01 = collarB := by\n  ext i j\n  fin_cases i <;> fin_cases j <;>
    simp [q1B11, q1B10, q1B00Inv, q1B01, q1C10, q1A01, collarB,\n      Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> ring_nf <;> norm_num [pow_two, Complex.I_mul_I] <;> ring

/-- The backward Schur complement is R1's `collarC`. -/\ntheorem q1_schurC :\n    q1C11 - q1C10 * q1B00Inv * q1B01 = collarC := by\n  ext i j\n  fin_cases i <;> fin_cases j <;>
    simp [q1C11, q1C10, q1B00Inv, q1B01, collarC,\n      Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> ring_nf <;> norm_num [pow_two, Complex.I_mul_I] <;> ring

#print axioms q1B00_inv
#print axioms q1_schurA
#print axioms q1_schurB
#print axioms q1_schurC
'''
# Collar body already has its own options and namespace. Append data in same namespace.
text=header+collar_body+'\n'+'open AdalyFormal.Round15.Dictionary\n\n'+''.join(parts)+extra
(ROOT/'AHP/round15/dictionary/r2/KData.lean').write_text(text)
print('wrote KData.lean',len(text),'bytes')
