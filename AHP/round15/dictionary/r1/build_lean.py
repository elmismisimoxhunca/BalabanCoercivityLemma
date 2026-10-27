#!/usr/bin/env python3
"""Generate the compact exact dominant-collar Lean certificate.

The matrix entries are Gaussian rationals extracted from the same frozen-family
numerical dictionary audited in this directory.  The generated proofs use no
numerical premise: Lean checks the displayed matrix and eigenpairs directly.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from fractions import Fraction
import json
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'AHP/round6/probe'))
from probe import Family,mp
H=Path(__file__).resolve().parent
CELLS=[(0,0),(1,0),(0,1),(1,1)]
ZERO=(Fraction(0),Fraction(0))
ONE=(Fraction(1),Fraction(0))

def add(z,w):return (z[0]+w[0],z[1]+w[1])
def neg(z):return (-z[0],-z[1])
def sub(z,w):return add(z,neg(w))
def mul(z,w):return (z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])
def inv(z):
    d=z[0]*z[0]+z[1]*z[1]
    return (z[0]/d,-z[1]/d)
def matmul(A,B):
    assert len(A[0])==len(B)
    def dot(i,j):
        ans=ZERO
        for k in range(len(B)):ans=add(ans,mul(A[i][k],B[k][j]))
        return ans
    return [[dot(i,j) for j in range(len(B[0]))] for i in range(len(A))]
def matinv(A):
    n=len(A);M=[row[:]+[ONE if i==j else ZERO for j in range(n)] for i,row in enumerate(A)]
    for k in range(n):
        p=next(i for i in range(k,n) if M[i][k]!=ZERO)
        M[k],M[p]=M[p],M[k]
        u=inv(M[k][k]);M[k]=[mul(u,x) for x in M[k]]
        for i in range(n):
            if i==k:continue
            c=M[i][k]
            if c!=ZERO:M[i]=[sub(x,mul(c,y)) for x,y in zip(M[i],M[k])]
    return [row[n:] for row in M]
def exact(z):
    z=complex(z)
    return (Fraction(round(z.real)),Fraction(round(z.imag)))

def build():
    mp.mp.dps=50
    f=Family(1,20,mp.mpf(0),1,0,1).assemble()
    def var(x,y,z,d):return f.em.get(f.bi[((x,y,z),d)])
    def entry(x,a,d,y,b,e):
        ya,za=CELLS[a];yb,zb=CELLS[b];i,j=var(x,ya,za,d),var(y,yb,zb,e)
        return exact(f.K.r[i].get(j,0)) if i is not None and j is not None else ZERO
    order=[(a,d) for d in range(3) for a in range(4)]
    def mat(dx):return [[entry(220,a,d,220+dx,b,e) for b,e in order] for a,d in order]
    A,B,C=mat(1),mat(0),mat(-1)
    def blocks(M):return ([row[:4] for row in M[:4]],[row[4:] for row in M[:4]],
      [row[:4] for row in M[4:]],[row[4:] for row in M[4:]])
    A00,A01,A10,A11=blocks(A);B00,B01,B10,B11=blocks(B);C00,C01,C10,C11=blocks(C)
    assert A00==[[ZERO]*4 for _ in range(4)] and C00==[[ZERO]*4 for _ in range(4)]
    assert A10==[[ZERO]*4 for _ in range(8)] and C01==[[ZERO]*8 for _ in range(4)]
    Bi=matinv(B00)
    # Use matrix products directly to avoid any floating-point roundoff.
    def mm(X,Y):return matmul(X,Y)
    ar=[[sub(A11[i][j],mm(mm(B10,Bi),A01)[i][j]) for j in range(8)] for i in range(8)]
    br=[[sub(sub(B11[i][j],mm(mm(B10,Bi),B01)[i][j]),mm(mm(C10,Bi),A01)[i][j])
      for j in range(8)] for i in range(8)]
    cr=[[sub(C11[i][j],mm(mm(C10,Bi),B01)[i][j]) for j in range(8)] for i in range(8)]
    ai=matinv(ar)
    M=[[neg(x) for x in row] for row in mm(ai,br)]
    N=[[neg(x) for x in row] for row in mm(ai,cr)]
    T=[[ZERO]*16 for _ in range(16)]
    for i in range(8):
        for j in range(8):
            T[i][j]=M[i][j];T[i][j+8]=N[i][j];T[i+8][j]=ONE if i==j else ZERO
    ci=matinv(cr)
    Mi=[[neg(x) for x in row] for row in mm(ci,ar)]
    Ni=[[neg(x) for x in row] for row in mm(ci,br)]
    Ti=[[ZERO]*16 for _ in range(16)]
    for i in range(8):
        for j in range(8):
            Ti[i][j+8]=ONE if i==j else ZERO
            Ti[i+8][j]=Mi[i][j];Ti[i+8][j+8]=Ni[i][j]
    (H/'exact_transfer.json').write_text(json.dumps({'A':[[[str(z[0]),str(z[1])] for z in row] for row in ar],
      'B':[[[str(z[0]),str(z[1])] for z in row] for row in br],
      'C':[[[str(z[0]),str(z[1])] for z in row] for row in cr],
      'T':[[[str(z[0]),str(z[1])] for z in row] for row in T],
      'Tinverse':[[[str(z[0]),str(z[1])] for z in row] for row in Ti]},indent=2)+'\n')
    return ar,br,cr,T,Ti

def cnum(z):
    re,im=z
    def fc(x):
        if x.denominator==1:return f'({x.numerator} : ℂ)'
        return f'({x.numerator}/{x.denominator} : ℂ)'
    if im==0:
        return '0' if re==0 else fc(re)
    if re==0:return f'{fc(im)}*Complex.I'
    return f'{fc(re)}+{fc(im)}*Complex.I'

def matrix_decl(name,T):
    n=len(T)
    rows=['  !![',';'.join(','.join(cnum(z) for z in row) for row in T)]
    return f'def {name} : Matrix (Fin {n}) (Fin {n}) ℂ :=\n  {rows[0]}{rows[1]}]\n'

HEADER='''import DrEquiv

/-!
Round 15: an exact dominant two-sublattice collar transfer certificate.

The displayed 16-by-16 matrix is the reduced eight-transverse-mode companion
matrix identified by `inspect_full.py` and `factor_audit.py`.  This file proves
its two dominant reciprocal eigenpairs directly.  It does NOT assert that this
matrix has already been identified with the frozen right-star operator in Lean;
that physical dictionary is recorded separately in NOTES.md.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.Round15.Dictionary

noncomputable section

/-- The dominant root satisfies rho+rho⁻¹=5-sqrt(2). -/
def rho : ℝ := (5-Real.sqrt 2+Real.sqrt (23-10*Real.sqrt 2))/2

/-- A sparse charged internal-sublattice phase. -/
def phase : ℂ := (1+Complex.I)/(Real.sqrt 2:ℂ)

def mode0 : Fin 8 → ℂ
  | 0 => 1 | 1 => phase | 2 => 1 | 3 => phase | _ => 0

def mode1 : Fin 8 → ℂ
  | 4 => 1 | 5 => phase | 6 => 1 | 7 => phase | _ => 0

/-- Geometric state at adjacent layers: the second half is rho⁻¹ times the first. -/
def forward (w : Fin 8 → ℂ) : Fin 16 → ℂ :=
  fun i => if h : i.val < 8 then w ⟨i.val,h⟩ else (1/rho : ℂ)*w ⟨i.val-8,by omega⟩

/-- The same charged internal mode transported by the reciprocal root. -/
def backward (w : Fin 8 → ℂ) : Fin 16 → ℂ :=
  fun i => if h : i.val < 8 then w ⟨i.val,h⟩ else (rho : ℂ)*w ⟨i.val-8,by omega⟩

'''

PROOFS='''
theorem rho_pos : 0 < rho := by
  have h2 : 0 ≤ (2 : ℝ) := by norm_num
  have hs2 := Real.sq_sqrt h2
  have hdisc : 0 ≤ 23-10*Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hsd := Real.sq_sqrt hdisc
  have hs12 : Real.sqrt 2 < 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hr : 0 < 5-Real.sqrt 2+Real.sqrt (23-10*Real.sqrt 2) := by
    nlinarith [Real.sqrt_nonneg (23-10*Real.sqrt 2)]
  exact div_pos hr (by norm_num)

theorem rho_quad : rho^2 = (5-Real.sqrt 2)*rho-1 := by
  have h2 : 0 ≤ (2 : ℝ) := by norm_num
  have hs2 := Real.sq_sqrt h2
  have hdisc : 0 ≤ 23-10*Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hsd := Real.sq_sqrt hdisc
  unfold rho
  field_simp
  ring_nf at *
  linear_combination hsd - hs2

theorem rho_ne_zero : rho ≠ 0 := ne_of_gt rho_pos

theorem phase_sq : phase^2 = Complex.I := by
  have h2 : 0 ≤ (2 : ℝ) := by norm_num
  have hs2 := Real.sq_sqrt h2
  unfold phase
  rw [div_pow, ← Complex.ofReal_pow, hs2]
  ring_nf
  simp

/-- Direct verification of the first sparse dominant eigenvector. -/
theorem dominant_mode0_forward : Matrix.mulVec dominantTransfer (forward mode0) = (rho : ℂ) • forward mode0 := by
  have hr := rho_quad
  have hrC : (rho : ℂ)^2 = (5-Real.sqrt 2 : ℂ)*(rho : ℂ)-1 := by exact_mod_cast hr
  have hs2C : (Real.sqrt 2 : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num
  have hz := rho_ne_zero
  have hp := phase_sq
  funext i
  fin_cases i <;>
    simp [dominantTransfer, forward, mode0, phase, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, smul_eq_mul] <;>
    field_simp [hz] <;>
    ring_nf <;>
    norm_num [hrC, hs2C, hp, Complex.I_mul_I] <;>
    ring_nf <;>
    rw [hs2C] <;>
    norm_num <;> ring

/-- Direct verification of the shifted independent dominant eigenvector. -/
theorem dominant_mode1_forward : Matrix.mulVec dominantTransfer (forward mode1) = (rho : ℂ) • forward mode1 := by
  have hr := rho_quad
  have hrC : (rho : ℂ)^2 = (5-Real.sqrt 2 : ℂ)*(rho : ℂ)-1 := by exact_mod_cast hr
  have hs2C : (Real.sqrt 2 : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num
  have hz := rho_ne_zero
  have hp := phase_sq
  funext i
  fin_cases i <;>
    simp [dominantTransfer, forward, mode1, phase, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, smul_eq_mul] <;>
    field_simp [hz] <;>
    ring_nf <;>
    norm_num [hrC, hs2C, hp, Complex.I_mul_I] <;>
    ring_nf <;>
    rw [hs2C] <;>
    norm_num <;> ring

/-- The reciprocal root acts on the first sparse mode. -/
theorem dominant_mode0_backward : Matrix.mulVec dominantTransfer (backward mode0) = (1/rho : ℂ) • backward mode0 := by
  have hr := rho_quad
  have hrC : (rho : ℂ)^2 = (5-Real.sqrt 2 : ℂ)*(rho : ℂ)-1 := by exact_mod_cast hr
  have hs2C : (Real.sqrt 2 : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num
  have hz := rho_ne_zero
  have hp := phase_sq
  funext i
  fin_cases i <;>
    simp [dominantTransfer, backward, mode0, phase, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, smul_eq_mul] <;>
    field_simp [hz] <;>
    ring_nf <;>
    norm_num [hrC, hs2C, hp, Complex.I_mul_I] <;>
    ring_nf <;>
    rw [hs2C] <;>
    norm_num

/-- The reciprocal root acts on the shifted sparse mode. -/
theorem dominant_mode1_backward : Matrix.mulVec dominantTransfer (backward mode1) = (1/rho : ℂ) • backward mode1 := by
  have hr := rho_quad
  have hrC : (rho : ℂ)^2 = (5-Real.sqrt 2 : ℂ)*(rho : ℂ)-1 := by exact_mod_cast hr
  have hs2C : (Real.sqrt 2 : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num
  have hz := rho_ne_zero
  have hp := phase_sq
  funext i
  fin_cases i <;>
    simp [dominantTransfer, backward, mode1, phase, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, smul_eq_mul] <;>
    field_simp [hz] <;>
    ring_nf <;>
    norm_num [hrC, hs2C, hp, Complex.I_mul_I] <;>
    ring_nf <;>
    rw [hs2C] <;>
    norm_num

/-- Exact reciprocal dominant eigenpairs of the displayed collar transfer. -/
theorem dominant_eigenpairs :
    Matrix.mulVec dominantTransfer (forward mode0) = (rho : ℂ) • forward mode0 ∧
    Matrix.mulVec dominantTransfer (forward mode1) = (rho : ℂ) • forward mode1 ∧
    Matrix.mulVec dominantTransfer (backward mode0) = (1/rho : ℂ) • backward mode0 ∧
    Matrix.mulVec dominantTransfer (backward mode1) = (1/rho : ℂ) • backward mode1 :=
  ⟨dominant_mode0_forward, dominant_mode1_forward,
    dominant_mode0_backward, dominant_mode1_backward⟩

#print axioms rho
#print axioms phase
#print axioms mode0
#print axioms mode1
#print axioms forward
#print axioms backward
#print axioms dominantTransfer
#print axioms rho_pos
#print axioms rho_quad
#print axioms rho_ne_zero
#print axioms phase_sq
#print axioms dominant_mode0_forward
#print axioms dominant_mode1_forward
#print axioms dominant_mode0_backward
#print axioms dominant_mode1_backward
#print axioms dominant_eigenpairs

end
end AdalyFormal.Round15.Dictionary
'''

EXTRA='''
/-- The companion matrix is explicitly invertible. -/
theorem transfer_inverse :
    dominantTransfer * dominantTransferInverse = 1 ∧
    dominantTransferInverse * dominantTransfer = 1 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dominantTransfer, dominantTransferInverse, Matrix.mul_apply,
        Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dominantTransfer, dominantTransferInverse, Matrix.mul_apply,
        Fin.sum_univ_succ]

/-- A transported scalar seed. -/
def observation (w : Fin 8 → ℂ) (n : ℕ) : Fin 8 → ℂ :=
  fun k => (rho^n : ℂ) * w k

/-- The exact second-order recurrence for the first sparse mode. -/
theorem dominant_mode0_recurrence (n : ℕ) :
    Matrix.mulVec collarA (observation mode0 (n+2)) +
      Matrix.mulVec collarB (observation mode0 (n+1)) +
      Matrix.mulVec collarC (observation mode0 n) = 0 := by
  have hr := rho_quad
  have hrC : (rho : ℂ)^2 = (5-Real.sqrt 2 : ℂ)*(rho : ℂ)-1 := by exact_mod_cast hr
  have hs2C : (Real.sqrt 2 : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num
  have hz := rho_ne_zero
  have hp := phase_sq
  funext i
  fin_cases i <;>
    simp [collarA, collarB, collarC, observation, mode0, phase,
      dotProduct, Fin.sum_univ_succ] <;>
    field_simp [hz] <;>
    ring_nf <;>
    norm_num [hrC, hs2C, hp, Complex.I_mul_I] <;>
    ring_nf <;>
    rw [hs2C] <;>
    ring

/-- The exact second-order recurrence for the shifted sparse mode. -/
theorem dominant_mode1_recurrence (n : ℕ) :
    Matrix.mulVec collarA (observation mode1 (n+2)) +
      Matrix.mulVec collarB (observation mode1 (n+1)) +
      Matrix.mulVec collarC (observation mode1 n) = 0 := by
  have hr := rho_quad
  have hrC : (rho : ℂ)^2 = (5-Real.sqrt 2 : ℂ)*(rho : ℂ)-1 := by exact_mod_cast hr
  have hs2C : (Real.sqrt 2 : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num
  have hz := rho_ne_zero
  have hp := phase_sq
  funext i
  fin_cases i <;>
    simp [collarA, collarB, collarC, observation, mode1, phase,
      dotProduct, Fin.sum_univ_succ] <;>
    field_simp [hz] <;>
    ring_nf <;>
    norm_num [hrC, hs2C, hp, Complex.I_mul_I] <;>
    ring_nf <;>
    rw [hs2C] <;>
    ring

/-- Both dominant sparse modes satisfy the displayed constant-coefficient recurrence. -/
theorem dominant_recurrence :
    (∀ n : ℕ, Matrix.mulVec collarA (observation mode0 (n+2)) +
      Matrix.mulVec collarB (observation mode0 (n+1)) +
      Matrix.mulVec collarC (observation mode0 n) = 0) ∧
    (∀ n : ℕ, Matrix.mulVec collarA (observation mode1 (n+2)) +
      Matrix.mulVec collarB (observation mode1 (n+1)) +
      Matrix.mulVec collarC (observation mode1 n) = 0) :=
  ⟨dominant_mode0_recurrence, dominant_mode1_recurrence⟩

/-- Recurrence, invertible transfer and exact dominant eigenpairs. -/
theorem collar_dictionary :
    (dominantTransfer * dominantTransferInverse = 1 ∧
      dominantTransferInverse * dominantTransfer = 1) ∧
    (Matrix.mulVec dominantTransfer (forward mode0) = (rho : ℂ) • forward mode0 ∧
      Matrix.mulVec dominantTransfer (forward mode1) = (rho : ℂ) • forward mode1 ∧
      Matrix.mulVec dominantTransfer (backward mode0) = (1/rho : ℂ) • backward mode0 ∧
      Matrix.mulVec dominantTransfer (backward mode1) = (1/rho : ℂ) • backward mode1) ∧
    (∀ n : ℕ, Matrix.mulVec collarA (observation mode0 (n+2)) +
      Matrix.mulVec collarB (observation mode0 (n+1)) +
      Matrix.mulVec collarC (observation mode0 n) = 0) ∧
    (∀ n : ℕ, Matrix.mulVec collarA (observation mode1 (n+2)) +
      Matrix.mulVec collarB (observation mode1 (n+1)) +
      Matrix.mulVec collarC (observation mode1 n) = 0) :=
  ⟨transfer_inverse, dominant_eigenpairs, dominant_recurrence⟩

#print axioms collarA
#print axioms collarB
#print axioms collarC
#print axioms dominantTransferInverse
#print axioms transfer_inverse
#print axioms observation
#print axioms dominant_mode0_recurrence
#print axioms dominant_mode1_recurrence
#print axioms dominant_recurrence
#print axioms collar_dictionary
'''

if __name__=='__main__':
    ar,br,cr,T,Ti=build()
    declarations = matrix_decl('collarA',ar) + matrix_decl('collarB',br) + matrix_decl('collarC',cr)
    declarations += matrix_decl('dominantTransfer',T) + matrix_decl('dominantTransferInverse',Ti)
    text=HEADER+declarations+PROOFS.replace('#print axioms rho',EXTRA+'\n#print axioms rho',1)
    (H/'Collar.lean').write_text(text)
    shared=H.parents[1]/'shared/dictionary'
    shared.mkdir(parents=True,exist_ok=True)
    (shared/'R1_Collar.lean').write_text(text)
    print('wrote',H/'Collar.lean',shared/'R1_Collar.lean','lines',len(text.splitlines()))
