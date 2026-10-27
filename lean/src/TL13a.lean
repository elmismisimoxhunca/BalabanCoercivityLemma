import TL12c

/-!
# TL13a -- descent calculus for abstract Hilbert spaces (needed for the subspace `E₀ = bondSupp`)
-/
set_option autoImplicit false
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace

section hcov
variable (D : Type) [Fintype D]

structure HCov (H Ht : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup Ht] [InnerProductSpace ℝ Ht] [FiniteDimensional ℝ Ht] where
  ell : H →L[ℝ] Ht
  rho : D → Ht →L[ℝ] Ht
  rho_ell : ∀ d, (rho d).comp ell = ell
  sum_rho : ∑ d, rho d = ell.comp (ContinuousLinearMap.adjoint ell)
  adj_ell_ell : (ContinuousLinearMap.adjoint ell).comp ell = (Fintype.card D : ℝ) • ContinuousLinearMap.id ℝ H
  rho_orth : ∀ d, (rho d).comp (ContinuousLinearMap.adjoint (rho d)) = ContinuousLinearMap.id ℝ Ht ∧
    (ContinuousLinearMap.adjoint (rho d)).comp (rho d) = ContinuousLinearMap.id ℝ Ht

end hcov

section hdesc
variable {D : Type} [Fintype D]
variable {H Ht K Kt M Mt : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup Ht] [InnerProductSpace ℝ Ht] [FiniteDimensional ℝ Ht]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  [NormedAddCommGroup Kt] [InnerProductSpace ℝ Kt] [FiniteDimensional ℝ Kt]
  [NormedAddCommGroup M] [InnerProductSpace ℝ M] [FiniteDimensional ℝ M]
  [NormedAddCommGroup Mt] [InnerProductSpace ℝ Mt] [FiniteDimensional ℝ Mt]

/-- fibre sum -/
noncomputable abbrev HCov.sig (c : HCov D H Ht) : Ht →L[ℝ] H := ContinuousLinearMap.adjoint c.ell

def HE1 (cX : HCov D H Ht) (cY : HCov D K Kt) (O : H →L[ℝ] K) (Ot : Ht →L[ℝ] Kt) : Prop :=
  Ot.comp cX.ell = cY.ell.comp O

def HE2 (cX : HCov D H Ht) (cY : HCov D K Kt) (O : H →L[ℝ] K) (Ot : Ht →L[ℝ] Kt) : Prop :=
  cY.sig.comp Ot = O.comp cX.sig

def HEqui (cX : HCov D H Ht) (cY : HCov D K Kt) (Ot : Ht →L[ℝ] Kt) : Prop :=
  ∀ d, Ot.comp (cX.rho d) = (cY.rho d).comp Ot

structure HDesc (cX : HCov D H Ht) (cY : HCov D K Kt) (O : H →L[ℝ] K) (Ot : Ht →L[ℝ] Kt) : Prop where
  e1 : HE1 cX cY O Ot
  e2 : HE2 cX cY O Ot
  equi : HEqui cX cY Ot

variable {cX : HCov D H Ht} {cY : HCov D K Kt} {cZ : HCov D M Mt}

theorem HDesc.comp {O1 : H →L[ℝ] K} {Ot1 : Ht →L[ℝ] Kt} {O2 : K →L[ℝ] M} {Ot2 : Kt →L[ℝ] Mt}
    (h1 : HDesc cX cY O1 Ot1) (h2 : HDesc cY cZ O2 Ot2) : HDesc cX cZ (O2.comp O1) (Ot2.comp Ot1) := by
  constructor
  · unfold HE1
    rw [ContinuousLinearMap.comp_assoc, h1.e1, ← ContinuousLinearMap.comp_assoc, h2.e1, ContinuousLinearMap.comp_assoc]
  · unfold HE2
    rw [← ContinuousLinearMap.comp_assoc, h2.e2, ContinuousLinearMap.comp_assoc, h1.e2, ContinuousLinearMap.comp_assoc]
  · intro d
    rw [ContinuousLinearMap.comp_assoc, h1.equi d, ← ContinuousLinearMap.comp_assoc, h2.equi d, ContinuousLinearMap.comp_assoc]

theorem HDesc.add {O O' : H →L[ℝ] K} {Ot Ot' : Ht →L[ℝ] Kt} (h : HDesc cX cY O Ot) (h' : HDesc cX cY O' Ot') :
    HDesc cX cY (O + O') (Ot + Ot') := by
  constructor
  · unfold HE1; rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, h.e1, h'.e1]
  · unfold HE2; rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp, h.e2, h'.e2]
  · intro d; rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, h.equi d, h'.equi d]

theorem HDesc.sub {O O' : H →L[ℝ] K} {Ot Ot' : Ht →L[ℝ] Kt} (h : HDesc cX cY O Ot) (h' : HDesc cX cY O' Ot') :
    HDesc cX cY (O - O') (Ot - Ot') := by
  constructor
  · unfold HE1; rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, h.e1, h'.e1]
  · unfold HE2; rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp, h.e2, h'.e2]
  · intro d; rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, h.equi d, h'.equi d]

theorem HDesc.smul {O : H →L[ℝ] K} {Ot : Ht →L[ℝ] Kt} (r : ℝ) (h : HDesc cX cY O Ot) : HDesc cX cY (r • O) (r • Ot) := by
  constructor
  · unfold HE1; rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, h.e1]
  · unfold HE2; rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, h.e2]
  · intro d; rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, h.equi d]

theorem HDesc.id : HDesc cX cX (ContinuousLinearMap.id ℝ H) (ContinuousLinearMap.id ℝ Ht) :=
  ⟨by unfold HE1; simp, by unfold HE2; simp, fun d => by simp⟩

theorem HDesc.zero : HDesc cX cY (0 : H →L[ℝ] K) (0 : Ht →L[ℝ] Kt) := ⟨by unfold HE1; simp, by unfold HE2; simp, fun d => by simp⟩

theorem HDesc.adjoint {O : H →L[ℝ] K} {Ot : Ht →L[ℝ] Kt} (h : HDesc cX cY O Ot) :
    HDesc cY cX (ContinuousLinearMap.adjoint O) (ContinuousLinearMap.adjoint Ot) := by
  constructor
  · unfold HE1
    have := congrArg ContinuousLinearMap.adjoint h.e2
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp] at this
    simpa [HCov.sig, ContinuousLinearMap.adjoint_adjoint] using this
  · unfold HE2
    have := congrArg ContinuousLinearMap.adjoint h.e1
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp] at this
    simpa [HCov.sig] using this
  · intro d
    ext1 f
    simp only [ContinuousLinearMap.comp_apply]
    obtain ⟨hPY, hPYs⟩ := cY.rho_orth d
    obtain ⟨hPX, hPXs⟩ := cX.rho_orth d
    have h' : ∀ g, ContinuousLinearMap.adjoint Ot (ContinuousLinearMap.adjoint (cY.rho d) g) =
        ContinuousLinearMap.adjoint (cX.rho d) (ContinuousLinearMap.adjoint Ot g) := by
      intro g
      have := congrArg ContinuousLinearMap.adjoint (h.equi d)
      rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp] at this
      exact (congrArg (fun T => T g) this).symm
    have h1 := h' (cY.rho d f)
    have e1 : ContinuousLinearMap.adjoint (cY.rho d) (cY.rho d f) = f := congrArg (fun T => T f) hPYs
    rw [e1] at h1
    have e2 := congrArg (fun T => T (ContinuousLinearMap.adjoint Ot (cY.rho d f))) hPX
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at e2
    rw [← h1] at e2
    exact e2.symm

end hdesc

end AdalyFormal.Thin
