import DLR27

/-!
# DL28 -- locality of the FIRST-ORDER JETS: the one-step jet and the level-`j` composite `Q_j(U)`

* `restrX P` : restriction of a coordinate field to the edges with property `P` (a CLM).
* **`QlinStepX_row_local`** : on a regular background, the row `c` of `D qStepX(0)` vanishes on fields vanishing on
  `VisStep c` (proof: `qStepX(·)(c) = qStepX(restr ·)(c)` (DL27) + uniqueness of the Fréchet derivative).
* `Foot ell j c e` : the level-`j` footprint (`Foot 0 c = {c}`, `Foot (j+1) c = ⋃_{e' ∈ VisStep(ℓ^j) c} Foot j e'`).
* **`QlinCompX_row_local`** : under `RegTower ell bg J`, for `j ≤ J` the row `c` of `QlinCompX ell bg j` vanishes on fields
  vanishing on `Foot ell j c` (induction through the chain rule `QlinCompX_succ`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp (SU2)

variable {L : PeriodicLatticeExtent}

open Classical in
/-- restriction of a coordinate field to the edges with property `P` -/
noncomputable def restrX (P : PeriodicLatticeEdge L → Prop) : XS L →L[ℝ] XS L :=
  ContinuousLinearMap.pi (fun e => if P e then ContinuousLinearMap.proj e else 0)

open Classical in
theorem restrX_apply (P : PeriodicLatticeEdge L → Prop) (a : XS L) (e : PeriodicLatticeEdge L) :
    restrX P a e = if P e then a e else 0 := by
  unfold restrX
  rw [ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl

theorem restrX_eq_on (P : PeriodicLatticeEdge L → Prop) (a : XS L) (e : PeriodicLatticeEdge L) (he : P e) :
    restrX P a e = a e := by
  classical
  rw [restrX_apply, if_pos he]

theorem restrX_zero_of (P : PeriodicLatticeEdge L → Prop) (a : XS L) (h : ∀ e, P e → a e = 0) : restrX P a = 0 := by
  classical
  funext e
  rw [restrX_apply]
  split_ifs with he
  · exact h e he
  · rfl

/-- **row locality of the one-step jet** -/
theorem QlinStepX_row_local (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (hreg : RegBg s ell V0)
    (c : PeriodicLatticeEdge L) (a : XS L) (ha : ∀ e, VisStep s ell c e → a e = 0) :
    QlinStepX s ell V0 a c = 0 := by
  set R := restrX (VisStep s ell c) with hR
  have hdiff : DifferentiableAt ℝ (qStepX s ell V0) 0 :=
    (qStepX_contDiffAt s ell V0 hreg).differentiableAt (by simp)
  have hf : HasFDerivAt (qStepX s ell V0) (QlinStepX s ell V0) 0 := hdiff.hasFDerivAt
  have hR0 : R 0 = 0 := map_zero R
  have hfR : HasFDerivAt (qStepX s ell V0 ∘ R) (QlinStepX s ell V0 ∘L R) 0 := by
    have hf' : HasFDerivAt (qStepX s ell V0) (QlinStepX s ell V0) (R 0) := by rw [hR0]; exact hf
    exact hf'.comp (0 : XS L) R.hasFDerivAt
  have hp := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) c).hasFDerivAt
    (x := qStepX s ell V0 0)
  have h1 : HasFDerivAt (fun b => qStepX s ell V0 b c)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) c) ∘L QlinStepX s ell V0) 0 :=
    hp.comp (0 : XS L) hf
  have hpR := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) c).hasFDerivAt
    (x := (qStepX s ell V0 ∘ R) 0)
  have h2' : HasFDerivAt (fun b => (qStepX s ell V0 ∘ R) b c)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) c)
        ∘L (QlinStepX s ell V0 ∘L R)) 0 :=
    hpR.comp (0 : XS L) hfR
  have hfun : (fun b => (qStepX s ell V0 ∘ R) b c) = (fun b => qStepX s ell V0 b c) := by
    funext b
    show qStepX s ell V0 (R b) c = qStepX s ell V0 b c
    exact qStepX_congr s ell V0 (R b) b c (fun e he => restrX_eq_on _ b e he)
  rw [hfun] at h2'
  have hu := h1.unique h2'
  have h3 := congrArg (fun T : XS L →L[ℝ] (Fin 3 → ℝ) => T a) hu
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at h3
  rw [h3, hR, restrX_zero_of _ a ha, map_zero]
  rfl

/-- the level-`j` footprint of the composite jet -/
def Foot (ell : ℕ) : ℕ → PeriodicLatticeEdge L → PeriodicLatticeEdge L → Prop
  | 0, c, e => e = c
  | j + 1, c, e => ∃ e', VisStep (ell ^ j) ell c e' ∧ Foot ell j e' e

theorem QlinCompX_zero_apply' (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (a : XS L) :
    QlinCompX ell bg 0 a = a := by
  simp [QlinCompX, qCompX]

/-- **row locality of the composite jet `L^j Q_j(U)`** -/
theorem QlinCompX_row_local (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (J : ℕ)
    (hreg : RegTower ell bg J) : ∀ j, j ≤ J → ∀ (c : PeriodicLatticeEdge L) (a : XS L),
      (∀ e, Foot ell j c e → a e = 0) → QlinCompX ell bg j a c = 0 := by
  intro j
  induction j with
  | zero =>
      intro _ c a ha
      rw [QlinCompX_zero_apply']
      exact ha c rfl
  | succ j ih =>
      intro hj c a ha
      rw [QlinCompX_succ ell bg J hreg j (by omega), ContinuousLinearMap.comp_apply]
      refine QlinStepX_row_local (ell ^ j) ell (bg j) (hreg j (by omega)) c _ (fun e' he' => ?_)
      exact ih (by omega) e' a (fun e he => ha e ⟨e', he', he⟩)

#print axioms restrX_apply
#print axioms restrX_eq_on
#print axioms restrX_zero_of
#print axioms QlinStepX_row_local
#print axioms QlinCompX_zero_apply'
#print axioms QlinCompX_row_local

end AdalyFormal.DLayer
