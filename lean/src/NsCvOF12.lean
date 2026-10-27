import NsCvOF11
import NsCvOK7
import NsCvOG9

/-!
# CvOF12 -- generic facts for the assembly: `c0 > 0`, `cLoc >= -1`, saddle existence on an affine subspace (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open Finset
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverNested
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoInner (hsInner hsInner_self_nonneg hsInner_self_eq_zero)

theorem c0_pos : 0 < c0 := by
  unfold c0
  have h0 := hsInner_self_nonneg (dgS 1)
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    have hz : dgS 1 = 0 := hsInner_self_eq_zero h.symm
    have := congrArg (fun X : SuTwo => (X : M2) 0 0) hz
    simp only [dgS_coe, dg] at this
    simp at this

theorem cLoc_ge (k : ℕ) : -1 ≤ cLoc (k + 2) := by
  unfold cLoc
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  push_cast
  have h1 : 0 < ((k : ℝ) + 2 - 1) * ((k : ℝ) + 2 + 4) := by nlinarith
  rw [le_div_iff₀ h1]
  nlinarith

/-- **saddle existence**: on a finite-dimensional space, if the symmetric form `BF C c` is positive definite on `V`, then every affine
space `f₀ + V` contains a (unique) saddle `e`: `BF C c e d = 0` for all `d ∈ V`. -/
theorem exists_saddle {n : ℕ} (C : ℕ) (c : ℝ) (V : Submodule ℝ (Fin n → ℝ))
    (hpos : ∀ d ∈ V, d ≠ 0 → 0 < qF C c d) (f₀ : Fin n → ℝ) :
    ∃ e : Fin n → ℝ, e - f₀ ∈ V ∧ ∀ d ∈ V, BF C c e d = 0 := by
  let B : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun w d => BF C c w d) (fun w w' d => BF_add_left C c w w' d)
      (fun r w d => BF_smul_left C c r w d) (fun w d d' => BF_add_right C c w d d')
      (fun r w d => BF_smul_right C c r w d)
  let Φ : V →ₗ[ℝ] Module.Dual ℝ V := (B.compl₁₂ V.subtype V.subtype)
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hne
    have hw0 : (w : Fin n → ℝ) ≠ 0 := fun h => hne (Subtype.ext h)
    have h1 := LinearMap.congr_fun hw w
    have h2 : BF C c (w : Fin n → ℝ) (w : Fin n → ℝ) = 0 := h1
    rw [BF_self] at h2
    exact absurd h2 (ne_of_gt (hpos _ w.2 hw0))
  have hdim : Module.finrank ℝ V = Module.finrank ℝ (Module.Dual ℝ V) := (Subspace.dual_finrank_eq).symm
  have hsurj : Function.Surjective Φ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  let φ : Module.Dual ℝ V := -((B f₀).comp V.subtype)
  obtain ⟨w, hw⟩ := hsurj φ
  refine ⟨f₀ + (w : Fin n → ℝ), by simp, fun d hd => ?_⟩
  have h1 := LinearMap.congr_fun hw ⟨d, hd⟩
  have h2 : BF C c (w : Fin n → ℝ) d = - BF C c f₀ d := h1
  rw [BF_add_left, h2]; ring


/-- `cs` is a first crossing of the Z-chain form of the nested instance. -/
def IsCrossingN (ell M R : ℕ) (cs : ℝ) : Prop :=
  cs < 1 ∧ (∃ es : Fin (nN ell M R) → ℝ, es ∈ Vsub (rowOfN ell M R) ∧ es ≠ 0 ∧ qF (neC ell M R - neP0 ell M R) cs es = 0) ∧
  (∀ e : Fin (nN ell M R) → ℝ, e ∈ Vsub (rowOfN ell M R) → 0 ≤ qF (neC ell M R - neP0 ell M R) cs e) ∧
  (∀ c : ℝ, cs < c → c ≤ 1 → ∀ e : Fin (nN ell M R) → ℝ, e ∈ Vsub (rowOfN ell M R) → e ≠ 0 → 0 < qF (neC ell M R - neP0 ell M R) c e)

/-- the first crossing is unique. -/
theorem crossing_unique {ell M R : ℕ} {c1 c2 : ℝ} (h1 : IsCrossingN ell M R c1) (h2 : IsCrossingN ell M R c2) : c1 = c2 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hlt := h2.1
    obtain ⟨_, ⟨es, hes, hne0, hq⟩, _, _⟩ := h2
    have := h1.2.2.2 c2 h hlt.le es hes hne0
    linarith
  · have hlt := h1.1
    obtain ⟨_, ⟨es, hes, hne0, hq⟩, _, _⟩ := h1
    have := h2.2.2.2 c1 h hlt.le es hes hne0
    linarith

#print axioms crossing_unique

#print axioms c0_pos
#print axioms cLoc_ge
#print axioms exists_saddle

end AdalyFormal.CoverOmega
