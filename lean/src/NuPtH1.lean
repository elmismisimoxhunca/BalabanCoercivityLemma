import NuPtG3

/-!
# PtH1 -- potential of the curl-free kernel field, transverse constants vanish, the potential `g` and the bond relation (lane omega/near2/point)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverOmegaTwo
open AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

section pot
variable {L : PeriodicLatticeExtent}

theorem hodge_pot (A : BondFnL2 L)
    (h : curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) A = 0) :
    ∃ (φ : SiteL2 L) (c : Fin 3 → SuTwo), ∀ b : Bond L,
      A b = φ (periodicLatticeShift b.1 b.2) - φ b.1 + c b.2 := by
  obtain ⟨φ, c, hA⟩ := AdalyFormal.GenuineU1H.hodge_K2 A h
  refine ⟨φ, c, fun b => ?_⟩
  have := congrFun (congrArg WithLp.ofLp hA) b
  have e1 : (gradL2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) φ) b
      = φ (periodicLatticeShift b.1 b.2) - φ b.1 :=
    AdalyFormal.GenuineU1H.gradL2_flat_apply φ b
  have e2 : (AdalyFormal.GenuineU1H.constBond L c) b = c b.2 := rfl
  show A b = _
  simp only [PiLp.add_apply] at this
  rw [this]
  show (gradL2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) φ) b + (AdalyFormal.GenuineU1H.constBond L c) b = _
  rw [e1, e2]

/-- the potential with the linear `x₀` correction. -/
noncomputable def gpot (φ : SiteL2 L) (c0 : SuTwo) (a b c : ℕ) : SuTwo :=
  φ (mkS L a b c) + ((a : ℝ)) • c0

theorem c1_zero (A : BondFnL2 L) (φ : SiteL2 L) (c : Fin 3 → SuTwo)
    (hb : ∀ b : Bond L, A b = φ (periodicLatticeShift b.1 b.2) - φ b.1 + c b.2)
    (a0 b0 : ℕ) (hz : ∀ t, A (mkS L a0 t b0, 1) = 0) : c 1 = 0 := by
  have hs : ∀ t, A (mkS L a0 t b0, 1) = φ (mkS L a0 (t + 1) b0) - φ (mkS L a0 t b0) + c 1 := by
    intro t
    rw [hb]
    simp only [shift_mkS1]
  have hsum : ∑ t ∈ range (L 1 + 1), A (mkS L a0 t b0, 1) = 0 := Finset.sum_eq_zero (fun t _ => hz t)
  simp only [hs] at hsum
  rw [Finset.sum_add_distrib, Finset.sum_range_sub (fun t => φ (mkS L a0 t b0)) (L 1 + 1)] at hsum
  simp only [Finset.sum_const, Finset.card_range] at hsum
  have e : mkS L a0 (L 1 + 1) b0 = mkS L a0 0 b0 :=
    mkS_ext rfl (by simp) rfl
  rw [e, sub_self, zero_add] at hsum
  have hn : ((L 1 + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [← Nat.cast_smul_eq_nsmul ℝ] at hsum
  exact (smul_eq_zero.mp hsum).resolve_left hn

theorem c2_zero (A : BondFnL2 L) (φ : SiteL2 L) (c : Fin 3 → SuTwo)
    (hb : ∀ b : Bond L, A b = φ (periodicLatticeShift b.1 b.2) - φ b.1 + c b.2)
    (a0 b0 : ℕ) (hz : ∀ t, A (mkS L a0 b0 t, 2) = 0) : c 2 = 0 := by
  have hs : ∀ t, A (mkS L a0 b0 t, 2) = φ (mkS L a0 b0 (t + 1)) - φ (mkS L a0 b0 t) + c 2 := by
    intro t
    rw [hb]
    simp only [shift_mkS2]
  have hsum : ∑ t ∈ range (L 2 + 1), A (mkS L a0 b0 t, 2) = 0 := Finset.sum_eq_zero (fun t _ => hz t)
  simp only [hs] at hsum
  rw [Finset.sum_add_distrib, Finset.sum_range_sub (fun t => φ (mkS L a0 b0 t)) (L 2 + 1)] at hsum
  simp only [Finset.sum_const, Finset.card_range] at hsum
  have e : mkS L a0 b0 (L 2 + 1) = mkS L a0 b0 0 :=
    mkS_ext rfl rfl (by simp)
  rw [e, sub_self, zero_add] at hsum
  have hn : ((L 2 + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [← Nat.cast_smul_eq_nsmul ℝ] at hsum
  exact (smul_eq_zero.mp hsum).resolve_left hn

/-- the bond relation in terms of the corrected potential (transverse constants vanish). -/
theorem rel_g (A : BondFnL2 L) (φ : SiteL2 L) (c : Fin 3 → SuTwo)
    (hb : ∀ b : Bond L, A b = φ (periodicLatticeShift b.1 b.2) - φ b.1 + c b.2)
    (h1 : c 1 = 0) (h2 : c 2 = 0) :
    (∀ a b d, A (mkS L a b d, 0) = gpot φ (c 0) (a + 1) b d - gpot φ (c 0) a b d) ∧
    (∀ a b d, A (mkS L a b d, 1) = gpot φ (c 0) a (b + 1) d - gpot φ (c 0) a b d) ∧
    (∀ a b d, A (mkS L a b d, 2) = gpot φ (c 0) a b (d + 1) - gpot φ (c 0) a b d) := by
  refine ⟨fun a b d => ?_, fun a b d => ?_, fun a b d => ?_⟩
  · rw [hb]
    simp only [shift_mkS0, gpot]
    push_cast
    rw [add_smul, one_smul]
    abel
  · rw [hb]
    simp only [shift_mkS1, gpot, h1]
    abel
  · rw [hb]
    simp only [shift_mkS2, gpot, h2]
    abel

end pot

end AdalyFormal.CoverOmegaTwo
