import NsCvOS14
import NsOdd12b
import NsCvOP16

/-!
# CvOS15 -- `gOf ≠ 0` for the nested staggered family, at EVERY `t` (lane omega/near2/struct)

`gOf_ne_zero`: general geometry with aligned, `Om0`-contained, pairwise disjoint `Λ_j`.
`neS_nested`: the nested slab tower is nested (`Om j ⊆ Om j'` for `j' ≤ j`), hence the hypotheses hold for `geomOf ell 2 (neS ell M R)`.
`gOf_PN_ne_zero`: `gOf (PN ell M R hell a t).G (PN ell M R hell a t).U ≠ 0` for every `t`;
`anUnits4_of_unitsFour_point`: `AnUnits4` from ONE point with the four units.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

namespace AdalyFormal.CoverOmega.Struct


set_option linter.unusedSectionVars false
variable [CfData]
open scoped RealInnerProductSpace
open Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.CoverNested
open AdalyFormal.CoverOmega
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG

variable {L : PeriodicLatticeExtent}

theorem gOf_ne_zero (G : TowerGeom L) (U : Cfg L) (hell : 0 < G.ell)
    (hal : ∀ j, ∀ y ∈ G.Lam j, ∀ μ, G.ell ^ j ∣ (y μ).val)
    (h0 : ∀ j, j ≤ G.k → ∀ y ∈ G.Lam j, y ∈ G.Om0)
    (hdisj : ∀ j j', j' < j → ∀ y, y ∈ G.Lam j → y ∈ G.Lam j' → False)
    (hout : ∃ x : PeriodicLatticeSite L, x ∉ G.Om0) : gOf G U ≠ 0 := by
  have hms := siteMask_symm (L := L) G.Om0
  have hmi := siteMask_idem (L := L) G.Om0
  have hLd : ∀ f, LmOf G U f = lapDir G U f + (f - siteMask G.Om0 f) := fun f => by simp [LmOf]
  have hl1 : ∀ f, siteMask G.Om0 (lapDir G U f) = lapDir G U f := fun f => by
    unfold lapDir
    simp only [ContinuousLinearMap.comp_apply]
    exact hmi _
  have hl2 : ∀ f, lapDir G U (siteMask G.Om0 f) = lapDir G U f := fun f => by
    unfold lapDir
    simp only [ContinuousLinearMap.comp_apply]
    rw [hmi]
  exact Gm_cdet_ne_of_cokernel (siteMask G.Om0) (lapDir G U) (LmOf G U) (Bq G U) hms hmi (LmOf_unit G U hout) hLd hl1 hl2
    (fun w hw => Bq_cokernel_trivial G U hell hal h0 hdisj w hw)

theorem geomOf_conds {Lf : PeriodicLatticeExtent} (ell k : ℕ) (S : Tower Lf)
    (hnest : ∀ j j', j' ≤ j → S.Om j ⊆ S.Om j') :
    (∀ j, ∀ y ∈ (geomOf ell k S).Lam j, ∀ μ, (geomOf ell k S).ell ^ j ∣ (y μ).val) ∧
    (∀ j, j ≤ (geomOf ell k S).k → ∀ y ∈ (geomOf ell k S).Lam j, y ∈ (geomOf ell k S).Om0) ∧
    (∀ j j', j' < j → ∀ y, y ∈ (geomOf ell k S).Lam j → y ∈ (geomOf ell k S).Lam j' → False) := by
  refine ⟨fun j y hy μ => hy.1 μ, fun j _ y hy => hnest j 0 (Nat.zero_le _) hy.2.1, ?_⟩
  intro j j' hlt y hy hy'
  exact hy'.2.2 (hnest j (j' + 1) (by omega) hy.2.1)

theorem neS_nested {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) :
    ∀ j j', j' ≤ j → (neS ell M R).Om j ⊆ (neS ell M R).Om j' := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin hell hM hR
  intro j j' hjj x hx
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ 3 ≤ j by omega) with rfl | rfl | rfl | h3
  · have : j' = 0 := by omega
    subst this; exact hx
  · rcases (show j' = 0 ∨ j' = 1 by omega) with rfl | rfl
    · rw [neS_om1] at hx; rw [neS_om0]
      simp only [neP0, neP1, neQ0, neQ1, neA', neB, neB', neA] at hx ⊢; omega
    · exact hx
  · rcases (show j' = 0 ∨ j' = 1 ∨ j' = 2 by omega) with rfl | rfl | rfl
    · rw [neS_om2] at hx; rw [neS_om0]
      simp only [neP0, neP1, neQ0, neQ1, neA', neB, neB', neA] at hx ⊢; omega
    · rw [neS_om2] at hx; rw [neS_om1]
      simp only [neP0, neP1, neQ0, neQ1, neA', neB, neB', neA] at hx ⊢; omega
    · exact hx
  · exact absurd hx (tw3_omHi j h3 x)

/-- **row independence at every `t`.** -/
theorem gOf_PN_ne_zero {ell M R : ℕ} (hell3 : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (hell : 0 < ell) (a t : ℝ) :
    gOf (PN ell M R hell a t).G (PN ell M R hell a t).U ≠ 0 := by
  obtain ⟨hal, h0, hdisj⟩ := geomOf_conds ell 2 (neS ell M R) (neS_nested hell3 hM hR)
  exact gOf_ne_zero _ _ hell hal h0 hdisj (out_nested hell3 hM hR hell a t)

#print axioms gOf_PN_ne_zero

/-- **`AnUnits4` from ONE point with the four units** (the structural half, complete). -/
theorem anUnits4_of_unitsFour_point {ell M R : ℕ} (hell3 : 3 ≤ ell) (hE : StagOK ell) (hdvd : ell ∣ M) (hM : 0 < M)
    (hR : 1 ≤ R) (hell : 0 < ell) {a : ℝ} (ha : 0 < a) (t0 : ℝ) (ht0 : |t0| < tcap ell)
    (hu : UnitsFour (PN ell M R hell a t0)) : AnUnits4 ell M R hell a :=
  anUnits4_of_point hell3 hE hdvd hM hR hell ha t0 ht0 (gOf_PN_ne_zero hell3 hM hR hell a t0) hu

#print axioms anUnits4_of_unitsFour_point


open AdalyFormal.NcwdhStrong

/-- **the refutation from points**: for `ell` with `StagOK ell` and `3 <= ell`, and `a > 0`, if for infinitely many `m` and for each infinitely many `R` there is a
parameter `t0` with `|t0| < tcap ell` at which the four units hold for the genuine family, then `P428Target8NCWDH` is false. -/
theorem not_WDH_of_unitsFour_points (ell : ℕ) (hell3 : 3 ≤ ell) (hE : StagOK ell) (a : ℝ) (ha : 0 < a)
    (h : ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ ∃ t0 : ℝ, |t0| < tcap ell ∧
      UnitsFour (PN ell (ell ^ m) R (by omega) a t0)) : FailEllC CfData.cf ell (by omega) a := by
  refine not_WDH_of_anUnits4 ell hell3 hE a ha (fun m₀ => ?_)
  obtain ⟨m, hm, hR⟩ := h (max m₀ 1)
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  refine ⟨m, le_trans (le_max_left _ _) hm, fun R₀ => ?_⟩
  obtain ⟨R, hRR, t0, ht0, hu⟩ := hR (max R₀ 1)
  have hM : 0 < ell ^ m := pow_pos (by omega) m
  have hdvd : ell ∣ ell ^ m := dvd_pow_self ell (by omega : m ≠ 0)
  exact ⟨R, le_trans (le_max_left _ _) hRR,
    pn_H0_good hell3 hE hdvd hM (le_trans (le_max_right _ _) hRR) a,
    anUnits4_of_unitsFour_point hell3 hE hdvd hM (le_trans (le_max_right _ _) hRR) (by omega) ha t0 ht0 hu⟩

#print axioms not_WDH_of_unitsFour_points

end AdalyFormal.CoverOmega.Struct
