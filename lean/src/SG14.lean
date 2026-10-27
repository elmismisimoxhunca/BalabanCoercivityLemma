import SG13

/-!
# SG14 -- the three field-level statements, conditional on `GoodTower` only (lane m2_fields123_20261015)

For `RemainingInputs` fields F1 `siteS1`, F2 `rowBound`, F3 `massComm` (exact `ClassFam` shape and constants of `m2_skeleton_20261015/src/SK1.lean`), the SAME statement with
the single extra hypothesis `GoodTower ell (ℓ^m) k S` (every anchor of level `≥ 1` has its `16 ℓ^j`-ball in the core of a class cube).
Everything else (`m₁ = 6`, `R₁`, `s`, the numeric windows, torus facts, the printed class `PerCubeRegular2`, `U = 1` off `ClassBond` NOT used) is proved.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
namespace AdalyFormal.M2F123

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.M2Skel
open AdalyFormal.M1IMS
open AdalyFormal.M1GaugeW4 (rhoT)
open AdalyFormal.TowerLoc (SstarM CMcStar)

theorem F1_of_good (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ClassFam ell Unit (fun _ _ _ => True) (fun M R k Lu _ S _ U α₀ =>
      GoodTower ell M k S → SiteS1 ell k S U a (csOf a (rhoT ell 12 M (alpha1 ell α₀)))) := by
  obtain ⟨s0, hs0, hwin⟩ := window ell hell
  refine ⟨6, fun m hm => ⟨max 26 (17 * ell), fun R hR => ⟨(), trivial, s0, hs0, ?_⟩⟩⟩
  intro k hk Lu α₀ hα hsα hT S hS Lam hLam U hcc hU1 hgood
  have hR26 : 26 ≤ R := le_trans (le_max_left _ _) hR
  have hM := pow_ge (ell := ell) hell hm
  have hM0 : 0 < ell ^ m := by omega
  have hell0 : 0 < ell := by omega
  obtain ⟨h5, hL⟩ := torus_facts (k := k) hell hm hT
  obtain ⟨ha1, hsm4, -, -⟩ := hwin (ell ^ m) α₀ hα.le (by exact_mod_cast hsα)
  have hRM : 18 ≤ R * ell ^ m := by nlinarith
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  exact siteS1_of_charts hell hS hRM (AdalyFormal.M1GaugeW4.hbig_of ell k Lu h5) hL hη hα.le ha1 hsm4 U
    (blockCharts hell hM0 hS hgood hL hα hη hcc.2) a ha

theorem F2_of_good (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ClassFam ell Unit (fun _ _ _ => True) (fun M R k Lu _ S _ U α₀ =>
      GoodTower ell M k S →
      RowBound ell k S U a (gamC ell a (rhoT ell 12 M (alpha1 ell α₀))
        (AdalyFormal.M1GaugeW4.epsXnum ell (R * M * ell) a (rhoT ell 12 M (alpha1 ell α₀))))) := by
  obtain ⟨s0, hs0, hwin⟩ := window ell hell
  obtain ⟨W₀, hW₀, ε1, hε1, a₁, ha₁, hN⟩ := AdalyFormal.M1W4Num.w4Num_exists ell hell a ha
  have hell0 : 0 < ell := by omega
  have hC : (0 : ℝ) < (ell : ℝ) ^ 3 := by positivity
  refine ⟨6, fun m hm => ⟨max (max 26 (17 * ell)) W₀, fun R hR => ⟨(), trivial, min s0 (a₁ / (2 * (ell : ℝ) ^ 3)),
    lt_min hs0 (by positivity), ?_⟩⟩⟩
  intro k hk Lu α₀ hα hsα hT S hS Lam hLam U hcc hU1 hgood
  have hR26 : 26 ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hRW : W₀ ≤ R := le_trans (le_max_right _ _) hR
  have hM := pow_ge (ell := ell) hell hm
  have hM0 : 0 < ell ^ m := by omega
  obtain ⟨h5, hL⟩ := torus_facts (k := k) hell hm hT
  have hs1 : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s0 := le_trans hsα (min_le_left _ _)
  have hs2 : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₁ / (2 * (ell : ℝ) ^ 3) := le_trans hsα (min_le_right _ _)
  obtain ⟨ha1, hsm4, -, -⟩ := hwin (ell ^ m) α₀ hα.le hs1
  have hRM : 18 ≤ R * ell ^ m := by nlinarith
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  have hR1 : 1 ≤ R := by omega
  have ha2 : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * (alpha1 ell α₀) ≤ a₁ := by
    unfold alpha1
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (ell : ℝ) ^ 3)).1 hs2
    nlinarith
  obtain ⟨-, -, hW4⟩ := hN (ell ^ m) R hM0 hRW (alpha1 ell α₀) (by unfold alpha1; positivity) ha2
  exact rowBound_of_charts hell hS hRM (AdalyFormal.M1GaugeW4.hbig_of ell k Lu h5) hL hR1 (by omega) hη hα.le ha1 hsm4 a ha ε1
    hW4 U (blockCharts hell hM0 hS hgood hL hα hη hcc.2)

theorem F3_of_good (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ClassFam ell Unit (fun _ _ _ => True) (fun M R k Lu _ S _ U α₀ =>
      GoodTower ell M k S →
      MassComm ell M k 1 5 S U a (CMcStar ell M 1 5 a (SstarM ell 12 M (alpha1 ell α₀)))) := by
  obtain ⟨s0, hs0, hwin⟩ := window ell hell
  refine ⟨6, fun m hm => ⟨max 26 (17 * ell), fun R hR => ⟨(), trivial, s0, hs0, ?_⟩⟩⟩
  intro k hk Lu α₀ hα hsα hT S hS Lam hLam U hcc hU1 hgood
  have hR26 : 26 ≤ R := le_trans (le_max_left _ _) hR
  have hR17 : 17 * ell ≤ R := le_trans (le_max_right _ _) hR
  have hM := pow_ge (ell := ell) hell hm
  have hM0 : 0 < ell ^ m := by omega
  have hell0 : 0 < ell := by omega
  obtain ⟨h5, hL⟩ := torus_facts (k := k) hell hm hT
  obtain ⟨ha1, hsm4, hsmA, hrr⟩ := hwin (ell ^ m) α₀ hα.le (by exact_mod_cast hsα)
  have hroom : 17 * ell ≤ R * ell ^ m := by nlinarith
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  exact massComm_of_charts hell hS hM0 (by omega) (by omega) hroom (fun μ => by have := h5 μ; omega) hη hα ha1 hsm4 hsmA hrr a ha.le U
    (rowCharts hell hM0 hS hgood hL hα hη hcc.2)

end AdalyFormal.M2F123

#print axioms AdalyFormal.M2F123.F1_of_good
#print axioms AdalyFormal.M2F123.F2_of_good
#print axioms AdalyFormal.M2F123.F3_of_good
