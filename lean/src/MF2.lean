import FE1c
import FE4b
import AdalyFormal.Balaban.WitnessInequality

/-!
# MF2 -- the FLAT side of the M0 route: Lemma 2.4 survives an L² perturbation, and Stokes holds on the whole torus for ANY fine field.

* `curl_pert`: `Σ_p ‖curl B₁‖² ≤ 2 Σ_p ‖curl B_f‖² + 64 Σ_b ‖B_f − B₁‖²` (any unit fields; tree `plaqEnergy_flatCurl_le`, constant 32).
* `flat_floor_pert`: for `B̃ ∈ Λ̃` (touching support, `Λ = B(Λ')`) and `B₁ = C₁ B̃` (FLAT `C`, `q1SU2`), and ANY unit field `B_f`:
  `(1/54) ℓ^{-5} ‖B̃‖² ≤ 2 Σ_p ‖curl B_f‖² + 64 Σ_b ‖B_f − B₁‖²`  (Lemma 2.4 `lemma24Su_sharp` + `Cop_props_gen`).
* `stokes_full`: for ANY fine field `x` on the fine torus `scaleUp ℓ k Lu`,
  `n Σ_q ‖curl (unitField (lineCoarseRestrictSuTwo n x)) q‖² ≤ Σ_p ‖curl x p‖²`, `n = ℓ^k` (no tower, no `Admissible`: the window
  hypothesis of `local_stokes_suTwo` is trivial for the whole torus).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M0Finish

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp OnLambdaTildeIn)
open AdalyFormal.StatementLane2 (OnLambdaT)
open AdalyFormal.StatementLaneG (LamBlockSum)
open AdalyFormal.IngredientFamilyR2 (H0 Cop)
open AdalyFormal.IngredientFamily (q1SU2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy plaqEnergy)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)

theorem sq_sub_le2 (u v : SuTwo) : ‖u - v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have h := norm_sub_le u v
  have h0 := norm_nonneg (u - v)
  nlinarith [sq_nonneg (‖u‖ - ‖v‖), norm_nonneg u, norm_nonneg v]

/-- curl energy of `B₁` from that of `B_f` and the bond energy of the difference. -/
theorem curl_pert {L : PeriodicLatticeExtent} (Bf B1 : Bond L → SuTwo) :
    ∑ p : PeriodicLatticePlaquette L, ‖flatCurlValue B1 p‖ ^ 2
      ≤ 2 * ∑ p : PeriodicLatticePlaquette L, ‖flatCurlValue Bf p‖ ^ 2
        + 64 * ∑ b : Bond L, ‖Bf b - B1 b‖ ^ 2 := by
  set d : Bond L → SuTwo := fun b => Bf b - B1 b with hd
  have hpt : ∀ p, flatCurlValue B1 p = flatCurlValue Bf p - flatCurlValue d p := by
    intro p; simp only [flatCurlValue, hd]; abel
  have h1 : ∑ p : PeriodicLatticePlaquette L, ‖flatCurlValue B1 p‖ ^ 2
      ≤ ∑ p : PeriodicLatticePlaquette L, (2 * ‖flatCurlValue Bf p‖ ^ 2 + 2 * ‖flatCurlValue d p‖ ^ 2) :=
    Finset.sum_le_sum (fun p _ => by rw [hpt p]; exact sq_sub_le2 _ _)
  have h2 : plaqEnergy (flatCurlValue d) ≤ 32 * bondEnergy d :=
    AdalyFormal.Balaban.WitnessInequality.plaqEnergy_flatCurl_le d
  unfold plaqEnergy bondEnergy at h2
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h1
  linarith

/-- **Lemma 2.4 under an L² perturbation** (flat `C`, every `ell ≥ 2`). -/
theorem flat_floor_pert {Lu : PeriodicLatticeExtent} {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ μ : Fin 3, ell < Lu μ + 1) (hd : ∀ μ, ell ∣ Lu μ + 1)
    {Lam : Set (PeriodicLatticeSite Lu)} (hLB : LamBlockSum ell Lam)
    (hb : Function.Bijective (H0 Lam (q1SU2 ell))) (Bt : Bond Lu → SuTwo)
    (hBt : OnLambdaTildeIn Lam ell Bt) (hBT : OnLambdaT Lam Bt) (Bf : Bond Lu → SuTwo) :
    (1 / 54 * (1 / (ell : ℝ) ^ 5)) * bondEnergy Bt
      ≤ 2 * ∑ p : PeriodicLatticePlaquette Lu, ‖flatCurlValue Bf p‖ ^ 2
        + 64 * ∑ b : Bond Lu, ‖Bf b - Cop Lam (q1SU2 ell) Bt b‖ ^ 2 := by
  have hell : 0 < ell := by omega
  have hu : ∀ μ, 1 ≤ Lu μ := fun μ => by have := hstrict μ; omega
  obtain ⟨hax, hker, hen, -⟩ := AdalyFormal.FlatEllGeneral.Cop_props_gen hell hd hu hLB hb Bt hBt hBT
  have h24 := AdalyFormal.FlatEllGeneral.lemma24Su_sharp hell2 hstrict hd
    (Cop Lam (q1SU2 ell) Bt) hax hker
  have hp := curl_pert Bf (Cop Lam (q1SU2 ell) Bt)
  have hγ : (0 : ℝ) ≤ 1 / 54 * (1 / (ell : ℝ) ^ 5) := by positivity
  have := mul_le_mul_of_nonneg_left hen hγ
  linarith

/-- **Stokes on the whole torus for ANY fine field** (`n = ℓ^k`). -/
theorem stokes_full {ell k : ℕ} (hell : 0 < ell) {Lu : PeriodicLatticeExtent} (hu : ∀ ρ, 1 ≤ Lu ρ)
    (x : Bond (scaleUp ell k Lu) → SuTwo) :
    ((ell ^ k : ℕ) : ℝ) * ∑ q : PeriodicLatticePlaquette Lu,
        ‖flatCurlValue (AdalyFormal.GenuineU1.unitField ell k Lu hell (lineCoarseRestrictSuTwo (ell ^ k) x)) q‖ ^ 2
      ≤ ∑ p : PeriodicLatticePlaquette (scaleUp ell k Lu), ‖flatCurlValue x p‖ ^ 2 := by
  classical
  have hre : ∀ q : PeriodicLatticePlaquette Lu,
      flatCurlValue (AdalyFormal.GenuineU1.unitField ell k Lu hell (lineCoarseRestrictSuTwo (ell ^ k) x)) q
        = AdalyFormal.Balaban.ThirdLevelStokes.coarseCurlSuTwo (AdalyFormal.GenuineU1.scaleUp_tiling ell k Lu hell)
            (lineCoarseRestrictSuTwo (ell ^ k) x) (AdalyFormal.GenuineU1.plaqE ell k Lu hell q) :=
    fun q => AdalyFormal.GenuineU1.curl_reindex ell k Lu hell hu _ q
  have hsum : ∑ q : PeriodicLatticePlaquette Lu,
        ‖flatCurlValue (AdalyFormal.GenuineU1.unitField ell k Lu hell (lineCoarseRestrictSuTwo (ell ^ k) x)) q‖ ^ 2
      = ∑ p : AdalyFormal.Balaban.CoarseCurl.CoarsePlaquette (scaleUp ell k Lu) (ell ^ k),
          ‖AdalyFormal.Balaban.ThirdLevelStokes.coarseCurlSuTwo (AdalyFormal.GenuineU1.scaleUp_tiling ell k Lu hell)
            (lineCoarseRestrictSuTwo (ell ^ k) x) p‖ ^ 2 := by
    rw [← (AdalyFormal.GenuineU1.plaqE ell k Lu hell).sum_comp]
    exact Finset.sum_congr rfl (fun q _ => by rw [hre q])
  rw [hsum]
  have h := AdalyFormal.FlatEllGeneral.local_stokes_suTwo (pow_pos hell k)
    (AdalyFormal.GenuineU1.scaleUp_tiling ell k Lu hell) x Finset.univ Finset.univ
    (fun _ _ _ _ _ _ _ _ => Finset.mem_univ _)
  push_cast at h ⊢
  exact h

#print axioms sq_sub_le2
#print axioms curl_pert
#print axioms flat_floor_pert
#print axioms stokes_full

end AdalyFormal.M0Finish
