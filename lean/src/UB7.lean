import UB6

/-!
# UB7 -- U1 `stokes_U1`: the summed per-plaquette-chart covariant Stokes inequality (lane m2_unit_20261014)

For a finite set `Qs` of good unit plaquettes, each with ITS OWN fine chart (`ChartOK`, uniform constants):
  `n Σ_{q∈Qs} ‖curl_W B q‖² ≤ (1+ε')(2 Xbox + 64 (s/n)² ‖y‖²) + (1+1/ε')(64 κ² n ‖B‖² + 7776·8 n⁻² δ² ‖y‖²)`,
`Xbox = Σ_{p ∈ plaqIn Ω_k} ‖curl_U y p‖²`, `δ = delLoc ℓ ε k`, provided `Q_U y = τ* B`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.M2Unit

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.GenuineU1 (plaqE)
open AdalyFormal.FlatEllGeneral (InBox)
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.TowerLoc (delLoc)

open Classical in
theorem stokes_U1 {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell2 : 2 ≤ ell) (hu : ∀ μ, 1 ≤ Lu μ)
    (S : Tower (scaleUp ell k Lu)) (hS : Admissible ell M R k S)
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (W : PeriodicLinkConfiguration SU2 Lu) (y : BondFnL2 (scaleUp ell k Lu)) (B : BondFnL2 Lu)
    (hQ : (bondSectorOf (geomOf ell k S) U).Qfull y
      = ContinuousLinearMap.adjoint (gparams ell k Lu (by omega) S U a Lam).tau B)
    (Qs : Finset (PeriodicLatticePlaquette Lu)) (γ : PeriodicLatticePlaquette Lu → GaugeFn (scaleUp ell k Lu))
    (Wr : PeriodicLatticePlaquette Lu → ℕ → Set (PeriodicLatticeSite (scaleUp ell k Lu)))
    (s κ ε' : ℝ) (ε : ℕ → ℝ) (hs : 0 ≤ s) (hκ : 0 ≤ κ) (hε' : 0 < ε')
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (hr : ∀ j, j < k → Real.pi / 2 * ((loopFactorBound ell : ℝ) * ε j) < r0)
    (hC : ∀ q ∈ Qs, ChartOK (by omega) S U W q (γ q) s κ ε (Wr q))
    (hgood : ∀ q ∈ Qs, ∀ c, InBox q.1 c → embY ell k Lu (by omega) c ∈ S.Om k) :
    (ell : ℝ) ^ k * ∑ q ∈ Qs, ‖curlValueCovariant W (WithLp.ofLp B) q‖ ^ 2
      ≤ (1 + ε') * (2 * ∑ p ∈ (Finset.univ : Finset (PeriodicLatticePlaquette (scaleUp ell k Lu))).filter
              (fun p => p ∈ plaqIn (S.Om k)), ‖curlValueCovariant U (WithLp.ofLp y) p‖ ^ 2
            + 64 * (s / (ell : ℝ) ^ k) ^ 2 * ‖y‖ ^ 2)
        + (1 + 1 / ε') * (64 * κ ^ 2 * (ell : ℝ) ^ k * ‖B‖ ^ 2
            + 8 * 7776 * (1 / ((ell : ℝ) ^ k) ^ 2) * delLoc ell ε (Fin.last k) ^ 2 * ‖y‖ ^ 2) := by
  have hell : 0 < ell := by omega
  set n : ℕ := ell ^ k with hn
  have hnpos : 0 < n := pow_pos hell k
  have hnR : ((n : ℕ) : ℝ) = (ell : ℝ) ^ k := by rw [hn]; push_cast; ring
  have hnR0 : (0 : ℝ) < (ell : ℝ) ^ k := by rw [← hnR]; exact_mod_cast hnpos
  set σ := s / (ell : ℝ) ^ k with hσ
  set G := Gwin U (WithLp.ofLp y) σ with hG
  set δ := delLoc ell ε (Fin.last k) with hδ
  set Pq := (Finset.univ : Finset (PeriodicLatticePlaquette (scaleUp ell k Lu))).filter (fun p => p ∈ plaqIn (S.Om k))
    with hPq
  -- per plaquette
  have hpq : ∀ q ∈ Qs, (ell : ℝ) ^ k * ‖curlValueCovariant W (WithLp.ofLp B) q‖ ^ 2
      ≤ (1 + ε') * ((1 / ((ell : ℝ) ^ k) ^ 2) * winSum n G (plaqE ell k Lu hell q))
        + (1 + 1 / ε') * (16 * κ ^ 2 * (ell : ℝ) ^ k * (‖(WithLp.ofLp B) (qb2 q)‖ ^ 2 + ‖(WithLp.ofLp B) (qb3 q)‖ ^ 2)
          + 8 * (1 / ((ell : ℝ) ^ k) ^ 2) * δ ^ 2 *
            (footT hell y (qb1 q) + footT hell y (qb2 q) + footT hell y (qb3 q) + footT hell y (qb4 q))) :=
    fun q hq => stokes_q hell hu S U a Lam W y B hQ q (γ q) s κ ε' ε (Wr q) hs hκ hε' hε0 hsm hr (hC q hq)
  have hsum := Finset.sum_le_sum hpq
  rw [← Finset.mul_sum] at hsum
  -- (i) windows
  have hwin : ∑ q ∈ Qs, winSum n G (plaqE ell k Lu hell q) ≤ (n : ℝ) ^ 2 * ∑ z ∈ Pq, G z := by
    have hmap : ∑ q ∈ Qs, winSum n G (plaqE ell k Lu hell q) = ∑ p ∈ Qs.map (plaqE ell k Lu hell).toEmbedding, winSum n G p := by
      rw [Finset.sum_map]; rfl
    rw [hmap]
    refine winSum_count hnpos G (Gwin_nonneg U _ σ) _ Pq ?_
    intro p hp x hx i hi j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact AdalyFormal.FlatEllGeneral.window_plaqIn_k hell hu hS q.1 (hgood q hq) q.2 x hx i j
      (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
  -- (ii) the window integrand
  have hG : ∑ z ∈ Pq, G z ≤ 2 * ∑ p ∈ Pq, ‖curlValueCovariant U (WithLp.ofLp y) p‖ ^ 2 + 64 * σ ^ 2 * ‖y‖ ^ 2 := by
    have e : ∑ z ∈ Pq, G z = 2 * ∑ p ∈ Pq, ‖curlValueCovariant U (WithLp.ofLp y) p‖ ^ 2
        + 16 * σ ^ 2 * ∑ z ∈ Pq, (‖(WithLp.ofLp y) (periodicLatticeShift z.1 z.2.1.1, z.2.1.2)‖ ^ 2
          + ‖(WithLp.ofLp y) (periodicLatticeShift z.1 z.2.1.2, z.2.1.1)‖ ^ 2) := by
      rw [hG]; unfold Gwin
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [e]
    have hsub : ∑ z ∈ Pq, (‖(WithLp.ofLp y) (periodicLatticeShift z.1 z.2.1.1, z.2.1.2)‖ ^ 2
          + ‖(WithLp.ofLp y) (periodicLatticeShift z.1 z.2.1.2, z.2.1.1)‖ ^ 2)
        ≤ ∑ z : PeriodicLatticePlaquette (scaleUp ell k Lu), (‖(WithLp.ofLp y) (periodicLatticeShift z.1 z.2.1.1, z.2.1.2)‖ ^ 2
          + ‖(WithLp.ofLp y) (periodicLatticeShift z.1 z.2.1.2, z.2.1.1)‖ ^ 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun z _ _ => by positivity)
    have hsplit : ∑ z : PeriodicLatticePlaquette (scaleUp ell k Lu),
          (‖(WithLp.ofLp y) (periodicLatticeShift z.1 z.2.1.1, z.2.1.2)‖ ^ 2
            + ‖(WithLp.ofLp y) (periodicLatticeShift z.1 z.2.1.2, z.2.1.1)‖ ^ 2)
        = ∑ z : PeriodicLatticePlaquette (scaleUp ell k Lu), ‖(WithLp.ofLp y) (periodicLatticeShift z.1 z.2.1.1, z.2.1.2)‖ ^ 2
          + ∑ z : PeriodicLatticePlaquette (scaleUp ell k Lu), ‖(WithLp.ofLp y) (periodicLatticeShift z.1 z.2.1.2, z.2.1.1)‖ ^ 2 :=
      Finset.sum_add_distrib
    rw [hsplit] at hsub
    have n1 := AdalyFormal.Balaban.RegularUPerturbation.sum_nbr1_sq_le (WithLp.ofLp y)
    have n2 := AdalyFormal.Balaban.RegularUPerturbation.sum_nbr2_sq_le (WithLp.ofLp y)
    have hbe : bondEnergy (WithLp.ofLp y) = ‖y‖ ^ 2 := by unfold bondEnergy; rw [PiLp.norm_sq_eq_of_L2]
    rw [hbe] at n1 n2
    have hσ0 : 0 ≤ 16 * σ ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left (hsub.trans (add_le_add n1 n2)) hσ0
    nlinarith
  -- (iii) the unit drift term
  have hB2 : ∑ q ∈ Qs, (‖(WithLp.ofLp B) (qb2 q)‖ ^ 2 + ‖(WithLp.ofLp B) (qb3 q)‖ ^ 2) ≤ 4 * ‖B‖ ^ 2 := by
    have hsub : ∑ q ∈ Qs, (‖(WithLp.ofLp B) (qb2 q)‖ ^ 2 + ‖(WithLp.ofLp B) (qb3 q)‖ ^ 2)
        ≤ ∑ q : PeriodicLatticePlaquette Lu, (‖(WithLp.ofLp B) (qb2 q)‖ ^ 2 + ‖(WithLp.ofLp B) (qb3 q)‖ ^ 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun z _ _ => by positivity)
    have hsplit : ∑ q : PeriodicLatticePlaquette Lu, (‖(WithLp.ofLp B) (qb2 q)‖ ^ 2 + ‖(WithLp.ofLp B) (qb3 q)‖ ^ 2)
        = ∑ q : PeriodicLatticePlaquette Lu, ‖(WithLp.ofLp B) (qb2 q)‖ ^ 2
          + ∑ q : PeriodicLatticePlaquette Lu, ‖(WithLp.ofLp B) (qb3 q)‖ ^ 2 := Finset.sum_add_distrib
    rw [hsplit] at hsub
    have n1 := AdalyFormal.Balaban.RegularUPerturbation.sum_nbr1_sq_le (WithLp.ofLp B)
    have n2 := AdalyFormal.Balaban.RegularUPerturbation.sum_nbr2_sq_le (WithLp.ofLp B)
    have hbe : bondEnergy (WithLp.ofLp B) = ‖B‖ ^ 2 := by unfold bondEnergy; rw [PiLp.norm_sq_eq_of_L2]
    rw [hbe] at n1 n2
    have e2 : ∑ q : PeriodicLatticePlaquette Lu, ‖(WithLp.ofLp B) (qb2 q)‖ ^ 2
        = ∑ p : PeriodicLatticePlaquette Lu, ‖(WithLp.ofLp B) (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ ^ 2 := rfl
    have e3 : ∑ q : PeriodicLatticePlaquette Lu, ‖(WithLp.ofLp B) (qb3 q)‖ ^ 2
        = ∑ p : PeriodicLatticePlaquette Lu, ‖(WithLp.ofLp B) (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ ^ 2 := rfl
    rw [e2, e3] at hsub
    linarith
  -- (iv) the footprints
  have hF : ∑ q ∈ Qs, (footT hell y (qb1 q) + footT hell y (qb2 q) + footT hell y (qb3 q) + footT hell y (qb4 q))
      ≤ 7776 * ‖y‖ ^ 2 := by
    have hf0 : ∀ b, 0 ≤ footT hell y b := fun b => sq_nonneg _
    have f1 := sum_pos_le qb1 qb_inj1 (footT hell y) hf0 Qs
    have f2 := sum_pos_le qb2 qb_inj2 (footT hell y) hf0 Qs
    have f3 := sum_pos_le qb3 qb_inj3 (footT hell y) hf0 Qs
    have f4 := sum_pos_le qb4 qb_inj4 (footT hell y) hf0 Qs
    have ft := sum_footT_le hell2 y
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    linarith
  -- assemble
  have hε1 : 0 ≤ 1 + 1 / ε' := by positivity
  have hε0' : 0 ≤ 1 + ε' := by linarith
  have hfirst : ∑ q ∈ Qs, (1 + ε') * ((1 / ((ell : ℝ) ^ k) ^ 2) * winSum n G (plaqE ell k Lu hell q))
      ≤ (1 + ε') * (2 * ∑ p ∈ Pq, ‖curlValueCovariant U (WithLp.ofLp y) p‖ ^ 2 + 64 * σ ^ 2 * ‖y‖ ^ 2) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hε0'
    have h1 := mul_le_mul_of_nonneg_left (hwin.trans (mul_le_mul_of_nonneg_left hG (by positivity)))
      (by positivity : (0 : ℝ) ≤ 1 / ((ell : ℝ) ^ k) ^ 2)
    rw [hnR] at h1
    have e : 1 / ((ell : ℝ) ^ k) ^ 2 * (((ell : ℝ) ^ k) ^ 2
        * (2 * ∑ p ∈ Pq, ‖curlValueCovariant U (WithLp.ofLp y) p‖ ^ 2 + 64 * σ ^ 2 * ‖y‖ ^ 2))
        = 2 * ∑ p ∈ Pq, ‖curlValueCovariant U (WithLp.ofLp y) p‖ ^ 2 + 64 * σ ^ 2 * ‖y‖ ^ 2 := by
      field_simp
    linarith
  have hsecond : ∑ q ∈ Qs, (1 + 1 / ε') * (16 * κ ^ 2 * (ell : ℝ) ^ k
        * (‖(WithLp.ofLp B) (qb2 q)‖ ^ 2 + ‖(WithLp.ofLp B) (qb3 q)‖ ^ 2)
          + 8 * (1 / ((ell : ℝ) ^ k) ^ 2) * δ ^ 2 *
            (footT hell y (qb1 q) + footT hell y (qb2 q) + footT hell y (qb3 q) + footT hell y (qb4 q)))
      ≤ (1 + 1 / ε') * (64 * κ ^ 2 * (ell : ℝ) ^ k * ‖B‖ ^ 2
            + 8 * 7776 * (1 / ((ell : ℝ) ^ k) ^ 2) * δ ^ 2 * ‖y‖ ^ 2) := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hε1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have c1 : (0 : ℝ) ≤ 16 * κ ^ 2 * (ell : ℝ) ^ k := by positivity
    have c2 : (0 : ℝ) ≤ 8 * (1 / ((ell : ℝ) ^ k) ^ 2) * δ ^ 2 := by positivity
    have t1 := mul_le_mul_of_nonneg_left hB2 c1
    have t2 := mul_le_mul_of_nonneg_left hF c2
    nlinarith
  rw [Finset.sum_add_distrib] at hsum
  linarith

end AdalyFormal.M2Unit

#print axioms AdalyFormal.M2Unit.stokes_U1
