import NMX2
import MX_NV

/-!
# NMX3 -- `nonvac_core_mix`: the NVC7 witness list for the MIXED class, with the "uses two factors" block (lane nonvac_mixed_20261017)

Layout of NMX1 (left component of width `w = R + ell q`, `f₁ ≤ w < f₂`), witness `k = 2` (the conclusion states `2 ≤ k`), torus `nvcLu M T`, the nonvac_c `Λ` and `B̃`, and the spike of nonvac_c (`Ufield` of a single
small bond field, curved, not pure gauge).  The class hypothesis is `ClassCoupledΦ ell M Φ`: coverage by cubes of factor `f₁ ∈ Φ` (`mx_covers`) and the printed
per-cube regularity at EVERY `f ∈ Φ` (`perCube_of_M1` of the `M1Regular` field `Ufield`, one application per factor).
Mixed block: the factors that cover `Ω₀` alone are exactly those `≤ w` (`mx_covers`, `mx_not_covers`); `f₁` covers (sites and plaquettes), `f₂` does not, and `f₂`-cubes occur in `Ω₀`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 32000000

namespace AdalyFormal.NonVacMix

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.NonVacC
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-- coverage by cubes of ONE factor `f ∈ Φ` is coverage by the mixed class `Φ`. -/
theorem coversΦ_of_mem {L : PeriodicLatticeExtent} {ell M f k : ℕ} {S : Tower L} {Φ : Set ℕ} (hf : f ∈ Φ)
    (h : CoversOm0p ell M f k S) : MXP.AllC.CoversOmΦ ell M Φ k S := by
  refine ⟨fun x hx => ?_, fun p hp => ?_⟩
  · obtain ⟨sites, j, hq, hx'⟩ := h.1 x hx
    exact ⟨sites, j, ⟨f, hf, hq⟩, hx'⟩
  · obtain ⟨sites, j, hq, hb⟩ := h.2 p hp
    exact ⟨sites, j, ⟨f, hf, hq⟩, hb⟩

theorem nonvac_core_mix {ell M R T q f₁ f₂ : ℕ} {Φ : Set ℕ} (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R)
    (hq : R ≤ q) (hT : 1 ≤ T) (hwT : R + ell * q ≤ T)
    (hΦ : ∀ f ∈ Φ, 10 ≤ f ∧ f ≤ T) (hf₁ : f₁ ∈ Φ) (hf₂ : f₂ ∈ Φ)
    (h1w : f₁ ≤ R + ell * q) (hwf2 : R + ell * q < f₂) {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
      2 ≤ k ∧ TorusOK ell M Lu ∧ Admissible ell M R k S ∧ LambdaOK2 ell M R k S Lam ∧
      0 < α₀ ∧ (∀ f ∈ Φ, (f : ℝ) * (M : ℝ) * α₀ ≤ a₀) ∧
      MXP.AllC.ClassCoupledΦ ell M Φ k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      (∃ p, p ∈ towerBj S 0) ∧ (∃ p, p ∈ towerBj S 1) ∧ (∃ p, p ∈ towerBj S 2) ∧
      (∃ p, p ∉ S.Om 0) ∧
      (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
      (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
      Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
      (∀ f ∈ Φ, ∀ j : ℕ, j ≤ k → ∀ μ : Fin 3, 6 * (f * bigSide M ell j) ≤ scaleUp ell k Lu μ + 1) ∧
      (∀ f ∈ Φ, ∀ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
        IsClassCube ell M f k S sites j → ∃ x, x ∉ sites) ∧
      (∀ g : ℕ, 2 ≤ g → (CoversOm0c ell M g k S ↔ g ≤ R + ell * q)) ∧
      CoversOm0p ell M f₁ k S ∧ ¬ CoversOm0c ell M f₂ k S ∧ f₁ ≠ f₂ ∧
      (∃ x ∈ S.Om 0, ∃ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
        IsClassCube ell M f₂ k S sites j ∧ x ∈ sites) := by
  have hell0 : 0 < ell := by omega
  have hRT : R ≤ T := by nlinarith
  have hf₁10 := (hΦ f₁ hf₁).1
  have hf₁T := (hΦ f₁ hf₁).2
  have hf₂T := (hΦ f₂ hf₂).2
  have hN : ∀ μ, scaleUp ell 2 (nvcLu M T) μ + 1 = nvcN ell M T := fun μ => scaleUp_nvc hell0 hM μ
  have G := slabGeo_mix hell hdvd hM hR hq hT hwT
  have hAdm : Admissible ell M R 2 (mxS (scaleUp ell 2 (nvcLu M T)) ell M R T q) := slab3_admissible G hN
  have hcov := mx_covers hell hdvd hM hR hq hT hwT (by omega : 2 ≤ f₁) h1w hN
  have hNpos : 2 ≤ nvcN ell M T := by
    have h1 : 1 ≤ M * ell ^ 2 := Nat.mul_pos hM (pow_pos hell0 2)
    have : 2 ≤ M * ell ^ 2 * (6 * T + 2) := by nlinarith
    simpa [nvcN] using this
  obtain ⟨-, -, -, -, -, hP12, -, -⟩ := mx_widths hell hM hR hq hT hwT (f := 0) (Nat.zero_le _)
  have hL0 : 1 ≤ scaleUp ell 2 (nvcLu M T) 0 := by have := hN 0; omega
  have g1 := G.nest01; have g2 := G.nest12; have g3 := G.nestw; have g4 := G.nest21; have g5 := G.nest10
  have g6 := G.QN; have g7 := G.c0P; have g8 := G.c0Q
  have hRM : 0 < R * M := Nat.mul_pos (by omega) hM
  obtain ⟨-, -, -, -, hQNlt, -, -, hQ10lt⟩ := nvc_widths (c := 2) hell hM hR hRT hT (by omega)
  -- the small parameter
  have hTr : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  obtain ⟨α₀, hα0def⟩ : ∃ α₀ : ℝ, α₀ = min (a₀ / (T * M)) 1 / 2 := ⟨_, rfl⟩
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hα0 : 0 < α₀ := by
    rw [hα0def]
    have : 0 < a₀ / ((T : ℝ) * (M : ℝ)) := by positivity
    have := lt_min this one_pos; positivity
  have hα1 : α₀ ≤ 1 / 2 := by rw [hα0def]; have := min_le_right (a₀ / ((T : ℝ) * (M : ℝ))) 1; linarith
  have hαS : (T : ℝ) * M * α₀ ≤ a₀ := by
    rw [hα0def]
    have h := min_le_left (a₀ / ((T : ℝ) * (M : ℝ))) 1
    have h2 : (T : ℝ) * M * (a₀ / (T * M)) = a₀ := by field_simp
    have h3 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ T * M)
    have h0 : 0 ≤ min (a₀ / ((T : ℝ) * (M : ℝ))) 1 := le_min (by positivity) zero_le_one
    nlinarith
  have hαΦ : ∀ f ∈ Φ, (f : ℝ) * (M : ℝ) * α₀ ≤ a₀ := by
    intro f hf
    have hfT : (f : ℝ) ≤ T := by exact_mod_cast (hΦ f hf).2
    have hMα : 0 ≤ (M : ℝ) * α₀ := by positivity
    calc (f : ℝ) * M * α₀ = f * (M * α₀) := by ring
      _ ≤ T * (M * α₀) := mul_le_mul_of_nonneg_right hfT hMα
      _ = T * M * α₀ := by ring
      _ ≤ a₀ := hαS
  -- the spike
  have hell' : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hη : (((ell : ℝ) ^ 2)⁻¹) ≤ 1 / 4 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
  have hη0 : 0 < ((ell : ℝ) ^ 2)⁻¹ := by positivity
  have hc0 : 0 < α₀ * (((ell : ℝ) ^ 2)⁻¹) ^ 2 / 10 := by positivity
  have hηc0 : 0 < ((ell : ℝ) ^ 2)⁻¹ * (α₀ * (((ell : ℝ) ^ 2)⁻¹) ^ 2 / 10) := by positivity
  have hηc1 : ((ell : ℝ) ^ 2)⁻¹ * (α₀ * (((ell : ℝ) ^ 2)⁻¹) ^ 2 / 10) < 1 := by
    have h1 : (((ell : ℝ) ^ 2)⁻¹) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  obtain ⟨v, hvdef⟩ : ∃ v, v = M * ell ^ 2 * (3 * T) := ⟨_, rfl⟩
  have hME : 0 < M * ell ^ 2 := Nat.mul_pos hM (pow_pos hell0 2)
  have hvP : mxP2 ell M R q ≤ v := by
    simp only [mxP2]; rw [hvdef]; exact Nat.mul_le_mul_left _ (by omega)
  have hvQ : v + 1 < nvcQ2 ell M T := by
    simp only [nvcQ2]; rw [hvdef]
    have : M * ell ^ 2 * (4 * T + 1) = M * ell ^ 2 * (3 * T) + M * ell ^ 2 * (T + 1) := by ring
    have : 2 ≤ M * ell ^ 2 * (T + 1) := by nlinarith
    omega
  let z0 : PeriodicLatticeSite (scaleUp ell 2 (nvcLu M T)) := siteAt0 (T := T) hell0 hM v (by omega)
  have hz0v : (z0 0).val = v := siteAt0_val hell0 hM v (by omega)
  have hN1 : 1 < nvcN ell M T := by omega
  have hsh : ((periodicLatticeShift z0 0) 0).val = v + 1 := by
    rw [shift_val_N hN hN1, if_pos rfl, hz0v, Nat.mod_eq_of_lt (by omega)]
  have hUreg : ∀ f ∈ Φ, AdalyFormal.M1.M1Regular ell M f 2 (mxS (scaleUp ell 2 (nvcLu M T)) ell M R T q) α₀ (((ell : ℝ) ^ 2)⁻¹)
      (Ufield (((ell : ℝ) ^ 2)⁻¹) (spike (periodicLatticeShift z0 0, 1) (α₀ * (((ell : ℝ) ^ 2)⁻¹) ^ 2 / 10))) := by
    intro f hf
    have h := AdalyFormal.M1.ufield_M1Regular (ell := ell) (M := M) (f := f) (k := 2) (by omega) hM (hΦ f hf).1
      (mxS (scaleUp ell 2 (nvcLu M T)) ell M R T q)
      hα0 (spike (periodicLatticeShift z0 0, 1) (α₀ * (((ell : ℝ) ^ 2)⁻¹) ^ 2 / 10)) (by
        intro e
        unfold spike
        split_ifs
        · rw [abs_of_pos hc0]
        · simp only [abs_zero]; positivity)
    exact h
  have hnowrap : ∀ f ∈ Φ, ∀ j : ℕ, j ≤ 2 → ∀ μ : Fin 3, 6 * (f * bigSide M ell j) ≤ scaleUp ell 2 (nvcLu M T) μ + 1 := by
    intro f hf j hj μ
    rw [hN μ]
    exact nvc_period (by omega) hM hj (hΦ f hf).2
  have hnowhole : ∀ f ∈ Φ, ∀ (sites : Set (PeriodicLatticeSite (scaleUp ell 2 (nvcLu M T)))) (j : ℕ),
      IsClassCube ell M f 2 (mxS (scaleUp ell 2 (nvcLu M T)) ell M R T q) sites j → ∃ x, x ∉ sites := by
    intro f hf sites j hq'
    obtain ⟨hj, ⟨z, -, rfl⟩, -⟩ := hq'.1
    refine box_not_univ hN z ?_
    have := nvc_period (ell := ell) (M := M) (T := T) (c := f) (j := j) (by omega) hM hj (hΦ f hf).2
    have h2 : 0 < f * bigSide M ell j := Nat.mul_pos (by have := (hΦ f hf).1; omega) (Nat.mul_pos hM (pow_pos hell0 j))
    omega
  refine ⟨2, nvcLu M T, mxS (scaleUp ell 2 (nvcLu M T)) ell M R T q, LamN M T,
    Ufield (((ell : ℝ) ^ 2)⁻¹) (spike (periodicLatticeShift z0 0, 1) (α₀ * (((ell : ℝ) ^ 2)⁻¹) ^ 2 / 10)),
    α₀, BseedNv ell hM, le_rfl, torusOK_nv hell hdvd hM, hAdm, lambdaOK2_mx hell hdvd hM hR hq hT hwT, hα0, hαΦ,
    ⟨coversΦ_of_mem hf₁ hcov, fun f hf => AdalyFormal.M1.perCube_of_M1 hAdm (hUreg f hf)⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, lam_nonempty hM, ?_,
    (BseedNv_props hell hdvd hM).1, (BseedNv_props hell hdvd hM).2.1, (BseedNv_props hell hdvd hM).2.2.1,
    (BseedNv_props hell hdvd hM).2.2.2, hnowrap, hnowhole, ?_, hcov, mx_not_covers hell hdvd hM hR hq hT hwT hwf2,
    by omega, ?_⟩
  · refine ⟨siteAt0 (T := T) hell0 hM (mxP0 ell M R q) (by omega), ?_⟩
    unfold mxS; rw [bj0, siteAt0_val]; omega
  · refine ⟨siteAt0 (T := T) hell0 hM (mxP1 ell M R q) (by omega), ?_⟩
    unfold mxS; rw [bj1, siteAt0_val]; omega
  · refine ⟨siteAt0 (T := T) hell0 hM (mxP2 ell M R q) (by omega), ?_⟩
    unfold mxS; rw [bj2, siteAt0_val]; omega
  · refine ⟨siteAt0 (T := T) hell0 hM (nvcQ0 ell M R T) (by omega), ?_⟩
    unfold mxS; rw [om0_mem, siteAt0_val]; omega
  · refine ⟨z0, ?_, ?_, ?_⟩
    · unfold mxS; rw [om2_mem, hz0v]; omega
    · unfold mxS; rw [om2_mem, hsh]; omega
    · rw [plaq_spike _ _ z0 (shift_ne_self z0 0 hL0)]
      exact Ug_ne_one hηc0 hηc1
  · exact spike_not_pure_gauge hL0 _ _ z0 hηc0 hηc1
  · exact (lamBlockSum_nv hell0 hdvd hM).lamPrime_nonempty (lam_nonempty hM)
  · intro g hg2
    constructor
    · intro hc
      by_contra hgw
      exact mx_not_covers hell hdvd hM hR hq hT hwT (by omega) hc
    · intro hgw
      exact (mx_covers hell hdvd hM hR hq hT hwT hg2 hgw hN).1
  · obtain ⟨x, sites, j, hx, hc, hxs⟩ := mx_right_cube hell hdvd hM hR hq hT hwT (by omega : 2 ≤ f₂) hf₂T
    exact ⟨x, hx, sites, j, hc, hxs⟩

end AdalyFormal.NonVacMix
