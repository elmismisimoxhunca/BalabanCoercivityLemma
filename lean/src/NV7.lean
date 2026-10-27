import NV6
import M1B

/-!
# NV7 -- `headline_regime_nonvacuous`: every hypothesis of `CoercG8At` is jointly satisfiable in the headline regime (lane nonvac_20261015)

For every `ell ≥ 2`, `m ≥ 1`, `R ≥ 18`, `a₀ > 0`: `k = 2`, the unit torus `Lu = nvLu`, the slab tower `S` (`Ω₀ ⊋ Ω₁ ⊋ Ω₂`, all three strata nonempty,
`Ω₀ ≠` torus), `Λ ≠ ∅` (`LambdaOK2`), a curved `U` that is not pure gauge in `ClassCoupled ell (ell^m) 12 2 S α₀ (ell^2)⁻¹ U`, `0 < α₀`,
`12 · ell^m · α₀ ≤ a₀`, and a nonzero `B̃ ∈ Λ̃`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.NonVac

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

theorem nv_widths {ell M R : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 18 ≤ R) :
    nvP0 ell M R + 12 * M ≤ nvP2 ell M R ∧ nvQ2 ell M R + 12 * M ≤ nvQ0 ell M R ∧
    nvP1 ell M R + 12 * (M * ell) ≤ nvQ1 ell M R ∧ nvP2 ell M R + 12 * (M * ell ^ 2) ≤ nvQ2 ell M R ∧
    nvQ0 ell M R < nvN ell M R ∧ nvP1 ell M R < nvP2 ell M R ∧ nvQ2 ell M R < nvQ1 ell M R ∧
    nvQ1 ell M R < nvQ0 ell M R := by
  obtain ⟨d, hd⟩ : ∃ d, ell ^ 2 = d + 1 := ⟨ell ^ 2 - 1, by have : 1 ≤ ell ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
  have hd3 : 3 ≤ d := by
    have : 4 ≤ ell ^ 2 := by nlinarith
    omega
  have hle : ell ≤ d + 1 := by rw [← hd]; nlinarith
  have hMe : M * ell ≤ M * (d + 1) := Nat.mul_le_mul_left M hle
  have h1 : 0 < M * R := Nat.mul_pos hM (by omega)
  have h2 : 12 ≤ M * R := by nlinarith
  simp only [nvP0, nvP1, nvP2, nvQ0, nvQ1, nvQ2, nvN, hd, Nat.add_sub_cancel]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith [Nat.zero_le (M * R * d), Nat.zero_le (M * d)]
  · nlinarith [Nat.zero_le (M * R * d), Nat.zero_le (M * d)]
  · nlinarith [Nat.zero_le (M * R * d), Nat.zero_le (M * d)]
  · nlinarith [Nat.zero_le (M * R * d), Nat.zero_le (M * d)]
  · nlinarith [Nat.zero_le (M * R * d), Nat.zero_le (M * d)]
  · nlinarith [Nat.zero_le (M * R * d), Nat.zero_le (M * d)]
  · nlinarith [Nat.zero_le (M * R * d), Nat.zero_le (M * d)]
  · nlinarith [Nat.zero_le (M * R * d), Nat.zero_le (M * d)]


/-- a site of the fine torus with coordinate 0 equal to `v` and the others `0`. -/
def siteAt0 {ell M R : ℕ} (hell : 0 < ell) (hM : 0 < M) (v : ℕ) (hv : v < nvN ell M R) :
    PeriodicLatticeSite (scaleUp ell 2 (nvLu M R)) :=
  fun μ => ⟨if μ = 0 then v else 0, by
    have h := scaleUp_nv (ell := ell) (R := R) hell hM μ
    have : 0 < nvN ell M R := lt_of_le_of_lt (Nat.zero_le _) hv
    split_ifs <;> omega⟩

theorem siteAt0_val {ell M R : ℕ} (hell : 0 < ell) (hM : 0 < M) (v : ℕ) (hv : v < nvN ell M R) :
    ((siteAt0 (R := R) hell hM v hv) 0).val = v := by simp [siteAt0]

theorem nonvac_core {ell M R : ℕ} (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 18 ≤ R)
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
      2 ≤ k ∧ TorusOK ell M Lu ∧ Admissible ell M R k S ∧ LambdaOK2 ell M R k S Lam ∧
      0 < α₀ ∧ ((12 : ℕ) : ℝ) * (M : ℝ) * α₀ ≤ a₀ ∧
      ClassCoupled ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      (∃ p, p ∈ towerBj S 0) ∧ (∃ p, p ∈ towerBj S 1) ∧ (∃ p, p ∈ towerBj S 2) ∧
      (∃ p, p ∉ S.Om 0) ∧
      (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
      (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
      Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 := by
  have hell0 : 0 < ell := by omega
  have hR1 : 1 ≤ R := by omega
  have G := slabGeo_inst hell hM hdvd hR1
  obtain ⟨w0L, w0R, w1, w2, hQN, hP12, hQ21, hQ10⟩ := nv_widths hell hM hR
  have hN : ∀ μ, scaleUp ell 2 (nvLu M R) μ + 1 = nvN ell M R := fun μ => scaleUp_nv hell0 hM μ
  have hAdm := slab3_admissible G hN
  have hcov := slab3_coversp G w0L w0R w1 w2 hQN hP12 hQ21 hQ10 hN
  have hNpos : 2 ≤ nvN ell M R := by
    have := G.nest21; have := G.nest10; have := G.nestw; have := G.QN; omega
  have hL0 : 1 ≤ scaleUp ell 2 (nvLu M R) 0 := by have := hN 0; omega
  have g1 := G.nest01; have g2 := G.nest12; have g3 := G.nestw; have g4 := G.nest21; have g5 := G.nest10
  have g6 := G.QN; have g7 := G.c0P; have g8 := G.c0Q
  have hRM : 0 < R * M := Nat.mul_pos (by omega) hM
  -- the small parameter
  obtain ⟨α₀, hα0def⟩ : ∃ α₀ : ℝ, α₀ = min (a₀ / (12 * M)) 1 / 2 := ⟨_, rfl⟩
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hα0 : 0 < α₀ := by
    rw [hα0def]
    have : 0 < a₀ / (12 * (M : ℝ)) := by positivity
    have := lt_min this one_pos; positivity
  have hα1 : α₀ ≤ 1 / 2 := by rw [hα0def]; have := min_le_right (a₀ / (12 * (M : ℝ))) 1; linarith
  have hαS : (12 : ℝ) * M * α₀ ≤ a₀ := by
    rw [hα0def]
    have h := min_le_left (a₀ / (12 * (M : ℝ))) 1
    have h2 : (12 : ℝ) * M * (a₀ / (12 * M)) = a₀ := by field_simp
    have h3 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 12 * M)
    have h0 : 0 ≤ min (a₀ / (12 * (M : ℝ))) 1 := le_min (by positivity) zero_le_one
    nlinarith
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
  obtain ⟨v, hvdef⟩ : ∃ v, v = M * ell ^ 2 * (3 * R) := ⟨_, rfl⟩
  have hME : 0 < M * ell ^ 2 := Nat.mul_pos hM (pow_pos hell0 2)
  have hvP : nvP2 ell M R ≤ v := by
    simp only [nvP2]; rw [hvdef]; exact Nat.mul_le_mul_left _ (by omega)
  have hvQ : v + 1 < nvQ2 ell M R := by
    simp only [nvQ2]; rw [hvdef]
    have : M * ell ^ 2 * (4 * R + 1) = M * ell ^ 2 * (3 * R) + M * ell ^ 2 * (R + 1) := by ring
    have : 2 ≤ M * ell ^ 2 * (R + 1) := by nlinarith
    omega
  let z0 : PeriodicLatticeSite (scaleUp ell 2 (nvLu M R)) := siteAt0 (R := R) hell0 hM v (by omega)
  have hz0v : (z0 0).val = v := siteAt0_val hell0 hM v (by omega)
  have hN1 : 1 < nvN ell M R := by omega
  have hsh : ((periodicLatticeShift z0 0) 0).val = v + 1 := by
    rw [shift_val_N hN hN1, if_pos rfl, hz0v, Nat.mod_eq_of_lt (by omega)]
  have hUreg := AdalyFormal.M1.ufield_M1Regular (ell := ell) (M := M) (f := 12) (k := 2) (by omega) hM (by norm_num)
    (slab3 (scaleUp ell 2 (nvLu M R)) (nvP0 ell M R) (nvQ0 ell M R) (nvP1 ell M R) (nvQ1 ell M R) (nvP2 ell M R) (nvQ2 ell M R))
    hα0 (spike (periodicLatticeShift z0 0, 1) (α₀ * (((ell : ℝ) ^ 2)⁻¹) ^ 2 / 10)) (by
      intro e
      unfold spike
      split_ifs
      · rw [abs_of_pos hc0]
      · simp only [abs_zero]; positivity)
  refine ⟨2, nvLu M R, slab3 (scaleUp ell 2 (nvLu M R)) (nvP0 ell M R) (nvQ0 ell M R) (nvP1 ell M R) (nvQ1 ell M R)
    (nvP2 ell M R) (nvQ2 ell M R), LamN M R,
    Ufield (((ell : ℝ) ^ 2)⁻¹) (spike (periodicLatticeShift z0 0, 1) (α₀ * (((ell : ℝ) ^ 2)⁻¹) ^ 2 / 10)),
    α₀, BseedNv ell hM, le_rfl, torusOK_nv hell hdvd hM, hAdm, lambdaOK2_nv hell hdvd hM hR1, hα0, ?_,
    ⟨hcov, AdalyFormal.M1.perCube_of_M1 hAdm hUreg⟩, ?_, ?_, ?_, ?_, ?_, ?_, lam_nonempty hM, ?_,
    (BseedNv_props hell hdvd hM).1, (BseedNv_props hell hdvd hM).2.1, (BseedNv_props hell hdvd hM).2.2.1,
    (BseedNv_props hell hdvd hM).2.2.2⟩
  · simpa using hαS
  · refine ⟨siteAt0 (R := R) hell0 hM (nvP0 ell M R) (by omega), ?_⟩
    rw [bj0, siteAt0_val]; omega
  · refine ⟨siteAt0 (R := R) hell0 hM (nvP1 ell M R) (by omega), ?_⟩
    rw [bj1, siteAt0_val]; omega
  · refine ⟨siteAt0 (R := R) hell0 hM (nvP2 ell M R) (by omega), ?_⟩
    rw [bj2, siteAt0_val]; omega
  · refine ⟨siteAt0 (R := R) hell0 hM (nvQ0 ell M R) (by omega), ?_⟩
    rw [om0_mem, siteAt0_val]; omega
  · refine ⟨z0, ?_, ?_, ?_⟩
    · rw [om2_mem, hz0v]; omega
    · rw [om2_mem, hsh]; omega
    · rw [plaq_spike _ _ z0 (shift_ne_self z0 0 hL0)]
      exact Ug_ne_one hηc0 hηc1
  · exact spike_not_pure_gauge hL0 _ _ z0 hηc0 hηc1
  · exact (lamBlockSum_nv hell0 hdvd hM).lamPrime_nonempty (lam_nonempty hM)

/-- **`headline_regime_nonvacuous`**: in the headline's regime (`M = ell^m`, `m ≥ 1`, `R ≥ 18`, any `a₀ > 0`) every hypothesis of `CoercG8At` holds jointly,
at `k = 2`, on a proper three-stratum tower, with `Λ ≠ ∅`, a curved non-pure-gauge `U`, and a nonzero `B̃ ∈ Λ̃`. -/
theorem headline_regime_nonvacuous {ell m R : ℕ} (hell : 2 ≤ ell) (hm : 1 ≤ m) (hR : 18 ≤ R)
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
      2 ≤ k ∧ TorusOK ell (ell ^ m) Lu ∧ Admissible ell (ell ^ m) R k S ∧ LambdaOK2 ell (ell ^ m) R k S Lam ∧
      0 < α₀ ∧ ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧
      ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      (∃ p, p ∈ towerBj S 0) ∧ (∃ p, p ∈ towerBj S 1) ∧ (∃ p, p ∈ towerBj S 2) ∧
      (∃ p, p ∉ S.Om 0) ∧
      (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
      (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
      Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 :=
  nonvac_core hell (dvd_pow_self ell (by omega)) (pow_pos (by omega) m) hR ha₀

end AdalyFormal.NonVac
