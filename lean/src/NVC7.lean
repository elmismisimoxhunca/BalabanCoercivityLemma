import NVC6
import M1B

/-!
# NVC7 -- `headline_regime_nonvacuousC`: every hypothesis of `CoercG8At` at cube factor `c ≥ 10` is jointly satisfiable (lane nonvac_c_20261017)

For every `ell ≥ 2`, `c ≥ 10`, `m ≥ 1`, `R ≥ 1`, `a₀ > 0`: `k = 2`, the unit torus `nvcLu M T` with layout scale `T = max R c`, the slab tower `S`
(`Ω₀ ⊋ Ω₁ ⊋ Ω₂`, all three strata nonempty, `Ω₀ ≠` torus), `Λ ≠ ∅` (`LambdaOK2`), a curved `U` that is not pure gauge in
`ClassCoupled ell (ell^m) c 2 S α₀ (ell^2)⁻¹ U`, `0 < α₀`, `c · ell^m · α₀ ≤ a₀`, and a nonzero `B̃ ∈ Λ̃`.
The coverage windows have width `c · bigSide`; they are clamped inside the stratum regions, which have width `≥ c · bigSide` because `T ≥ c`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.NonVacC

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

theorem nvc_widths {ell M R T c : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (hRT : R ≤ T) (hT : 1 ≤ T)
    (hcT : c ≤ 2 * T + 1) :
    nvcP0 ell M R T + c * M ≤ nvcP2 ell M T ∧ nvcQ2 ell M T + c * M ≤ nvcQ0 ell M R T ∧
    nvcP1 ell M T + c * (M * ell) ≤ nvcQ1 ell M T ∧ nvcP2 ell M T + c * (M * ell ^ 2) ≤ nvcQ2 ell M T ∧
    nvcQ0 ell M R T < nvcN ell M T ∧ nvcP1 ell M T < nvcP2 ell M T ∧ nvcQ2 ell M T < nvcQ1 ell M T ∧
    nvcQ1 ell M T < nvcQ0 ell M R T := by
  obtain ⟨e, he⟩ : ∃ e, e = ell ^ 2 := ⟨_, rfl⟩
  have he4 : 4 ≤ e := by rw [he]; nlinarith
  have hle : ell ≤ e := by rw [he]; nlinarith
  have hs : ell ^ 2 = e := he.symm
  have hTe : 4 * T ≤ e * T := Nat.mul_le_mul_right T he4
  obtain ⟨g, hg⟩ : ∃ g, e * T = R + g := ⟨e * T - R, by omega⟩
  have hP0 : nvcP0 ell M R T = M * g := by simp only [nvcP0, hs]; congr 1; omega
  have hcg : c ≤ g := by omega
  have hcT3 : c ≤ 3 * T := by omega
  have hX : 0 < M * e := Nat.mul_pos hM (by omega)
  have hcM : c * M ≤ g * M := Nat.mul_le_mul_right M hcg
  have hcl : c * ell ≤ e * (3 * T) := by
    calc c * ell ≤ (3 * T) * e := Nat.mul_le_mul hcT3 hle
      _ = e * (3 * T) := by ring
  have hcl' : c * (M * ell) ≤ M * (e * (3 * T)) := by
    calc c * (M * ell) = M * (c * ell) := by ring
      _ ≤ M * (e * (3 * T)) := Nat.mul_le_mul_left M hcl
  have hc2 : c * (M * e) ≤ (2 * T + 1) * (M * e) := Nat.mul_le_mul_right (M * e) hcT
  have hRM : 0 < R * M := Nat.mul_pos hR hM
  have hMg : M * (e * T) = M * R + M * g := by rw [hg]; ring
  have hMT : 0 < M * e * T := Nat.mul_pos hX hT
  have hRM' : R * M ≤ M * e * T := by
    have : R * M ≤ M * (e * T) := by
      calc R * M = M * R := by ring
        _ ≤ M * (e * T) := Nat.mul_le_mul_left M (by omega)
    nlinarith
  simp only [nvcP1, nvcP2, nvcQ0, nvcQ1, nvcQ2, nvcN, hs]
  rw [hP0]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith [Nat.zero_le (M * R)]
  · nlinarith [Nat.zero_le (M * R)]
  · nlinarith [Nat.zero_le (M * R)]
  · nlinarith [Nat.zero_le (M * R)]
  · nlinarith [Nat.zero_le (M * R)]
  · nlinarith [Nat.zero_le (M * R)]
  · nlinarith [Nat.zero_le (M * R)]
  · nlinarith [Nat.zero_le (M * R)]

/-- a site of the fine torus with coordinate 0 equal to `v` and the others `0`. -/
def siteAt0 {ell M T : ℕ} (hell : 0 < ell) (hM : 0 < M) (v : ℕ) (hv : v < nvcN ell M T) :
    PeriodicLatticeSite (scaleUp ell 2 (nvcLu M T)) :=
  fun μ => ⟨if μ = 0 then v else 0, by
    have h := scaleUp_nvc (ell := ell) (T := T) hell hM μ
    have : 0 < nvcN ell M T := lt_of_le_of_lt (Nat.zero_le _) hv
    split_ifs <;> omega⟩

theorem siteAt0_val {ell M T : ℕ} (hell : 0 < ell) (hM : 0 < M) (v : ℕ) (hv : v < nvcN ell M T) :
    ((siteAt0 (T := T) hell hM v hv) 0).val = v := by simp [siteAt0]

/-- a periodic box strictly smaller than the period misses a site (no wrap-around saturation). -/
theorem box_not_univ {L : PeriodicLatticeExtent} {N : ℕ} (hN : ∀ μ, L μ + 1 = N) (z : PeriodicLatticeSite L) {side : ℕ}
    (h : side < N) : ∃ x : PeriodicLatticeSite L, x ∉ siteBox z side := by
  have hz : (z 0).val < N := by have := (z 0).isLt; have := hN 0; omega
  let v : ℕ := if (z 0).val + side < N then (z 0).val + side else (z 0).val + side - N
  have hv : v < L 0 + 1 := by rw [hN 0]; simp only [v]; split_ifs <;> omega
  refine ⟨Function.update z 0 ⟨v, hv⟩, fun hx => ?_⟩
  have h0 := hx 0
  simp only [Function.update_self, hN 0] at h0
  by_cases hc : (z 0).val + side < N
  · have e : v + N - (z 0).val = side + N := by simp only [v, if_pos hc]; omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt h] at h0
    omega
  · have e : v + N - (z 0).val = side := by simp only [v, if_neg hc]; omega
    rw [e, Nat.mod_eq_of_lt h] at h0
    omega

theorem nvc_period {ell M T c j : ℕ} (hell : 1 ≤ ell) (hM : 0 < M) (hj : j ≤ 2) (hcT : c ≤ T) :
    6 * (c * bigSide M ell j) ≤ nvcN ell M T := by
  have h1 : ell ^ j ≤ ell ^ 2 := Nat.pow_le_pow_right hell hj
  have h2 : bigSide M ell j ≤ M * ell ^ 2 := Nat.mul_le_mul_left M h1
  have h3 : c * bigSide M ell j ≤ T * (M * ell ^ 2) := Nat.mul_le_mul hcT h2
  simp only [nvcN]
  nlinarith [Nat.zero_le (M * ell ^ 2)]

theorem nonvac_core {ell M R T c : ℕ} (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (hRT : R ≤ T)
    (hT : 1 ≤ T) (hcT : c ≤ 2 * T + 1) (hcT' : c ≤ T) (hc10 : 10 ≤ c)
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
      2 ≤ k ∧ TorusOK ell M Lu ∧ Admissible ell M R k S ∧ LambdaOK2 ell M R k S Lam ∧
      0 < α₀ ∧ ((c : ℕ) : ℝ) * (M : ℝ) * α₀ ≤ a₀ ∧
      ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      (∃ p, p ∈ towerBj S 0) ∧ (∃ p, p ∈ towerBj S 1) ∧ (∃ p, p ∈ towerBj S 2) ∧
      (∃ p, p ∉ S.Om 0) ∧
      (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
      (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
      Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
      (∀ j : ℕ, j ≤ k → ∀ μ : Fin 3, 6 * (c * bigSide M ell j) ≤ scaleUp ell k Lu μ + 1) ∧
      (∀ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ), IsClassCube ell M c k S sites j → ∃ x, x ∉ sites) := by
  have hell0 : 0 < ell := by omega
  have G := slabGeo_inst hell hM hdvd hRT hT
  obtain ⟨w0L, w0R, w1, w2, hQN, hP12, hQ21, hQ10⟩ := nvc_widths hell hM hR hRT hT hcT
  have hN : ∀ μ, scaleUp ell 2 (nvcLu M T) μ + 1 = nvcN ell M T := fun μ => scaleUp_nvc hell0 hM μ
  have hAdm := slab3_admissible G hN
  have hcov := slab3_coversp (by omega) G w0L w0R w1 w2 hQN hP12 hQ21 hQ10 hN
  have hNpos : 2 ≤ nvcN ell M T := by
    have := G.nest21; have := G.nest10; have := G.nestw; have := G.QN; omega
  have hL0 : 1 ≤ scaleUp ell 2 (nvcLu M T) 0 := by have := hN 0; omega
  have g1 := G.nest01; have g2 := G.nest12; have g3 := G.nestw; have g4 := G.nest21; have g5 := G.nest10
  have g6 := G.QN; have g7 := G.c0P; have g8 := G.c0Q
  have hRM : 0 < R * M := Nat.mul_pos (by omega) hM
  have hcR : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  -- the small parameter
  obtain ⟨α₀, hα0def⟩ : ∃ α₀ : ℝ, α₀ = min (a₀ / (c * M)) 1 / 2 := ⟨_, rfl⟩
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hα0 : 0 < α₀ := by
    rw [hα0def]
    have : 0 < a₀ / ((c : ℝ) * (M : ℝ)) := by positivity
    have := lt_min this one_pos; positivity
  have hα1 : α₀ ≤ 1 / 2 := by rw [hα0def]; have := min_le_right (a₀ / ((c : ℝ) * (M : ℝ))) 1; linarith
  have hαS : (c : ℝ) * M * α₀ ≤ a₀ := by
    rw [hα0def]
    have h := min_le_left (a₀ / ((c : ℝ) * (M : ℝ))) 1
    have h2 : (c : ℝ) * M * (a₀ / (c * M)) = a₀ := by field_simp
    have h3 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ c * M)
    have h0 : 0 ≤ min (a₀ / ((c : ℝ) * (M : ℝ))) 1 := le_min (by positivity) zero_le_one
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
  obtain ⟨v, hvdef⟩ : ∃ v, v = M * ell ^ 2 * (3 * T) := ⟨_, rfl⟩
  have hME : 0 < M * ell ^ 2 := Nat.mul_pos hM (pow_pos hell0 2)
  have hvP : nvcP2 ell M T ≤ v := by
    simp only [nvcP2]; rw [hvdef]; exact Nat.mul_le_mul_left _ (by omega)
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
  have hUreg := AdalyFormal.M1.ufield_M1Regular (ell := ell) (M := M) (f := c) (k := 2) (by omega) hM hc10
    (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T))
    hα0 (spike (periodicLatticeShift z0 0, 1) (α₀ * (((ell : ℝ) ^ 2)⁻¹) ^ 2 / 10)) (by
      intro e
      unfold spike
      split_ifs
      · rw [abs_of_pos hc0]
      · simp only [abs_zero]; positivity)
  refine ⟨2, nvcLu M T, slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T)
    (nvcP2 ell M T) (nvcQ2 ell M T), LamN M T,
    Ufield (((ell : ℝ) ^ 2)⁻¹) (spike (periodicLatticeShift z0 0, 1) (α₀ * (((ell : ℝ) ^ 2)⁻¹) ^ 2 / 10)),
    α₀, BseedNv ell hM, le_rfl, torusOK_nv hell hdvd hM, hAdm, lambdaOK2_nv hell hdvd hM hRT hT, hα0, hαS,
    ⟨hcov, AdalyFormal.M1.perCube_of_M1 hAdm hUreg⟩, ?_, ?_, ?_, ?_, ?_, ?_, lam_nonempty hM, ?_,
    (BseedNv_props hell hdvd hM).1, (BseedNv_props hell hdvd hM).2.1, (BseedNv_props hell hdvd hM).2.2.1,
    (BseedNv_props hell hdvd hM).2.2.2, ?_, ?_⟩
  · refine ⟨siteAt0 (T := T) hell0 hM (nvcP0 ell M R T) (by omega), ?_⟩
    rw [bj0, siteAt0_val]; omega
  · refine ⟨siteAt0 (T := T) hell0 hM (nvcP1 ell M T) (by omega), ?_⟩
    rw [bj1, siteAt0_val]; omega
  · refine ⟨siteAt0 (T := T) hell0 hM (nvcP2 ell M T) (by omega), ?_⟩
    rw [bj2, siteAt0_val]; omega
  · refine ⟨siteAt0 (T := T) hell0 hM (nvcQ0 ell M R T) (by omega), ?_⟩
    rw [om0_mem, siteAt0_val]; omega
  · refine ⟨z0, ?_, ?_, ?_⟩
    · rw [om2_mem, hz0v]; omega
    · rw [om2_mem, hsh]; omega
    · rw [plaq_spike _ _ z0 (shift_ne_self z0 0 hL0)]
      exact Ug_ne_one hηc0 hηc1
  · exact spike_not_pure_gauge hL0 _ _ z0 hηc0 hηc1
  · exact (lamBlockSum_nv hell0 hdvd hM).lamPrime_nonempty (lam_nonempty hM)
  · intro j hj μ
    rw [hN μ]
    exact nvc_period (by omega) hM hj hcT'
  · intro sites j hq
    obtain ⟨hj, ⟨z, -, rfl⟩, -⟩ := hq.1
    refine box_not_univ hN z ?_
    have := nvc_period (ell := ell) (M := M) (T := T) (c := c) (j := j) (by omega) hM hj hcT'
    have h2 : 0 < c * bigSide M ell j := Nat.mul_pos (by omega) (Nat.mul_pos hM (pow_pos hell0 j))
    omega

/-- **`headline_regime_nonvacuousC`**: for every cube factor `c ≥ 10` (`M = ell^m`, `m ≥ 1`, `R ≥ 1`, any `a₀ > 0`) every hypothesis of
`CoercG8At`/`CoercG8AtWD` at factor `c` holds jointly, at `k = 2`, on a proper three-stratum tower, with `Λ ≠ ∅`, a curved non-pure-gauge `U`, and a
nonzero `B̃ ∈ Λ̃`. -/
theorem headline_regime_nonvacuousC {ell m R c : ℕ} (hell : 2 ≤ ell) (hm : 1 ≤ m) (hc : 10 ≤ c) (hR : 1 ≤ R)
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
      2 ≤ k ∧ TorusOK ell (ell ^ m) Lu ∧ Admissible ell (ell ^ m) R k S ∧ LambdaOK2 ell (ell ^ m) R k S Lam ∧
      0 < α₀ ∧ ((c : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧
      ClassCoupled ell (ell ^ m) c k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      (∃ p, p ∈ towerBj S 0) ∧ (∃ p, p ∈ towerBj S 1) ∧ (∃ p, p ∈ towerBj S 2) ∧
      (∃ p, p ∉ S.Om 0) ∧
      (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
      (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
      Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
      (∀ j : ℕ, j ≤ k → ∀ μ : Fin 3, 6 * (c * bigSide (ell ^ m) ell j) ≤ scaleUp ell k Lu μ + 1) ∧
      (∀ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ), IsClassCube ell (ell ^ m) c k S sites j → ∃ x, x ∉ sites) :=
  nonvac_core (T := max R c) hell (dvd_pow_self ell (by omega)) (pow_pos (by omega) m) hR (le_max_left _ _)
    (by have := le_max_right R c; omega) (by have := le_max_right R c; omega) (le_max_right R c) hc ha₀

end AdalyFormal.NonVacC
