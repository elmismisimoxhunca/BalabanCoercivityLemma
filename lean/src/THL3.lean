import NVC7
import THL1

/-!
# TL3 -- a curved thin-layer witness (lane thin_layer_20261019)

The witness of lane nonvac_c_20261017 (`NonVacC.nonvac_core`: slab tower, `k = 2`, curved non-pure-gauge `U` in `ClassCoupled`, `Lambda != empty`,
nonzero `B~`) has its `Omega_0` widened by `R M` and its level-1 gap `T M ell^2` independent of `R`.  Run at a SMALL level-0 radius `R` and a larger radius `Rb`
(`R < Rb <= T`) the same tower has:
* `Admissible ell M R 2 S`, `AdmSplit ell M R (fun _ => Rb) 2 S` (level-0 radius `R`, level-1 radius `Rb`), `LambdaOK2 ell M Rb 2 S Lam`;
* `not Admissible ell M Rb 2 S` (the layer is strictly thinner than the radial `Rb M`-layer; `Omega_1` is shared, so T6 would force `Omega_0` equal);
* the curved `U` (`plaq U z != 1`, not pure gauge) in `ClassCoupled ell M c 2 S alpha_0 (ell^2)^-1 U`.
`thin_nonvac_core` is `nonvac_core` (copied proof, lane nonvac_c_20261017) with these extra conclusions.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 64000000

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
open AdalyFormal.ThinLayer (AdmSplit)

/-- `LambdaOK2` depends on the tower only through `Omega_k`. -/
theorem lambdaOK2_congr {Lu Lf : PeriodicLatticeExtent} {ell M R k : ℕ} {S S' : Tower Lf}
    {Lam : Set (PeriodicLatticeSite Lu)} (h : S.Om k = S'.Om k) (hL : LambdaOK2 ell M R k S Lam) :
    LambdaOK2 ell M R k S' Lam := by
  obtain ⟨⟨hb, emb, eA, eB, eC⟩, h2⟩ := hL
  exact ⟨⟨hb, emb, eA, fun y hy => by rw [← h]; exact eB y hy, fun y hy y' hy' => eC y hy y' (by rw [h]; exact hy')⟩, h2⟩

theorem thin_nonvac_core {ell M R Rb T c : ℕ} (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (hRb : R < Rb) (hRbT : Rb ≤ T) (hRT : R ≤ T)
    (hT : 1 ≤ T) (hcT : c ≤ 2 * T + 1) (hcT' : c ≤ T) (hc10 : 10 ≤ c)
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
      2 ≤ k ∧ TorusOK ell M Lu ∧ Admissible ell M R k S ∧ AdmSplit ell M R (fun _ => Rb) k S ∧ ¬ Admissible ell M Rb k S ∧
      LambdaOK2 ell M Rb k S Lam ∧
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
  have Gb := slabGeo_inst (R := Rb) hell hM hdvd hRbT hT
  have hAdmB := slab3_admissible Gb hN
  have hSplit : AdmSplit ell M R (fun _ => Rb) 2
      (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)) := by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hAdm
    obtain ⟨-, -, -, -, b5, -⟩ := hAdmB
    refine ⟨a1, a2, a3, a4, a5 0 (Nat.zero_le _), fun j hj1 hj2 x hx y hy => ?_, a6⟩
    refine b5 j hj2 x ?_ y ?_
    · have h0 : j ≠ 0 := by omega
      simpa [slab3, h0] using hx
    · have h0 : j + 1 ≠ 0 := by omega
      have h1 : j ≠ 0 := by omega
      simpa [slab3, h0] using hy
  have hnot : ¬ Admissible ell M Rb 2
      (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)) := by
    intro hA
    obtain ⟨-, -, -, -, -, c6⟩ := hA
    obtain ⟨-, -, -, -, -, d6⟩ := hAdmB
    have hv : nvcP0 ell M Rb T < nvcN ell M T := by
      have := Gb.nest01; have := Gb.nest12; have := Gb.nestw; have := Gb.nest21; have := Gb.nest10; have := Gb.QN; omega
    have hlt : nvcP0 ell M Rb T < nvcP0 ell M R T := by
      have hE : T ≤ ell ^ 2 * T := Nat.le_mul_of_pos_left T (pow_pos (by omega) 2)
      simp only [nvcP0]
      exact Nat.mul_lt_mul_of_pos_left (by omega) hM
    set z0 := siteAt0 (T := T) (by omega) hM (nvcP0 ell M Rb T) hv with hz0
    have hz0v : (z0 0).val = nvcP0 ell M Rb T := siteAt0_val (by omega) hM _ hv
    have hmemB : z0 ∈ (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M Rb T) (nvcQ0 ell M Rb T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)).Om 0 := by
      rw [om0_mem, hz0v]
      have := Gb.nest01; have := Gb.nest12; have := Gb.nestw; have := Gb.nest21; have := Gb.nest10; omega
    have hnotS : z0 ∉ (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)).Om 0 := by
      rw [om0_mem, hz0v]; omega
    apply hnotS
    rw [c6 z0]
    exact (d6 z0).1 hmemB
  have hLam : LambdaOK2 ell M Rb 2
      (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)) (LamN M T) :=
    lambdaOK2_congr (by simp [slab3]) (lambdaOK2_nv hell hdvd hM hRbT hT)
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
    α₀, BseedNv ell hM, le_rfl, torusOK_nv hell hdvd hM, hAdm, hSplit, hnot, hLam, hα0, hαS,
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


/-- the thin-layer witness at `M = ell^m`, level-0 radius `R`, level-`>= 1` and `Lambda` radius `Rb > R`, layout scale `T = max Rb c`. -/
theorem thin_headline_regime_nonvacuous {ell m R Rb c : ℕ} (hell : 2 ≤ ell) (hm : 1 ≤ m) (hc : 10 ≤ c) (hR : 1 ≤ R) (hRb : R < Rb)
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
      2 ≤ k ∧ TorusOK ell (ell ^ m) Lu ∧ Admissible ell (ell ^ m) R k S ∧ AdmSplit ell (ell ^ m) R (fun _ => Rb) k S ∧
      ¬ Admissible ell (ell ^ m) Rb k S ∧ LambdaOK2 ell (ell ^ m) Rb k S Lam ∧
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
  thin_nonvac_core (T := max Rb c) hell (dvd_pow_self ell (by omega)) (pow_pos (by omega) m) hR hRb (le_max_left _ _)
    (by have := le_max_left Rb c; omega) (by have := le_max_left Rb c; omega)
    (by have := le_max_right Rb c; omega) (le_max_right Rb c) hc ha₀

/-- **the thin-layer headline instantiated at the witness**: the thin `P428Target8Total` constants `m₁, R₁, a₀, γ₀` (chosen before `c, m, R0, Rs, RL`); for every
`c ≥ 10`, `m ≥ m₁`, level-0 radius `R0 ≥ max R₁ 1` and any larger level-`>= 1`/`Lambda` radius `Rb > R0`: the witness list above holds and the conclusion
(`WellDefG` and `γ₀ ‖B~‖² ≤ genForm (C B~)`) holds at it, with `‖B~‖² > 0`.  The tower is NOT `Admissible` at `Rb`. -/
theorem thin_instance_inequality (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ (a₀ γ₀ : ℝ), 0 < a₀ ∧ 0 < γ₀ ∧ ∀ c : ℕ, 10 ≤ c → ∀ m : ℕ, m₁ ≤ m →
      ∀ R : ℕ, max R₁ 1 ≤ R → ∀ Rb : ℕ, R < Rb →
      ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
        (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
        2 ≤ k ∧ TorusOK ell (ell ^ m) Lu ∧ Admissible ell (ell ^ m) R k S ∧ AdmSplit ell (ell ^ m) R (fun _ => Rb) k S ∧
        ¬ Admissible ell (ell ^ m) Rb k S ∧ LambdaOK2 ell (ell ^ m) Rb k S Lam ∧
        0 < α₀ ∧ ((c : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧
        ClassCoupled ell (ell ^ m) c k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
        (∃ p, p ∈ towerBj S 0) ∧ (∃ p, p ∈ towerBj S 1) ∧ (∃ p, p ∈ towerBj S 2) ∧ (∃ p, p ∉ S.Om 0) ∧
        (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
        (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
        Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
        OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
        (∀ j : ℕ, j ≤ k → ∀ μ : Fin 3, 6 * (c * bigSide (ell ^ m) ell j) ≤ scaleUp ell k Lu μ + 1) ∧
        (∀ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
          IsClassCube ell (ell ^ m) c k S sites j → ∃ x, x ∉ sites) ∧
        GenP.WellDefG (gparams ell k Lu (by omega) S U a Lam) ∧
        γ₀ * bondEnergy Bt ≤
          GenP.genForm (gparams ell k Lu (by omega) S U a Lam)
            (WithLp.toLp 2 (GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt)) := by
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ₀, hT⟩ := AdalyFormal.ThinLayer.totalThin_unconditional ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, γ₀, ha₀, hγ₀, fun c hc m hm R hR Rb hRb => ?_⟩
  obtain ⟨k, Lu, S, Lam, U, α₀, Bt, hk, hTor, hA, hSp, hn, hL, hα, hαS, hCC, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
    thin_headline_regime_nonvacuous (ell := ell) (m := m) (R := R) (Rb := Rb) (c := c) hell (le_trans hm₁ hm) hc
      (le_trans (le_max_right _ _) hR) hRb ha₀
  have hmain := hT c hc m hm R (le_trans (le_max_left _ _) hR) (fun _ => Rb) (fun _ _ => hRb.le) Rb hRb.le k (by omega) Lu α₀ hα hαS
    hTor S hSp Lam hL U hCC
  exact ⟨k, Lu, S, Lam, U, α₀, Bt, hk, hTor, hA, hSp, hn, hL, hα, hαS, hCC, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    hmain.1, hmain.2 Bt h8 h9⟩

end AdalyFormal.NonVacC

#print axioms AdalyFormal.NonVacC.thin_nonvac_core
#print axioms AdalyFormal.NonVacC.thin_headline_regime_nonvacuous
#print axioms AdalyFormal.NonVacC.thin_instance_inequality
