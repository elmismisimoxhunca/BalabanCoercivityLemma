import THL3
import TD4
import TD6

/-!
# TD5 -- non-vacuity of the two-domain headline (lane two_domain_20261019)

The slab tower of lane nonvac_c_20261017 (`k = 2`, curved non-pure-gauge `U`, `Lambda != empty`, nonzero `B~`) at level-0 radius `R` (the operator tower `S`, `AdmSplitNB ell M R (fun _ => Rb) 2 S`)
and the SAME slab geometry at level-0 radius `Rb > R` (`Sc`, `Admissible ell M Rb 2 Sc`: the p.396 "<= Rb M" layer), `Sc.Om j = S.Om j` for `j >= 1`, `S.Om 0 ⊊ Sc.Om 0`.
`ClassCoupled ell M c 2 Sc alpha0 eta U` holds for the curved `U` (the regularity lemma applied to `Sc`).  `twodom_instance_inequality` applies `totalTwoDom` at it.
JOINT instance: the same `U` satisfies the UNION-class family hypothesis `ClassCoupledP unionClass (famF c) Sc` (every `Sc`-class union of factor `c` is regular: M1 regime), and the family contains the
cut-missing cube of `plain_cut_fails` (TD6); `twodom_union_instance_inequality` applies `famTwoDom_union` at it.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 64000000

namespace AdalyFormal.TwoDom

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.ThinLayer (AdmSplitNB)
open AdalyFormal.NonVacC
open UNI.AllC

theorem two_nonvac_core {ell M R Rb T c : ℕ} (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (hRb : R < Rb) (hRbT : Rb ≤ T) (hRT : R ≤ T)
    (hT : 1 ≤ T) (hcT : c ≤ 2 * T + 1) (hcT' : c ≤ T) (hc10 : 10 ≤ c)
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S Sc : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
      2 ≤ k ∧ TorusOK ell M Lu ∧ AdmSplitNB ell M R (fun _ => Rb) k S ∧ Admissible ell M Rb k Sc ∧
      (∀ j : ℕ, 1 ≤ j → Sc.Om j = S.Om j) ∧ (∀ x, x ∈ S.Om 0 → x ∈ Sc.Om 0) ∧ (∃ p, p ∈ Sc.Om 0 ∧ p ∉ S.Om 0) ∧
      LambdaOK2 ell M Rb k S Lam ∧
      0 < α₀ ∧ ((c : ℕ) : ℝ) * (M : ℝ) * α₀ ≤ a₀ ∧
      ClassCoupled ell M c k Sc α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      (∃ p, p ∈ towerBj S 0) ∧ (∃ p, p ∈ towerBj S 1) ∧ (∃ p, p ∈ towerBj S 2) ∧
      (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
      (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
      Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
      UNI.Total.ClassCoupledP UNI.Total.unionClass ell M (famF c (scaleUp ell k Lu)) k Sc α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      (∃ C : Set (PeriodicLatticeSite (scaleUp ell k Lu)), IsClassUnion ell M k Sc C 0 ∧ (C ∩ S.Om 0).Nonempty ∧
        ¬ UnionAt ell M k S (C ∩ S.Om 0) 0) := by
  have hell0 : 0 < ell := by omega
  have G := slabGeo_inst hell hM hdvd hRT hT
  obtain ⟨w0L, w0R, w1, w2, hQN, hP12, hQ21, hQ10⟩ := nvc_widths hell hM hR hRT hT hcT
  have hN : ∀ μ, scaleUp ell 2 (nvcLu M T) μ + 1 = nvcN ell M T := fun μ => scaleUp_nvc hell0 hM μ
  have hAdm := slab3_admissible G hN
  have Gb := slabGeo_inst (R := Rb) hell hM hdvd hRbT hT
  have hAdmB := slab3_admissible Gb hN
  have hSplit : AdmSplitNB ell M R (fun _ => Rb) 2
      (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)) := by
    obtain ⟨a1, a2, a3, a4, a5, -⟩ := hAdm
    obtain ⟨-, -, -, -, b5, -⟩ := hAdmB
    refine ⟨a1, a2, a3, a4, a5 0 (Nat.zero_le _), fun j hj1 hj2 x hx y hy => ?_⟩
    refine b5 j hj2 x ?_ y ?_
    · have h0 : j ≠ 0 := by omega
      simpa [slab3, h0] using hx
    · have h0 : j + 1 ≠ 0 := by omega
      have h1 : j ≠ 0 := by omega
      simpa [slab3, h0] using hy
  have hproper : ∃ p, p ∈ (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M Rb T) (nvcQ0 ell M Rb T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)).Om 0 ∧ p ∉ (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)).Om 0 := by
    have hv : nvcP0 ell M Rb T < nvcN ell M T := by
      have := Gb.nest01; have := Gb.nest12; have := Gb.nestw; have := Gb.nest21; have := Gb.nest10; have := Gb.QN; omega
    have hlt : nvcP0 ell M Rb T < nvcP0 ell M R T := by
      have hE : T ≤ ell ^ 2 * T := Nat.le_mul_of_pos_left T (pow_pos (by omega) 2)
      simp only [nvcP0]
      exact Nat.mul_lt_mul_of_pos_left (by omega) hM
    set z0 := siteAt0 (T := T) (by omega) hM (nvcP0 ell M Rb T) hv with hz0
    have hz0v : (z0 0).val = nvcP0 ell M Rb T := siteAt0_val (by omega) hM _ hv
    refine ⟨z0, ?_, ?_⟩
    · rw [om0_mem, hz0v]
      have := Gb.nest01; have := Gb.nest12; have := Gb.nestw; have := Gb.nest21; have := Gb.nest10; omega
    · rw [om0_mem, hz0v]; omega
  have hsubS : ∀ x : PeriodicLatticeSite (scaleUp ell 2 (nvcLu M T)),
      x ∈ (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)).Om 0 → x ∈ (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M Rb T) (nvcQ0 ell M Rb T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)).Om 0 := by
    intro x hx
    rw [om0_mem] at hx ⊢
    have h1 : nvcP0 ell M Rb T ≤ nvcP0 ell M R T := by
      simp only [nvcP0]; exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hRb.le _)
    have h2 : nvcQ0 ell M R T ≤ nvcQ0 ell M Rb T := by
      simp only [nvcQ0]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hRb.le) _
    omega
  have hagree : ∀ j : ℕ, 1 ≤ j → (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M Rb T) (nvcQ0 ell M Rb T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)).Om j = (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)).Om j := by
    intro j hj
    have h0 : j ≠ 0 := by omega
    simp [slab3, h0]
  have hLam : LambdaOK2 ell M Rb 2
      (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)) (LamN M T) :=
    lambdaOK2_congr (by simp [slab3]) (lambdaOK2_nv hell hdvd hM hRbT hT)
  obtain ⟨w0LB, w0RB, w1B, w2B, hQNB, hP12B, hQ21B, hQ10B⟩ := nvc_widths hell hM (by omega : 1 ≤ Rb) hRbT hT hcT
  have hcovB := slab3_coversp (by omega) Gb w0LB w0RB w1B w2B hQNB hP12B hQ21B hQ10B hN
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
    (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M Rb T) (nvcQ0 ell M Rb T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T))
    hα0 (spike (periodicLatticeShift z0 0, 1) (α₀ * (((ell : ℝ) ^ 2)⁻¹) ^ 2 / 10)) (by
      intro e
      unfold spike
      split_ifs
      · rw [abs_of_pos hc0]
      · simp only [abs_zero]; positivity)
  have hUC := classCoupledU_of_M1 hAdmB hcovB hUreg
  obtain ⟨Ccut, hC1, hC2, -, hC3⟩ := plain_cut_fails hell hdvd hM hR hRb hRbT hRT hT
  refine ⟨2, nvcLu M T, (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)), (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M Rb T) (nvcQ0 ell M Rb T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)), LamN M T,
    Ufield (((ell : ℝ) ^ 2)⁻¹) (spike (periodicLatticeShift z0 0, 1) (α₀ * (((ell : ℝ) ^ 2)⁻¹) ^ 2 / 10)),
    α₀, BseedNv ell hM, le_rfl, torusOK_nv hell hdvd hM, hSplit, hAdmB, hagree, hsubS, hproper, hLam, hα0, hαS,
    ⟨hcovB, AdalyFormal.M1.perCube_of_M1 hAdmB hUreg⟩, ?_, ?_, ?_, ?_, ?_, lam_nonempty hM, ?_,
    (BseedNv_props hell hdvd hM).1, (BseedNv_props hell hdvd hM).2.1, (BseedNv_props hell hdvd hM).2.2.1,
    (BseedNv_props hell hdvd hM).2.2.2, hUC, ⟨Ccut, hC1, hC2, hC3⟩⟩
  · refine ⟨siteAt0 (T := T) hell0 hM (nvcP0 ell M R T) (by omega), ?_⟩
    rw [bj0, siteAt0_val]; omega
  · refine ⟨siteAt0 (T := T) hell0 hM (nvcP1 ell M T) (by omega), ?_⟩
    rw [bj1, siteAt0_val]; omega
  · refine ⟨siteAt0 (T := T) hell0 hM (nvcP2 ell M T) (by omega), ?_⟩
    rw [bj2, siteAt0_val]; omega
  · refine ⟨z0, ?_, ?_, ?_⟩
    · rw [om2_mem, hz0v]; omega
    · rw [om2_mem, hsh]; omega
    · rw [plaq_spike _ _ z0 (shift_ne_self z0 0 hL0)]
      exact Ug_ne_one hηc0 hηc1
  · exact spike_not_pure_gauge hL0 _ _ z0 hηc0 hηc1
  · exact (lamBlockSum_nv hell0 hdvd hM).lamPrime_nonempty (lam_nonempty hM)

/-- the two-domain witness at `M = ell^m`: layout scale `T = max Rb c` -/
theorem twodom_nonvac_regime {ell m R Rb c : ℕ} (hell : 2 ≤ ell) (hm : 1 ≤ m) (hc : 10 ≤ c) (hR : 1 ≤ R) (hRb : R < Rb)
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S Sc : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
      2 ≤ k ∧ TorusOK ell (ell ^ m) Lu ∧ AdmSplitNB ell (ell ^ m) R (fun _ => Rb) k S ∧ Admissible ell (ell ^ m) Rb k Sc ∧
      (∀ j : ℕ, 1 ≤ j → Sc.Om j = S.Om j) ∧ (∀ x, x ∈ S.Om 0 → x ∈ Sc.Om 0) ∧ (∃ p, p ∈ Sc.Om 0 ∧ p ∉ S.Om 0) ∧
      LambdaOK2 ell (ell ^ m) Rb k S Lam ∧
      0 < α₀ ∧ ((c : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧
      ClassCoupled ell (ell ^ m) c k Sc α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      (∃ p, p ∈ towerBj S 0) ∧ (∃ p, p ∈ towerBj S 1) ∧ (∃ p, p ∈ towerBj S 2) ∧
      (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
      (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
      Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
      UNI.Total.ClassCoupledP UNI.Total.unionClass ell (ell ^ m) (famF c (scaleUp ell k Lu)) k Sc α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      (∃ C : Set (PeriodicLatticeSite (scaleUp ell k Lu)), IsClassUnion ell (ell ^ m) k Sc C 0 ∧ (C ∩ S.Om 0).Nonempty ∧
        ¬ UnionAt ell (ell ^ m) k S (C ∩ S.Om 0) 0) :=
  two_nonvac_core (T := max Rb c) hell (dvd_pow_self ell (by omega)) (pow_pos (by omega) m) hR hRb (le_max_left _ _)
    (by have := le_max_left Rb c; omega) (by have := le_max_left Rb c; omega)
    (by have := le_max_right Rb c; omega) (by have := le_max_right Rb c; omega) hc ha₀

/-- **the two-domain headline applied at the witness**: for every `c >= 10`, `m >= m₁`, level-0 radius `R >= max R₁ 1`, `Rb > R`: the operator tower `S` (thin level-0 domain) and the
class tower `Sc` (the `<= Rb M` layer, `Admissible`) exist, `Om0(S) ⊊ Om0(Sc)`, the curved `U` is in `ClassCoupled .. Sc`, and the conclusion holds for `S` with a nonzero `B~` of positive energy. -/
theorem twodom_instance_inequality (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ (a₀ γ₀ : ℝ), 0 < a₀ ∧ 0 < γ₀ ∧ ∀ c : ℕ, 10 ≤ c → ∀ m : ℕ, m₁ ≤ m →
      ∀ R : ℕ, max R₁ 1 ≤ R → ∀ Rb : ℕ, R < Rb →
      ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S Sc : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
        (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
        2 ≤ k ∧ TorusOK ell (ell ^ m) Lu ∧ AdmSplitNB ell (ell ^ m) R (fun _ => Rb) k S ∧ Admissible ell (ell ^ m) Rb k Sc ∧
        (∀ j : ℕ, 1 ≤ j → Sc.Om j = S.Om j) ∧ (∀ x, x ∈ S.Om 0 → x ∈ Sc.Om 0) ∧ (∃ p, p ∈ Sc.Om 0 ∧ p ∉ S.Om 0) ∧
        LambdaOK2 ell (ell ^ m) Rb k S Lam ∧
        0 < α₀ ∧ ((c : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧
        ClassCoupled ell (ell ^ m) c k Sc α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
        (∃ p, p ∈ towerBj S 0) ∧ (∃ p, p ∈ towerBj S 1) ∧ (∃ p, p ∈ towerBj S 2) ∧
        (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
        (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
        Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
        OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
        GenP.WellDefG (gparams ell k Lu (by omega) S U a Lam) ∧
        γ₀ * bondEnergy Bt ≤
          GenP.genForm (gparams ell k Lu (by omega) S U a Lam)
            (WithLp.toLp 2 (GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt)) := by
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ₀, hT⟩ := totalTwoDom ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, γ₀, ha₀, hγ₀, fun c hc m hm R hR Rb hRb => ?_⟩
  obtain ⟨k, Lu, S, Sc, Lam, U, α₀, Bt, hk, hTor, hSp, hAd, hag, hsub, hprop, hL, hα, hαS, hCC, h0, h1, h2, h4, h5, h6, h7, h8, h9, h10, h11, -, -⟩ :=
    twodom_nonvac_regime (ell := ell) (m := m) (R := R) (Rb := Rb) (c := c) hell (le_trans hm₁ hm) hc
      (le_trans (le_max_right _ _) hR) hRb ha₀
  have hmain := hT c hc m hm R (le_trans (le_max_left _ _) hR) (fun _ => Rb) (fun _ _ => hRb.le) Rb hRb.le k (by omega) Lu α₀ hα hαS
    hTor S hSp Sc hag hsub Lam hL U hCC
  exact ⟨k, Lu, S, Sc, Lam, U, α₀, Bt, hk, hTor, hSp, hAd, hag, hsub, hprop, hL, hα, hαS, hCC, h0, h1, h2, h4, h5, h6, h7, h8, h9, h10, h11,
    hmain.1, hmain.2 Bt h8 h9⟩

/-- **the joint instance for the UNION class**: at the slab witness, the union-class family hypothesis `ClassCoupledP unionClass (famF c) Sc` holds for the curved `U`, the family `famF c`
contains an `Sc`-class union (index 0) whose plain cut to `S.Om 0` is nonempty and is not an `S`-class union of index 0 (TD6), and `famTwoDom_union` gives the conclusion at `S`. -/
theorem twodom_union_instance_inequality (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ (a₀ γ₀ : ℝ), 0 < a₀ ∧ 0 < γ₀ ∧ ∀ c : ℕ, 10 ≤ c → ∀ m : ℕ, m₁ ≤ m →
      ∀ R : ℕ, max R₁ 1 ≤ R → ∀ Rb : ℕ, R < Rb →
      ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S Sc : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
        (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
        2 ≤ k ∧ TorusOK ell (ell ^ m) Lu ∧ AdmSplitNB ell (ell ^ m) R (fun _ => Rb) k S ∧ Admissible ell (ell ^ m) Rb k Sc ∧
        (∀ j : ℕ, 1 ≤ j → Sc.Om j = S.Om j) ∧ (∀ x, x ∈ S.Om 0 → x ∈ Sc.Om 0) ∧ (∃ p, p ∈ Sc.Om 0 ∧ p ∉ S.Om 0) ∧
        LambdaOK2 ell (ell ^ m) Rb k S Lam ∧
        0 < α₀ ∧ ((c : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧
        UNI.Total.ClassCoupledP UNI.Total.unionClass ell (ell ^ m) (famF c (scaleUp ell k Lu)) k Sc α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
        (∃ C : Set (PeriodicLatticeSite (scaleUp ell k Lu)), IsClassUnion ell (ell ^ m) k Sc C 0 ∧ (C ∩ S.Om 0).Nonempty ∧
          ¬ UnionAt ell (ell ^ m) k S (C ∩ S.Om 0) 0) ∧
        (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
        (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
        Lam.Nonempty ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
        GenP.WellDefG (gparams ell k Lu (by omega) S U a Lam) ∧
        γ₀ * bondEnergy Bt ≤
          GenP.genForm (gparams ell k Lu (by omega) S U a Lam)
            (WithLp.toLp 2 (GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt)) := by
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ₀, hT⟩ := famTwoDom_union ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, γ₀, ha₀, hγ₀, fun c hc m hm R hR Rb hRb => ?_⟩
  obtain ⟨k, Lu, S, Sc, Lam, U, α₀, Bt, hk, hTor, hSp, hAd, hag, hsub, hprop, hL, hα, hαS, -, h0, h1, h2, h4, h5, h6, h7, h8, h9, h10, h11, hUC, hcut⟩ :=
    twodom_nonvac_regime (ell := ell) (m := m) (R := R) (Rb := Rb) (c := c) hell (le_trans hm₁ hm) hc
      (le_trans (le_max_right _ _) hR) hRb ha₀
  have hFs : ∀ (s : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j f : ℕ), (s, j, f) ∈ famF c (scaleUp ell k Lu) →
      10 ≤ f ∧ (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ := by
    intro s j f hmem
    have hf : f = c := hmem
    subst hf
    exact ⟨hc, hαS⟩
  have hmain := hT m hm R (le_trans (le_max_left _ _) hR) (fun _ => Rb) (fun _ _ => hRb.le) Rb hRb.le k (by omega) Lu α₀ hα
    (famF c (scaleUp ell k Lu)) hFs hTor S hSp Sc hag hsub Lam hL U hUC
  exact ⟨k, Lu, S, Sc, Lam, U, α₀, Bt, hk, hTor, hSp, hAd, hag, hsub, hprop, hL, hα, hαS, hUC, hcut, h4, h5, h6, h10, h11,
    hmain.1, hmain.2 Bt h8 h9⟩

end AdalyFormal.TwoDom

#print axioms AdalyFormal.TwoDom.two_nonvac_core
#print axioms AdalyFormal.TwoDom.twodom_nonvac_regime
#print axioms AdalyFormal.TwoDom.twodom_instance_inequality
#print axioms AdalyFormal.TwoDom.twodom_union_instance_inequality
