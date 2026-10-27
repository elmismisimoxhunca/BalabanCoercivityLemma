import NVC7
import M12_F

/-!
# M12_NV -- a CURVED witness for the hypotheses of the `{12, 12*ell}` Mixed / Family headlines (lane mixed12_20261019)

`nonvac_core_Phi` is `AdalyFormal.NonVacC.nonvac_core` (lane nonvac_c_20261017) with the single cube factor `c` replaced by a nonempty set `Φ ⊆ [10, T]`:
same slab tower (layout scale `T`), same curved `U` (a single tiny spike, `|χ| ≤ α₀ η²/10`), same `Λ`, `B̃`; the class hypothesis is `ClassCoupledΦ` (coverage by
cubes of SOME factor in `Φ`, regularity of EVERY described cube of EVERY factor in `Φ`), obtained from `ClassCoupled` at each `f ∈ Φ` (coverage of `Ω₀` by `f`-cubes holds for each
`f ≤ T` on this layout, regularity at `f` is `ufield_M1Regular` at `f`).
`nonvac_core_Phi` also carries an arbitrary predicate `Q k Lu S` on the witness tower (hypothesis `hQ` at the explicit tower `towerW`), so that further properties of THE witness tower (`M12_C5`: the two printed cubes) are conjoined to the same witness.
`factors12_curved_nonvacuous` (M12_W) is the specialisation `Φ = {12, 12 ell}`, `T = max R (12 ell)`, for EVERY `R ≥ 1` (so `R ≥ 21 ell` and every `R ≥ R₁`) and every `m ≥ 1`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace M12NV

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.NonVacC

/-- the slab tower of the witness (layout scale `T`), named so that further properties of THE witness tower can be stated. -/
def towerW (ell M R T : ℕ) : Tower (scaleUp ell 2 (nvcLu M T)) :=
  slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)

theorem nonvac_core_Phi {ell M R T : ℕ} (Q : ∀ (k : ℕ) (Lu : PeriodicLatticeExtent), Tower (scaleUp ell k Lu) → Prop)
    (hQ : Q 2 (nvcLu M T) (towerW ell M R T)) (Φ : Set ℕ) (hne : Φ.Nonempty) (hΦ : ∀ f ∈ Φ, 10 ≤ f ∧ f ≤ T)
    (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (hRT : R ≤ T) (hT : 1 ≤ T)
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
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
      (∀ μ : Fin 3, M < Lu μ + 1) ∧
      (∀ f ∈ Φ, ∀ j : ℕ, j ≤ k → ∀ μ : Fin 3, 6 * (f * bigSide M ell j) ≤ scaleUp ell k Lu μ + 1) ∧
      (∀ f ∈ Φ, ∀ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
        IsClassCube ell M f k S sites j → ∃ x, x ∉ sites) ∧
      (∀ f ∈ Φ, ∃ x ∈ S.Om 0, ∃ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
        IsClassCube ell M f k S sites j ∧ x ∈ sites) ∧
      Q k Lu S := by
  have hell0 : 0 < ell := by omega
  have G := slabGeo_inst hell hM hdvd hRT hT
  have hN : ∀ μ, scaleUp ell 2 (nvcLu M T) μ + 1 = nvcN ell M T := fun μ => scaleUp_nvc hell0 hM μ
  have hcovF : ∀ f ∈ Φ, CoversOm0p ell M f 2 (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T)
      (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)) := by
    intro f hf
    have hf' := hΦ f hf
    obtain ⟨w0L, w0R, w1, w2, hQN, hP12, hQ21, hQ10⟩ := nvc_widths (c := f) hell hM hR hRT hT (by omega)
    exact slab3_coversp (by omega) G w0L w0R w1 w2 hQN hP12 hQ21 hQ10 hN
  obtain ⟨w0L, w0R, w1, w2, hQN, hP12, hQ21, hQ10⟩ := nvc_widths (c := 0) hell hM hR hRT hT (by omega)
  have hAdm := slab3_admissible G hN
  have hNpos : 2 ≤ nvcN ell M T := by
    have := G.nest21; have := G.nest10; have := G.nestw; have := G.QN; omega
  have hL0 : 1 ≤ scaleUp ell 2 (nvcLu M T) 0 := by have := hN 0; omega
  have g1 := G.nest01; have g2 := G.nest12; have g3 := G.nestw; have g4 := G.nest21; have g5 := G.nest10
  have g6 := G.QN; have g7 := G.c0P; have g8 := G.c0Q
  have hRM : 0 < R * M := Nat.mul_pos (by omega) hM
  have hTr : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  obtain ⟨α₀, hα0def⟩ : ∃ α₀ : ℝ, α₀ = min (a₀ / (T * M)) 1 / 2 := ⟨_, rfl⟩
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hα0 : 0 < α₀ := by
    rw [hα0def]
    have : 0 < a₀ / ((T : ℝ) * (M : ℝ)) := by positivity
    have := lt_min this one_pos; positivity
  have hα1 : α₀ ≤ 1 / 2 := by rw [hα0def]; have := min_le_right (a₀ / ((T : ℝ) * (M : ℝ))) 1; linarith
  have hαT : (T : ℝ) * M * α₀ ≤ a₀ := by
    rw [hα0def]
    have h := min_le_left (a₀ / ((T : ℝ) * (M : ℝ))) 1
    have h2 : (T : ℝ) * M * (a₀ / (T * M)) = a₀ := by field_simp
    have h3 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ T * M)
    have h0 : 0 ≤ min (a₀ / ((T : ℝ) * (M : ℝ))) 1 := le_min (by positivity) zero_le_one
    nlinarith
  have hαS : ∀ f ∈ Φ, (f : ℝ) * M * α₀ ≤ a₀ := by
    intro f hf
    have hfT : (f : ℝ) ≤ T := by exact_mod_cast (hΦ f hf).2
    have hMα : 0 ≤ (M : ℝ) * α₀ := by positivity
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
  have hUregF : ∀ f ∈ Φ, AdalyFormal.M1.M1Regular ell M f 2
      (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T))
      α₀ (((ell : ℝ) ^ 2)⁻¹)
      (Ufield (((ell : ℝ) ^ 2)⁻¹) (spike (periodicLatticeShift z0 0, 1) (α₀ * (((ell : ℝ) ^ 2)⁻¹) ^ 2 / 10))) := by
    intro f hf
    exact AdalyFormal.M1.ufield_M1Regular (ell := ell) (M := M) (f := f) (k := 2) (by omega) hM (hΦ f hf).1
      (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T))
      hα0 (spike (periodicLatticeShift z0 0, 1) (α₀ * (((ell : ℝ) ^ 2)⁻¹) ^ 2 / 10)) (by
        intro e
        unfold spike
        split_ifs
        · rw [abs_of_pos hc0]
        · simp only [abs_zero]; positivity)
  have hCCF : ∀ f ∈ Φ, ClassCoupled ell M f 2
      (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T))
      α₀ (((ell : ℝ) ^ 2)⁻¹)
      (Ufield (((ell : ℝ) ^ 2)⁻¹) (spike (periodicLatticeShift z0 0, 1) (α₀ * (((ell : ℝ) ^ 2)⁻¹) ^ 2 / 10))) :=
    fun f hf => ⟨hcovF f hf, AdalyFormal.M1.perCube_of_M1 hAdm (hUregF f hf)⟩
  have hper : ∀ f ∈ Φ, ∀ j : ℕ, j ≤ 2 → ∀ μ : Fin 3, 6 * (f * bigSide M ell j) ≤ scaleUp ell 2 (nvcLu M T) μ + 1 := by
    intro f hf j hj μ
    rw [hN μ]
    exact nvc_period (by omega) hM hj (hΦ f hf).2
  have hmemP0 : siteAt0 (T := T) hell0 hM (nvcP0 ell M R T) (by omega) ∈
      (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)).Om 0 := by
    rw [om0_mem, siteAt0_val]; omega
  refine ⟨2, nvcLu M T, slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T)
    (nvcP2 ell M T) (nvcQ2 ell M T), LamN M T,
    Ufield (((ell : ℝ) ^ 2)⁻¹) (spike (periodicLatticeShift z0 0, 1) (α₀ * (((ell : ℝ) ^ 2)⁻¹) ^ 2 / 10)),
    α₀, BseedNv ell hM, le_rfl, torusOK_nv hell hdvd hM, hAdm, lambdaOK2_nv hell hdvd hM hRT hT, hα0, hαS,
    MXP.AllC.classCoupledΦ_of_forall hne hCCF, ?_, ?_, ?_, ?_, ?_, ?_, lam_nonempty hM, ?_,
    (BseedNv_props hell hdvd hM).1, (BseedNv_props hell hdvd hM).2.1, (BseedNv_props hell hdvd hM).2.2.1,
    (BseedNv_props hell hdvd hM).2.2.2, ?_, hper, ?_, ?_, hQ⟩
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
  · intro μ
    rw [nvcLu_succ hM]
    nlinarith
  · intro f hf sites j hq
    obtain ⟨hj, ⟨z, -, rfl⟩, -⟩ := hq.1
    refine box_not_univ hN z ?_
    have := nvc_period (ell := ell) (M := M) (T := T) (c := f) (j := j) (by omega) hM hj (hΦ f hf).2
    have h2 : 0 < f * bigSide M ell j := Nat.mul_pos (by have := (hΦ f hf).1; omega) (Nat.mul_pos hM (pow_pos hell0 j))
    omega
  · intro f hf
    obtain ⟨hs, -⟩ := (hCCF f hf).1
    obtain ⟨sites, j, hq, hx⟩ := hs _ hmemP0
    exact ⟨_, hmemP0, sites, j, hq, hx⟩

end M12NV
