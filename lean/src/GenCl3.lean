import GenCl2
import NC7

/-!
# GenCl3 -- the general-class gap in the headline regime (lane general_class_20261015)

`gc_class_gap`: for EVERY bound `F` on the per-cube factor, every `ell ≥ max 3 (2F)`, `m ≥ 1`, `R ≥ max 1 (F-1)` (`M = ell^m`):
the isolated-block tower (GenCl2) with NC4's `Λ`, `B̃` is in the headline regime (`TorusOK`, `Admissible`, `LambdaOK2`, `Λ ≠ ∅`,
`B̃ ∈ Λ̃` nonzero), its site `x_c ∈ Ω₀` lies in no general class cube of factor `≤ F` (and in no set of the non-box superset),
general-class coverage fails, the general class `PerCubeRegularG .. F ..` leaves the link `b* = (x_c, 1)` completely free, and the
plaquette `p* = (x_c; 0, 1)` is in `plaqIn Ω₀` with holonomy `-1` at `1[b* ↦ -1]`.
`gc_forces_unit`: `P428Target8G F` forces `Ginv` (3.122) to be invertible at every `1[b* ↦ v]` on these instances (NC7's mechanism).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.GeneralClass

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.NoCover
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.FullReparamC (freeBond freeBond_not_dropped)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.NonVac (pcd_gt_right2 pcd_gt_left2 shift_val_N)

/-! ## `Λ` (NC4's) is admissible on any tower whose `Ω₁` contains the thick slab -/

theorem lambdaOK_gc {ell M R : ℕ} (hell : 3 ≤ ell) (_hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) :
    LambdaOK ell M R 1 (gcS ell M R) (ncLam M R) := by
  have hell0 : 0 < ell := by omega
  have hsub : ∀ x : GSite ell M R, ncP1 ell M R ≤ (x 0).val → (x 0).val < ncQ1 ell M R → x ∈ (gcS ell M R).Om 1 := by
    intro x h1 h2; rw [gcS_om1]; exact Or.inl ⟨h1, h2⟩
  refine ⟨blockClosed_ncLam hM, embNc ell M R hell0 hM, fun y μ => rfl, ?_, ?_⟩
  · intro y hy
    apply hsub
    · show ncP1 ell M R ≤ ell ^ 1 * (y 0).val
      simp only [ncP1, pow_one]
      have h1 := hy.1
      calc ell * (R * M + M) ≤ ell * (M * (2 * R + 2)) := Nat.mul_le_mul_left _ (by nlinarith)
        _ ≤ ell * (y 0).val := Nat.mul_le_mul_left _ h1
    · show ell ^ 1 * (y 0).val < ncQ1 ell M R
      simp only [ncQ1, pow_one]
      have h2 := hy.2
      calc ell * (y 0).val < ell * (M * (2 * R + 2) + M) := Nat.mul_lt_mul_of_pos_left h2 hell0
        _ ≤ ell * (3 * (R * M) + 4 * M) := Nat.mul_le_mul_left _ (by nlinarith)
  · intro y hy y' hy'
    have hcase : (y' 0).val < R * M + M ∨ 3 * (R * M) + 4 * M ≤ (y' 0).val := by
      by_contra hcon
      push Not at hcon
      apply hy'
      apply hsub
      · show ncP1 ell M R ≤ ell ^ 1 * (y' 0).val
        simp only [ncP1, pow_one]; exact Nat.mul_le_mul_left _ hcon.1
      · show ell ^ 1 * (y' 0).val < ncQ1 ell M R
        simp only [ncQ1, pow_one]; exact Nat.mul_lt_mul_of_pos_left hcon.2 hell0
    have hyN : (y 0).val < ncNu M R := nc_lt hM y 0
    have hy'N : (y' 0).val < ncNu M R := nc_lt hM y' 0
    have e4 : ncNu M R = 5 * (R * M) + 17 * M := by simp only [ncNu]; ring
    have hMR : 0 < R * M := Nat.mul_pos (by omega) hM
    have hy1 := hy.1
    have hy2 := hy.2
    have e5 : M * (2 * R + 2) = 2 * (R * M) + 2 * M := by ring
    have hpd : R * M < pcd (ncNu M R) (y 0).val (y' 0).val := by
      rcases hcase with h | h
      · exact pcd_gt_right2 (by omega) (by omega)
      · exact pcd_gt_left2 (by omega) hy'N (by omega)
    unfold pdist
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun μ : Fin 3 => pcd (ncLu M R μ + 1) (y μ).val (y' μ).val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0))
    simpa [ncLu_succ hM] using hpd

theorem lambdaOK2_gc {ell M R : ℕ} (hell : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) :
    LambdaOK2 ell M R 1 (gcS ell M R) (ncLam M R) :=
  ⟨lambdaOK_gc hell hdvd hM hR, lamBlockSum_nc (by omega) hdvd hM⟩

/-! ## the plaquette `p* = (x_c; 0, 1)` is read by the operators -/

theorem pStar_plaqIn_gc {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) :
    pStar (xcG ell M R (by omega) hM) ∈ plaqIn ((gcS ell M R).Om 0) := by
  have hell0 : 0 < ell := by omega
  have hN := nc_scaleUp (ell := ell) (R := R) hell0 hM
  obtain ⟨-, -, e3, -, e5⟩ := nc_expand ell M R
  have hme : M * ell = ell * M := Nat.mul_comm _ _
  have hMl : M ≤ M * ell := Nat.le_mul_of_pos_right M hell0
  have hN1 : 1 < ncN ell M R := by rw [e5]; omega
  obtain ⟨hx0, hx1, hx2⟩ := xcG_val (R := R) hell0 hM
  set x := xcG ell M R hell0 hM
  -- `ell/2 + 2 ≤ ell` (`ell ≥ 3`), so `M(ell/2) + 2 ≤ M ell`
  have hh : M * (ell / 2) + 2 * M ≤ M * ell := by
    have : ell / 2 + 2 ≤ ell := by omega
    have := Nat.mul_le_mul_left M this
    rw [mul_add, mul_comm M 2] at this; exact this
  have memB : ∀ y : GSite ell M R, ((y 0).val = (x 0).val ∨ (y 0).val = (x 0).val + 1) →
      ((y 1).val = (x 1).val ∨ (y 1).val = (x 1).val + 1) → (y 2).val = (x 2).val → y ∈ (gcS ell M R).Om 0 := by
    intro y h0 h1 h2
    rw [gcS_om0]
    apply gcOm1_sub
    right
    rw [hx0] at h0; rw [hx1] at h1; rw [hx2] at h2
    refine ⟨?_, ?_, ?_⟩ <;> omega
  have v0 : (x 0).val + 1 < ncN ell M R := by rw [hx0, e3, e5]; omega
  have v1 : (x 1).val + 1 < ncN ell M R := by rw [hx1, e5]; omega
  have m0 : ((x 0).val + 1) % ncN ell M R = (x 0).val + 1 := Nat.mod_eq_of_lt v0
  have m1 : ((x 1).val + 1) % ncN ell M R = (x 1).val + 1 := Nat.mod_eq_of_lt v1
  have sv := shift_val_N hN hN1
  intro e he
  simp only [periodicPlaquetteBoundaryEdges, pStar, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · refine ⟨memB _ (Or.inl rfl) (Or.inl rfl) rfl, memB _ ?_ ?_ ?_⟩ <;> simp [sv, m0]
  · refine ⟨memB _ ?_ ?_ ?_, memB _ ?_ ?_ ?_⟩ <;> simp [sv, m0, m1]
  · refine ⟨memB _ ?_ ?_ ?_, memB _ ?_ ?_ ?_⟩ <;> simp [sv, m0, m1]
  · refine ⟨memB _ (Or.inl rfl) (Or.inl rfl) rfl, memB _ ?_ ?_ ?_⟩ <;> simp [sv, m1]

/-! ## the gap -/

/-- **the general-class gap in the headline regime.** -/
theorem gc_class_gap {F ell m R : ℕ} (hell : 3 ≤ ell) (hF2 : 2 * F ≤ ell) (hm : 1 ≤ m) (hR : 1 ≤ R) (hFR : F ≤ R + 1) :
    ∃ (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell 1 Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (Bt : Bond Lu → SuTwo) (x : PeriodicLatticeSite (scaleUp ell 1 Lu)),
      TorusOK ell (ell ^ m) Lu ∧ Admissible ell (ell ^ m) R 1 S ∧ LambdaOK2 ell (ell ^ m) R 1 S Lam ∧ Lam.Nonempty ∧
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧
      x ∈ S.Om 0 ∧
      (∀ (sites : Set (PeriodicLatticeSite (scaleUp ell 1 Lu))) (j : ℕ), IsClassSetW ell (ell ^ m) F 1 S sites j → x ∉ sites) ∧
      (∀ (f : ℕ) (sites : Set (PeriodicLatticeSite (scaleUp ell 1 Lu))) (j : ℕ), f ≤ F →
        IsClassCubeG ell (ell ^ m) f 1 S sites j → x ∉ sites) ∧
      ¬ CoversOm0G ell (ell ^ m) F 1 S ∧
      (∀ α₀ : ℝ, 0 < α₀ → ∀ v : Matrix.specialUnitaryGroup (Fin 2) ℂ,
        PerCubeRegularG ell (ell ^ m) F 1 S α₀ ((ell : ℝ) ^ 1)⁻¹ (Function.update (fun _ => 1) ((x, 1) : Bond _) v)) ∧
      (∀ (α₀ η : ℝ) (U : LinkCfg (scaleUp ell 1 Lu)), PerCubeRegularG ell (ell ^ m) F 1 S α₀ η U →
        ∀ v : Matrix.specialUnitaryGroup (Fin 2) ℂ,
          PerCubeRegularG ell (ell ^ m) F 1 S α₀ η (Function.update U ((x, 1) : Bond _) v)) ∧
      pStar x ∈ plaqIn (S.Om 0) ∧ ((x, 1) : Bond _) ∈ periodicPlaquetteBoundaryEdges (pStar x) ∧
      periodicPlaquetteHolonomy (Function.update (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) ((x, 1) : Bond _) negOne)
        (pStar x) = negOne := by
  have hell0 : 0 < ell := by omega
  have hM : 0 < ell ^ m := pow_pos hell0 m
  have hdvd : ell ∣ ell ^ m := dvd_pow_self ell (by omega)
  obtain ⟨Bp1, Bp2, Bp3, -⟩ := BseedNc_props (R := R) hell hdvd hM
  have hunc := gc_uncoveredG (R := R) hell0 hM hF2 hFR
  have hN := nc_scaleUp (ell := ell) (R := R) hell0 hM
  have hN1 : 1 < ncN ell (ell ^ m) R := by
    obtain ⟨-, -, -, -, e5⟩ := nc_expand ell (ell ^ m) R
    have : 0 < ell * ell ^ m := Nat.mul_pos hell0 hM
    rw [e5]; omega
  refine ⟨ncLu (ell ^ m) R, gcS ell (ell ^ m) R, ncLam (ell ^ m) R, BseedNc (R := R) ell hM, xcG ell (ell ^ m) R hell0 hM,
    torusOK_nc hell hdvd hM, gc_admissible hell0 hM, lambdaOK2_gc hell hdvd hM hR, ncLam_nonempty hM, Bp1, Bp2, Bp3,
    xcG_om0 hell0 hM, gc_uncoveredW hell0 hM hF2 hFR, hunc, gc_not_coversG hell0 hM hF2 hFR, ?_, ?_,
    pStar_plaqIn_gc (by omega) hM, bStar_mem _, hol_update_negOne hN hN1 _⟩
  · intro α₀ hα v
    have hη : (0 : ℝ) < ((ell : ℝ) ^ 1)⁻¹ := by positivity
    exact perCubeG_update (perCubeG_one hell0 hM hα hη) _ (fun f sites j hf hq => hunc f sites j hf hq) v
  · intro α₀ η U hU v
    exact perCubeG_update hU _ (fun f sites j hf hq => hunc f sites j hf hq) v

/-! ## the general headline forces invertibility of `Ginv` on these instances -/

theorem instIneq_fails_of_not_unit_gc {ell M R : ℕ} (hell : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M)
    {a γ₀ : ℝ} (ha : 0 < a) (hγ : 0 ≤ γ₀) (U : LinkCfg (scaleUp ell 1 (ncLu M R)))
    (h : ¬ IsUnit (gparams ell 1 (ncLu M R) (by omega) (gcS ell M R) U a (ncLam M R)).data.Ginv) :
    ¬ InstIneq ell 1 (by omega) a (ncLu M R) γ₀ (gcS ell M R) (ncLam M R) U := by
  intro hI
  obtain ⟨h1, h2, h3, -⟩ := BseedNc_props (R := R) hell hdvd hM
  have hI' := hI (BseedNc (R := R) ell hM) h1 h2
  rw [genForm_of_not_unit _ h] at hI'
  have hell2 : 2 ≤ ell := by omega
  have hdvd' : ∀ μ : Fin 3, ell ∣ ncLu M R μ + 1 := fun μ => by
    rw [ncLu_succ hM]; exact Dvd.dvd.mul_right hdvd _
  have hy : yNc (R := R) hM ∈ CoarseLattice (ncLu M R) ell := by
    rw [mem_CoarseLattice]
    intro μ
    show (if μ = 0 then M * (2 * R + 2) else 0) % ell = 0
    split_ifs
    · exact Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right hdvd _)
    · simp
  set Bt := BseedNc (R := R) ell hM
  set P := gparams ell 1 (ncLu M R) (by omega) (gcS ell M R) U a (ncLam M R)
  have hnd : ¬ IsDroppedIn (ncLam M R) ell (freeBond ell (yNc (R := R) hM)) := by
    rintro ⟨c, -, hc⟩
    exact freeBond_not_dropped hell2 hdvd' (yNc (R := R) hM) hy ⟨c, hc⟩
  have hC : GenP.genC P Bt (freeBond ell (yNc (R := R) hM)) = suTwoWitness := by
    show Cop (ncLam M R) P.Q1 Bt (freeBond ell (yNc (R := R) hM)) = suTwoWitness
    rw [Cop_id _ _ _ _ hnd]
    exact Pi.single_eq_same _ _
  have hpos : 0 < ⟪(WithLp.toLp 2 (GenP.genC P Bt) : BondFnL2 (ncLu M R)),
      (WithLp.toLp 2 (GenP.genC P Bt) : BondFnL2 (ncLu M R))⟫ := by
    rw [real_inner_self_eq_norm_sq]
    have hne : (WithLp.toLp 2 (GenP.genC P Bt) : BondFnL2 (ncLu M R)) ≠ 0 := by
      intro h0
      have := congrArg (fun f : BondFnL2 (ncLu M R) => (WithLp.ofLp f) (freeBond ell (yNc (R := R) hM))) h0
      have h00 : GenP.genC P Bt (freeBond ell (yNc (R := R) hM)) = 0 := by simpa using this
      rw [hC] at h00
      exact suTwoWitness_ne_zero h00
    have := norm_pos_iff.mpr hne
    positivity
  have hE : 0 ≤ γ₀ * bondEnergy Bt := mul_nonneg hγ h3.le
  have : -P.a * ⟪(WithLp.toLp 2 (GenP.genC P Bt) : BondFnL2 (ncLu M R)),
      (WithLp.toLp 2 (GenP.genC P Bt) : BondFnL2 (ncLu M R))⟫ < 0 := by
    have hPa : P.a = a := rfl
    rw [hPa]; nlinarith
  linarith

/-- **`P428Target8G F` forces `Ginv` (3.122) to be invertible at every `1[b* ↦ v]` on the isolated-block instances**
(`1 ≤ F`, `ell ≥ max 3 (2F)`, `R ≥ max R₀ 1`, `F ≤ R + 1`).  Contrapositive: one `v` with `Ginv` singular there, for arbitrarily
large `m` and `R`, refutes `P428Target8G F`. -/
theorem gc_forces_unit {F : ℕ} (hF : 1 ≤ F) (h : P428Target8G F) :
    ∀ (ell : ℕ) (hell : 3 ≤ ell), 2 * F ≤ ell → ∀ (a : ℝ), 0 < a →
      ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 1 ≤ R → F ≤ R + 1 →
        ∀ v : Matrix.specialUnitaryGroup (Fin 2) ℂ,
        IsUnit (gparams ell 1 (ncLu (ell ^ m) R) (by omega) (gcS ell (ell ^ m) R)
          (Function.update (fun _ => 1) ((xcG ell (ell ^ m) R (by omega) (pow_pos (by omega) m), 1) : Bond _) v) a
          (ncLam (ell ^ m) R)).data.Ginv := by
  intro ell hell hF2 a ha
  obtain ⟨m₀, hm₀, hm⟩ := h ell (by omega) a ha
  refine ⟨m₀, hm₀, fun m hm' => ?_⟩
  obtain ⟨R₀, hR⟩ := hm m hm'
  refine ⟨R₀, fun R hR' hR1 hFR v => ?_⟩
  obtain ⟨-, a₀, ha₀, γ₀, hγ, hcore⟩ := hR R hR'
  have hell0 : 0 < ell := by omega
  have hM : 0 < ell ^ m := pow_pos hell0 m
  have hdvd : ell ∣ ell ^ m := dvd_pow_self ell (by omega)
  have hMr : (0 : ℝ) < ((ell ^ m : ℕ) : ℝ) := by exact_mod_cast hM
  have hFr : (0 : ℝ) < (F : ℝ) := by exact_mod_cast hF
  set α₀ : ℝ := a₀ / ((F : ℝ) * ((ell ^ m : ℕ) : ℝ)) with hα
  have hα0 : 0 < α₀ := by rw [hα]; positivity
  have hαS : (F : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ := by
    rw [hα]; field_simp; exact le_rfl
  have hη : (0 : ℝ) < ((ell : ℝ) ^ 1)⁻¹ := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell0
    positivity
  have hcls : PerCubeRegularG ell (ell ^ m) F 1 (gcS ell (ell ^ m) R) α₀ ((ell : ℝ) ^ 1)⁻¹
      (Function.update (fun _ => 1) ((xcG ell (ell ^ m) R hell0 hM, 1) : Bond _) v) :=
    perCubeG_update (perCubeG_one hell0 hM hα0 hη) _
      (fun f sites j hf hq => gc_uncoveredG hell0 hM hF2 hFR f sites j hf hq) v
  have hI := hcore 1 le_rfl (ncLu (ell ^ m) R) α₀ hα0 hαS (torusOK_nc hell hdvd hM) (gcS ell (ell ^ m) R)
    (gc_admissible hell0 hM) (ncLam (ell ^ m) R) (lambdaOK2_gc hell hdvd hM hR1) _ hcls
  by_contra hn
  exact instIneq_fails_of_not_unit_gc hell hdvd hM ha hγ.le _ hn hI

#print axioms lambdaOK_gc
#print axioms lambdaOK2_gc
#print axioms pStar_plaqIn_gc
#print axioms gc_class_gap
#print axioms instIneq_fails_of_not_unit_gc
#print axioms gc_forces_unit

end AdalyFormal.GeneralClass
