import P4L4
import M12_W

/-!
# M12_C5 -- the printed `tilde-square^5` of p.409 at index `j = 2` AND at index `j - 1 = 1` on the witness tower (lane mixed12_20261019)

On the explicit slab tower `towerW ell M R T` (the tower of `factors12_curved_nonvacuous`), `k = 2`, with `21 ell <= R <= T`, `12 ell <= T`:
* `c₁` (centre deep inside `Ω₂`, coordinate `3 T M ell²`) and `c₂` (centre on the `Ω₂` boundary, coordinate `2 T M ell²`) are `D_2` cubes (`IsDCube`),
* `printedCube5 (M ell²) c₁` is a class cube of factor `12` at index `2` (`i = j`), and `printedCube5 (M ell²) c₂` is a class cube of factor `12 ell` at index `1` (`i + 1 = j`),
  both via `cube5_is_class_box` (lane p409_local_20261019), the factor being pinned by the geometry (`c₁`: the cube misses `B¹`; `c₂`: it contains a point outside `Ω₂`, and `B³ = ∅`).
`factors12_curved_cube5` : the curved witness of `factors12_curved_nonvacuous` carries, for `R ≥ 21 ell`, these two cubes as members of the family `famPhi {12, 12 ell}`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 64000000

namespace M12NV

open AdalyFormal.P409L AdalyFormal.GeneralClass AdalyFormal.Target.ClayStatement AdalyFormal.StatementLane AdalyFormal.StatementLane2
  AdalyFormal.StatementLaneG AdalyFormal.P409C5
open AdalyFormal.NonVacC
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

section geom

variable {L : PeriodicLatticeExtent}

theorem mem_cubeR_self (c : PeriodicLatticeSite L) {r : ℕ} (hr : 0 < r) : c ∈ cubeR c r := by
  intro μ
  exact ⟨0, by omega, by omega, by simp⟩

theorem cubeR_coord {N : ℕ} (hN : ∀ μ, L μ + 1 = N) {c y : PeriodicLatticeSite L} {r : ℕ} (hy : y ∈ cubeR c r)
    (h1 : r ≤ (c 0).val) (h2 : (c 0).val + r ≤ N) :
    (c 0).val ≤ (y 0).val + r ∧ (y 0).val < (c 0).val + r := by
  obtain ⟨t, ht1, ht2, ht3⟩ := hy 0
  have hNN : ((L 0 + 1 : ℕ) : ℤ) = (N : ℤ) := by rw [hN 0]
  rw [hNN] at ht3
  have hy0 : ((y 0).val : ℤ) < N := by have := (y 0).isLt; have := hN 0; omega
  have e1 : ((y 0).val : ℤ) % (N : ℤ) = ((y 0).val : ℤ) := Int.emod_eq_of_lt (by positivity) hy0
  have e2 : (((c 0).val : ℤ) + t) % (N : ℤ) = ((c 0).val : ℤ) + t := Int.emod_eq_of_lt (by omega) (by omega)
  have h3 := ht3
  unfold Int.ModEq at h3
  rw [e1, e2] at h3
  omega

end geom

theorem siteAt0_ne {ell M T : ℕ} (hell : 0 < ell) (hM : 0 < M) (v : ℕ) (hv : v < nvcN ell M T) {μ : Fin 3} (hμ : μ ≠ 0) :
    ((siteAt0 (T := T) hell hM v hv) μ).val = 0 := by
  simp [siteAt0, hμ]

theorem cube5_both_factors {ell M R T : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hdvd : ell ∣ M) (hR21 : 21 * ell ≤ R) (hRT : R ≤ T)
    (hT12 : 12 * ell ≤ T) :
    ∃ (c₁ c₂ : PeriodicLatticeSite (scaleUp ell 2 (nvcLu M T))),
      IsDCube ell M 2 (towerW ell M R T) 2 c₁ ∧ IsDCube ell M 2 (towerW ell M R T) 2 c₂ ∧
      IsClassCube ell M 12 2 (towerW ell M R T) (printedCube5 (bigSide M ell 2) c₁) 2 ∧
      IsClassCube ell M (12 * ell) 2 (towerW ell M R T) (printedCube5 (bigSide M ell 2) c₂) 1 ∧
      c₁ ∈ printedCube5 (bigSide M ell 2) c₁ ∧ c₁ ∈ (towerW ell M R T).Om 0 ∧
      c₂ ∈ printedCube5 (bigSide M ell 2) c₂ ∧ c₂ ∈ (towerW ell M R T).Om 0 := by
  have hell0 : 0 < ell := by omega
  have hT : 1 ≤ T := by omega
  have G := slabGeo_inst hell hM hdvd (by omega : R ≤ T) hT
  have hN : ∀ μ, scaleUp ell 2 (nvcLu M T) μ + 1 = nvcN ell M T := fun μ => scaleUp_nvc hell0 hM μ
  have hA : Admissible ell M R 2 (towerW ell M R T) := slab3_admissible G hN
  obtain ⟨g, hg⟩ : ∃ g, g = M * ell ^ 2 := ⟨_, rfl⟩
  have hgpos : 0 < g := by rw [hg]; exact Nat.mul_pos hM (pow_pos hell0 2)
  obtain ⟨a, ha⟩ : ∃ a, a = g * T := ⟨_, rfl⟩
  have ha24 : 24 * g ≤ a := by
    rw [ha]; have : 24 ≤ T := by omega
    nlinarith
  have hbig : bigSide M ell 2 = g := by rw [hg]; rfl
  have hNa : nvcN ell M T = 6 * a + 2 * g := by simp only [nvcN]; rw [← hg, ha]; ring
  have hP2 : nvcP2 ell M T = 2 * a := by simp only [nvcP2]; rw [← hg, ha]; ring
  have hQ2 : nvcQ2 ell M T = 4 * a + g := by simp only [nvcQ2]; rw [← hg, ha]; ring
  have hgt : ∀ μ : Fin 3, bigSide M ell 2 < scaleUp ell 2 (nvcLu M T) μ + 1 := by
    intro μ; rw [hN μ, hNa, hbig]; omega
  have hbs : bigSide M ell 2 * 1 = g := by rw [hbig]; ring
  -- centres
  have hv1 : 3 * a < nvcN ell M T := by omega
  have hv2 : 2 * a < nvcN ell M T := by omega
  set c₁ : PeriodicLatticeSite (scaleUp ell 2 (nvcLu M T)) := siteAt0 (T := T) hell0 hM (3 * a) hv1 with hc₁
  set c₂ : PeriodicLatticeSite (scaleUp ell 2 (nvcLu M T)) := siteAt0 (T := T) hell0 hM (2 * a) hv2 with hc₂
  have hc₁0 : (c₁ 0).val = 3 * a := siteAt0_val hell0 hM _ _
  have hc₂0 : (c₂ 0).val = 2 * a := siteAt0_val hell0 hM _ _
  have hD : ∀ (c : PeriodicLatticeSite (scaleUp ell 2 (nvcLu M T))) (b : ℕ), (c 0).val = b * g → (∀ μ : Fin 3, μ ≠ 0 → (c μ).val = 0) →
      2 * a ≤ b * g → b * g < 4 * a + g →
      IsDCube ell M 2 (towerW ell M R T) 2 c := by
    intro c b hb hrest h1 h2
    refine ⟨le_rfl, fun μ => ?_, c, (bj2 c).2 ?_, ?_⟩
    · by_cases hμ : μ = 0
      · subst hμ; rw [hbig, hb]; exact Nat.mul_mod_left b g
      · rw [hrest μ hμ]; exact Nat.zero_mod _
    · exact ⟨by omega, by omega⟩
    · rw [dCube_eq, hbig]; exact mem_cubeR_self c hgpos
  have hD1 : IsDCube ell M 2 (towerW ell M R T) 2 c₁ := by
    refine hD c₁ (3 * T) (by rw [hc₁0, ha]; ring) (fun μ hμ => siteAt0_ne hell0 hM _ _ hμ) ?_ ?_ <;>
      · have : 3 * T * g = 3 * a := by rw [ha]; ring
        omega
  have hD2 : IsDCube ell M 2 (towerW ell M R T) 2 c₂ := by
    refine hD c₂ (2 * T) (by rw [hc₂0, ha]; ring) (fun μ hμ => siteAt0_ne hell0 hM _ _ hμ) ?_ ?_ <;>
      · have : 2 * T * g = 2 * a := by rw [ha]; ring
        omega
  have hmono := hA.1
  have hc1c : c₁ ∈ printedCube5 (bigSide M ell 2) c₁ := by
    rw [printedCube5_eq]; exact mem_cubeR_self c₁ (by omega)
  have hc2c : c₂ ∈ printedCube5 (bigSide M ell 2) c₂ := by
    rw [printedCube5_eq]; exact mem_cubeR_self c₂ (by omega)
  have hOm0 : ∀ c : PeriodicLatticeSite (scaleUp ell 2 (nvcLu M T)), (c 0).val = 3 * a ∨ (c 0).val = 2 * a → c ∈ (towerW ell M R T).Om 0 := by
    intro c hc
    show c ∈ (slab3 _ _ _ _ _ _ _).Om 0
    rw [om0_mem]
    have e1 : nvcP0 ell M R T ≤ 2 * a := by
      have := G.nest01; have := G.nest12; omega
    have e2 : 4 * a + g ≤ nvcQ0 ell M R T := by
      have := G.nest21; have := G.nest10; omega
    rcases hc with h | h <;> rw [h] <;> constructor <;> omega
  -- cube5 at c₁ (coordinate 3a): inside Omega_2
  have hcube1 : ∀ y ∈ printedCube5 (bigSide M ell 2) c₁, 2 * a ≤ (y 0).val ∧ (y 0).val < 4 * a + g := by
    intro y hy
    rw [printedCube5_eq] at hy
    have := cubeR_coord (N := nvcN ell M T) hN hy (by rw [hc₁0, hbig]; omega) (by rw [hc₁0, hbig, hNa]; omega)
    rw [hc₁0, hbig] at this
    omega
  obtain ⟨i1, f1, hif1, -, hdesc1, -⟩ := cube5_is_class_box (c := c₁) (j := 2) (R := R) hell hM hR21 hA hgt hD1 (by norm_num)
  obtain ⟨i2, f2, hif2, -, hdesc2, -⟩ := cube5_is_class_box (c := c₂) (j := 2) (R := R) hell hM hR21 hA hgt hD2 (by norm_num)
  refine ⟨c₁, c₂, hD1, hD2, ?_, ?_, hc1c, hOm0 c₁ (Or.inl hc₁0), hc2c, hOm0 c₂ (Or.inr hc₂0)⟩
  · rcases hif1 with ⟨rfl, rfl⟩ | ⟨hi, rfl⟩
    · exact (isClassCube_iff hmono _ _).2 hdesc1
    · exfalso
      have hi1 : i1 = 1 := by omega
      subst hi1
      obtain ⟨y, hy1, hy2⟩ := hdesc1.2.2.2
      have hb := (bj1 y).1 hy2
      have := hcube1 y hy1
      exact hb.2 ⟨by rw [hP2]; exact this.1, by rw [hQ2]; exact this.2⟩
  · rcases hif2 with ⟨rfl, rfl⟩ | ⟨hi, rfl⟩
    · exfalso
      have hy : siteAt0 (T := T) hell0 hM (2 * a - 1) (by omega) ∈ printedCube5 (bigSide M ell 2) c₂ := by
        rw [printedCube5_eq]
        intro μ
        by_cases hμ : μ = 0
        · subst hμ
          refine ⟨-1, by omega, by omega, ?_⟩
          have e1 : ((siteAt0 (T := T) hell0 hM (2 * a - 1) (by omega)) 0).val = 2 * a - 1 := siteAt0_val hell0 hM _ _
          rw [e1, hc₂0]
          have : ((2 * a - 1 : ℕ) : ℤ) = ((2 * a : ℕ) : ℤ) + (-1) := by omega
          rw [this]
        · refine ⟨0, by omega, by omega, ?_⟩
          rw [siteAt0_ne hell0 hM _ _ hμ, siteAt0_ne hell0 hM _ _ hμ]
          simp
      rcases hdesc2.2.2.1 hy with h | h
      · have := ((bj2 _).1 h).1
        rw [siteAt0_val hell0 hM, hP2] at this
        omega
      · exact bj3 _ h
    · have hi1 : i2 = 1 := by omega
      subst hi1
      exact (isClassCube_iff hmono _ _).2 hdesc2

/-- the two p.409 cubes of the witness tower: `tilde-square^5` of two `D_2` cubes (`k`-independent form), one a class cube of factor `12` (index `2`), one of factor `12 ell`
(index `1`), both members of the family `famPhi {12, 12 ell}`, both through a point of `Ω₀`. -/
def Cube5Q (ell M : ℕ) (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) : Prop :=
  ∃ c₁ c₂ : PeriodicLatticeSite (scaleUp ell k Lu),
    IsDCube ell M k S 2 c₁ ∧ IsDCube ell M k S 2 c₂ ∧
    IsClassCube ell M 12 k S (printedCube5 (bigSide M ell 2) c₁) 2 ∧
    IsClassCube ell M (12 * ell) k S (printedCube5 (bigSide M ell 2) c₂) 1 ∧
    (printedCube5 (bigSide M ell 2) c₁, 2, 12) ∈ MXQ.Total.famPhi (M12.Phi12 ell) (scaleUp ell k Lu) ∧
    (printedCube5 (bigSide M ell 2) c₂, 1, 12 * ell) ∈ MXQ.Total.famPhi (M12.Phi12 ell) (scaleUp ell k Lu) ∧
    c₁ ∈ printedCube5 (bigSide M ell 2) c₁ ∧ c₁ ∈ S.Om 0 ∧ c₂ ∈ printedCube5 (bigSide M ell 2) c₂ ∧ c₂ ∈ S.Om 0

/-- **the curved witness at the p.409 collar `R ≥ 21 ell`, carrying the printed `tilde-square^5` at index `j = 2` (factor `12`) and at index `j - 1 = 1` (factor `12 ell`).** -/
theorem factors12_curved_cube5 {ell m R : ℕ}
    (hell : 2 ≤ ell) (hm : 1 ≤ m) (hR21 : 21 * ell ≤ R)
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
      2 ≤ k ∧ TorusOK ell (ell ^ m) Lu ∧ (∀ μ : Fin 3, ell ^ m < Lu μ + 1) ∧
      (∀ μ : Fin 3, bigSide (ell ^ m) ell k < scaleUp ell k Lu μ + 1) ∧
      Admissible ell (ell ^ m) R k S ∧ LambdaOK2 ell (ell ^ m) R k S Lam ∧
      0 < α₀ ∧ (12 * (ell : ℝ)) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧
      (∀ f ∈ M12.Phi12 ell, (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) ∧
      MXP.AllC.ClassCoupledΦ ell (ell ^ m) (M12.Phi12 ell) k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      MXQ.AllC.ClassCoupledQ ell (ell ^ m) (MXQ.Total.famPhi (M12.Phi12 ell)) k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      (∃ p, p ∈ towerBj S 0) ∧ (∃ p, p ∈ towerBj S 1) ∧ (∃ p, p ∈ towerBj S 2) ∧
      (∃ p, p ∉ S.Om 0) ∧
      (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
      (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
      Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
      (∀ f ∈ M12.Phi12 ell, ∀ j : ℕ, j ≤ k → ∀ μ : Fin 3,
        6 * (f * bigSide (ell ^ m) ell j) ≤ scaleUp ell k Lu μ + 1) ∧
      (∀ f ∈ M12.Phi12 ell, ∀ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
        IsClassCube ell (ell ^ m) f k S sites j → ∃ x, x ∉ sites) ∧
      (12 : ℕ) ≠ 12 * ell ∧
      (∃ x ∈ S.Om 0, ∃ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
        IsClassCube ell (ell ^ m) 12 k S sites j ∧ x ∈ sites ∧
        (sites, j, 12) ∈ MXQ.Total.famPhi (M12.Phi12 ell) (scaleUp ell k Lu)) ∧
      (∃ x ∈ S.Om 0, ∃ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
        IsClassCube ell (ell ^ m) (12 * ell) k S sites j ∧ x ∈ sites ∧
        (sites, j, 12 * ell) ∈ MXQ.Total.famPhi (M12.Phi12 ell) (scaleUp ell k Lu)) ∧
      Cube5Q ell (ell ^ m) k Lu S :=
  factors12_curved_nonvacuous_Q (Cube5Q ell (ell ^ m)) (by
    obtain ⟨c₁, c₂, h1, h2, h3, h4, h5, h6, h7, h8⟩ := cube5_both_factors (ell := ell) (M := ell ^ m) (R := R) (T := max R (12 * ell))
      hell (pow_pos (by omega) m) (dvd_pow_self ell (by omega)) hR21 (le_max_left _ _) (le_max_right _ _)
    exact ⟨c₁, c₂, h1, h2, h3, h4, Or.inl rfl, Or.inr rfl, h5, h6, h7, h8⟩) hell hm (by omega) ha₀

/-- **the Family headline at the curved witness with the two printed `tilde-square^5` cubes (`R ≥ max R₁ (21 ell)`).** -/
theorem factors12_instance_inequality_cube5 (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ (a₀ γ₀ : ℝ), 0 < a₀ ∧ 0 < γ₀ ∧
      ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, max R₁ (21 * ell) ≤ R →
      ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
      2 ≤ k ∧ TorusOK ell (ell ^ m) Lu ∧ (∀ μ : Fin 3, ell ^ m < Lu μ + 1) ∧
      (∀ μ : Fin 3, bigSide (ell ^ m) ell k < scaleUp ell k Lu μ + 1) ∧
      Admissible ell (ell ^ m) R k S ∧ LambdaOK2 ell (ell ^ m) R k S Lam ∧
      0 < α₀ ∧ (12 * (ell : ℝ)) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧
      MXQ.AllC.ClassCoupledQ ell (ell ^ m) (MXQ.Total.famPhi (M12.Phi12 ell)) k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
      (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
      Lam.Nonempty ∧ OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
      Cube5Q ell (ell ^ m) k Lu S ∧
      GenP.WellDefG (gparams ell k Lu (by omega) S U a Lam) ∧
      γ₀ * bondEnergy Bt ≤
        GenP.genForm (gparams ell k Lu (by omega) S U a Lam)
          (WithLp.toLp 2 (GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt)) := by
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ₀, hU⟩ := M12.p428Target8_factors_12_12ell_family ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, γ₀, ha₀, hγ₀, fun m hm R hR => ?_⟩
  have hR21 : 21 * ell ≤ R := le_trans (le_max_right R₁ (21 * ell)) hR
  obtain ⟨k, Lu, S, Lam, U, α₀, Bt, hk, hT, hLu, hgt, hA, hL, hα, hα12l, -, -, hCQ, -, -, -, -, hcv, hnp, hLam, -, hOT, hOT2, hen, hBt,
    -, -, -, -, -, hC5⟩ := factors12_curved_cube5 (ell := ell) (m := m) (R := R) hell (le_trans hm₁ hm) hR21 ha₀
  have hmain := hU (MXQ.Total.famPhi (M12.Phi12 ell)) (fun L s j f hx => hx) m hm R (le_trans (le_max_left _ _) hR) k (by omega) Lu α₀
    hα hα12l hT S hA Lam hL U hCQ
  exact ⟨k, Lu, S, Lam, U, α₀, Bt, hk, hT, hLu, hgt, hA, hL, hα, hα12l, hCQ, hcv, hnp, hLam, hOT, hOT2, hen, hBt, hC5,
    hmain.1, hmain.2 Bt hOT hOT2⟩

end M12NV

#print axioms M12NV.cube5_both_factors
#print axioms M12NV.factors12_curved_cube5
#print axioms M12NV.factors12_instance_inequality_cube5
