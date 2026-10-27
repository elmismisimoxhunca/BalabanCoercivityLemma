import ZT5F

/-!
# ZT5G -- `GuardsUnit` (the three `Ring.inverse` units of `WellDefG`) at the flat FULL TOWER, every `k`, `ell ≥ 2`, `a > 0`.
Extends `PK_wellDef` (GU1I): `WellDefG = WellDef ∧ GuardsUnit`; the guards were proved only at the flat single-level tower (`P1_guards`, `k = 0`).
Components (as in `ZT4F.GuardsUnit`): (1) `Δ'_a|Ω₀ + pad` is a unit, (2) `G⁻¹ = Ginv` of (3.122) is a unit, (3) `Q G Q*` is a unit.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.GenuineU1

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.QjComposite (Qcomposite)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

theorem ajSeq_pos (ell : ℕ) (hell2 : 2 ≤ ell) {a : ℝ} (ha : 0 < a) (j : ℕ) : 0 < ajSeq a ell j := by
  unfold ajSeq
  split_ifs with h
  · exact ha
  · have hl : (2 : ℝ) ≤ ell := by exact_mod_cast hell2
    have hl2 : (4 : ℝ) ≤ (ell : ℝ) * ell := by nlinarith
    have hd : 0 < a / ((ell : ℝ) * ell) := by positivity
    have hda : a / ((ell : ℝ) * ell) < a := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    exact AdalyFormal.Balaban.ConstantA.aSeqAux_pos a (a / ((ell : ℝ) * ell)) ha hd hda (j - 1)

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
  (Lam : Set (PeriodicLatticeSite Lu))

local notation "PP" => PK ell k Lu hell a Lam


/-- (2) `G⁻¹` of (3.122) equals `G₁⁻¹` at the flat point (`Δ⁽²⁾ = 0`), hence is a unit -/
theorem PK_ginv_eq (hN : ∀ μ, 1 ≤ Lu μ) (ha : 0 < a) : (PP).G1inv = (PP).data.Ginv := by
  have h1 := (PP).data.G1inv_unique (PP).G1inv_spec ((PP).data.isG1inv_sub (PP).data_laws)
  rw [h1, PK_Delta2_zero ell k Lu hell a Lam, sub_zero]

theorem PK_isUnit_Ginv (hN : ∀ μ, 1 ≤ Lu μ) (ha : 0 < a) : IsUnit (PP).data.Ginv := by
  rw [← PK_ginv_eq ell k Lu hell a Lam hN ha]
  exact PK_isUnit_G1inv ell k Lu hell a Lam hN ha

/-- (3) `Q G Q*` is a unit -/
theorem PK_isUnit_QGQs (hN : ∀ μ, 1 ≤ Lu μ) (ha : 0 < a) :
    IsUnit (((PP).data.Q.comp (PP).data.G).comp (PP).data.Qs) := by
  obtain ⟨c, hc, hco⟩ := PK_G1inv_coercive ell k Lu hell a Lam hN ha
  rw [PK_ginv_eq ell k Lu hell a Lam hN ha] at hco
  exact isUnit_Q_inv_Qs (fun x y => (PP).data.Ginv_symm (PP).data_laws x y) hc hco (PP).data.Q_adj
    (PK_Qs_injective ell k Lu hell a Lam)


/-- (1) `Δ'_a|Ω₀ + pad` is a unit at the flat full tower (`Ω₀ = torus`, so the pad vanishes; positive definite: `grad f = 0` forces `f` constant, and the
level-`k` block mean of a constant is the constant, with weight `a_k ell^k > 0`) -/
theorem PK_delp_unit (hell2 : 2 ≤ ell) (ha : 0 < a) :
    IsUnit (DelpA (PP).G (PP).U (PP).a + (1 - siteMask (PP).G.Om0)) := by
  classical
  have e : DelpA (PP).G (PP).U (PP).a + (1 - siteMask (PP).G.Om0) = DelpA (PP).G (PP).U (PP).a := by
    have hOm' : (PP).G.Om0 = Set.univ := G_Om0 ell k Lu
    rw [hOm']
    refine ContinuousLinearMap.ext (fun f => ?_)
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    rw [siteMask_univ, sub_self, add_zero]
  rw [e]
  change IsUnit (DelpA (geomOf ell k (fullTower ell k Lu)) flatCfg a)
  have hell' : 0 < ell := hell
  set G : TowerGeom (scaleUp ell k Lu) := geomOf ell k (fullTower ell k Lu) with hGdef
  have hGe : G.ell = ell := rfl
  have hGk : G.k = k := rfl
  have hOm : G.Om0 = Set.univ := G_Om0 ell k Lu
  have hD : ∀ f, DelpA G flatCfg a f = lapFull flatCfg f + Qpa G flatCfg a f := by
    intro f
    unfold DelpA
    simp only [ContinuousLinearMap.comp_apply]
    rw [hOm, siteMask_univ, siteMask_univ]
    rfl
  have hbg : ∀ j, bgTower G flatCfg j = trivialU (scaleUp ell k Lu) := by
    intro j; exact bgTower_PK ell k Lu hell a Lam j
  have hinj : ∀ f, DelpA G flatCfg a f = 0 → f = 0 := by
    intro f hf
    have h0 : ⟪f, lapFull flatCfg f + Qpa G flatCfg a f⟫ = 0 := by
      rw [← hD, hf, inner_zero_right]
    rw [inner_add_right, inner_lapFull, inner_Qpa] at h0
    have hc : ∀ j, 0 ≤ ajSeq a G.ell j * (G.ell : ℝ) ^ j := fun j => by
      rw [hGe]; exact mul_nonneg (ajSeq_pos ell hell2 ha j).le (by positivity)
    have hterm : ∀ j : ℕ, ∀ y : PeriodicLatticeSite (scaleUp ell k Lu),
        0 ≤ (if y ∈ G.Lam j then (ajSeq a G.ell j * (G.ell : ℝ) ^ j) * ‖Qlev G flatCfg j y f‖ ^ 2 else 0) := by
      intro j y
      split_ifs
      · exact mul_nonneg (hc j) (sq_nonneg _)
      · exact le_rfl
    obtain ⟨hgz, hSz⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _)
      (Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun y _ => hterm j y)))).mp h0
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Finset.sum_nonneg (fun y _ => hterm j y))).mp hSz k
      (Finset.mem_range.mpr (by rw [hGk]; exact Nat.lt_succ_self k))
    let y0 : PeriodicLatticeSite (scaleUp ell k Lu) := fun μ => ⟨0, Nat.succ_pos _⟩
    have hy0Lam : y0 ∈ G.Lam k := by
      refine ⟨fun μ => by simp [y0], ?_, ?_⟩
      · show y0 ∈ (fullTower ell k Lu).Om k
        simp [fullTower]
      · show y0 ∉ (fullTower ell k Lu).Om (k + 1)
        simp [fullTower]
    have hy0 := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hterm k y)).mp hj y0 (Finset.mem_univ _)
    rw [if_pos hy0Lam] at hy0
    have hgrad0 : gradL2 (AdalyFormal.GenuineU1H.flatU (scaleUp ell k Lu)) f = 0 :=
      norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hgz)
    obtain ⟨X, hX⟩ := AdalyFormal.GenuineU1H.K3 f hgrad0
    have hyc : y0 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ k) := by
      rw [mem_CoarseLattice]; intro ν; simp [y0]
    have hq : Qlev G flatCfg k y0 f = X := by
      rw [Qlev_apply]
      have hq0 := Qcomposite_closed ell hell (bgTower G flatCfg) hbg k (scaleUp_tiling ell k Lu hell)
        (WithLp.ofLp f) k le_rfl (ell ^ k) rfl y0 hyc
      rw [hGe]
      refine hq0.trans ?_
      have hsum : ∑ x ∈ blockOf y0 (ell ^ k), (WithLp.ofLp f) x = ((ell ^ k) ^ 3 : ℕ) • X := by
        calc ∑ x ∈ blockOf y0 (ell ^ k), (WithLp.ofLp f) x = ∑ x ∈ blockOf y0 (ell ^ k), X :=
              Finset.sum_congr rfl (fun x _ => hX x)
          _ = ((ell ^ k) ^ 3 : ℕ) • X := by
              rw [Finset.sum_const,
                AdalyFormal.Balaban.AdmissibleSubspace.card_blockOf_of_coarse (scaleUp_tiling ell k Lu hell) hyc]
      have hne : ((ell ^ k : ℕ) : ℝ) ≠ 0 := by positivity
      have hkey : (1 / ((ell ^ k : ℕ) : ℝ) ^ 3) • (((ell ^ k) ^ 3 : ℕ) • X) = X := by
        rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
        have : (1 / ((ell ^ k : ℕ) : ℝ) ^ 3) * (((ell ^ k) ^ 3 : ℕ) : ℝ) = 1 := by
          push_cast; field_simp
        rw [this, one_smul]
      rw [hsum]
      exact hkey
    have hpos : 0 < ajSeq a G.ell k * (G.ell : ℝ) ^ k := by
      rw [hGe]
      exact mul_pos (ajSeq_pos ell hell2 ha k) (by positivity)
    have hnX : ‖Qlev G flatCfg k y0 f‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp hy0 with h | h
      · exact absurd h hpos.ne'
      · exact h
    rw [hq] at hnX
    have hX0 : X = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hnX)
    ext x
    rw [hX x, hX0]; rfl
  have hinjM : Function.Injective (DelpA G flatCfg a) := by
    rw [injective_iff_map_eq_zero]; exact hinj
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr
    ⟨hinjM, (LinearMap.injective_iff_surjective (f := (DelpA G flatCfg a).toLinearMap)).mp hinjM⟩

/-- **`GuardsUnit` at the flat full tower, every `k`** -/
theorem PK_guardsUnit (hell2 : 2 ≤ ell) (hN : ∀ μ, 1 ≤ Lu μ) (ha : 0 < a) : GenP.GuardsUnit (PP) :=
  ⟨PK_delp_unit ell k Lu hell a Lam hell2 ha, PK_isUnit_Ginv ell k Lu hell a Lam hN ha,
    PK_isUnit_QGQs ell k Lu hell a Lam hN ha⟩

/-- **`WellDefG` at the flat full tower, every `k`** -/
theorem PK_wellDefG (hell2 : 2 ≤ ell) (hN : ∀ μ, 1 ≤ Lu μ) (hdvd : ∀ μ, ell ∣ Lu μ + 1) (ha : 0 < a) :
    GenP.WellDefG (PP) :=
  ⟨PK_wellDef ell k Lu hell a Lam hN hdvd ha, PK_guardsUnit ell k Lu hell a Lam hell2 hN ha⟩

end

#print axioms ajSeq_pos
#print axioms PK_isUnit_Ginv
#print axioms PK_isUnit_QGQs
#print axioms PK_delp_unit
#print axioms PK_guardsUnit
#print axioms PK_wellDefG

end AdalyFormal.GenuineU1
