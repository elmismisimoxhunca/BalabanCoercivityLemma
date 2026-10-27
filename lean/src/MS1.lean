import DLR24

/-!
# MS1 -- S4 (PLAN.md §1.2 Layer S): the DL23/DL24 identities for a GENERAL `TowerGeom` (Dirichlet `Ω₀`, stratified `Q'`)

DL21/DL23/DL24 proved `DelpA_eq_L`, `Rproj_eq`, `Tfull_eq_T`, `Wop_eq_W` at the full tower (`Ω₀ = univ`, only `Λ_k ≠ ∅`).
Here `G : TowerGeom L` is arbitrary.  The constraint map is the stratified `Q'` of (3.21): one row per `(j, y)`, `j ≤ k`,
`y ∈ Λ_j`, weighted by `√(a_j ℓ^j)` (the weights of `Qpa`, ZR2Ops2), PADDED by the Dirichlet rows `f ↦ f(x)`, `x ∉ Ω₀`:
* `QIdx G`, `OffIdx G`, `YP G = L²(QIdx ⊕ OffIdx)`;  `QpP G U a : SiteL2 → YP G`;  `Dm G U = D_U ∘ Ω₀`.
* `LP G U a := DelpA + (1 − Ω₀)` (the operator whose `Ring.inverse` defines `Gp`);  `LinvP := Ring.inverse LP`, so
  `Gp = LinvP ∘ Ω₀` (`Gp_eq`, rfl).
* **`inner_LP`** / **`LP_eq_L`** : `LP = Dm*Dm + QpP*QpP` (general-tower `DelpA_eq_L`, padded);
  **`DelpA_eq_L_strat`** : `⟪g, DelpA f⟫ = ⟪D Ω₀g, D Ω₀f⟫ + Σ_{(j,y)} a_jℓ^j ⟪Q'_j(y)Ω₀g, Q'_j(y)Ω₀f⟫` (unpadded form).
* `QpP_eq_zero_iff` : `QpP μ = 0 ↔ μ ∈ N(Q')` (needs `a_jℓ^j > 0`);  `LP_of_NQp` : `LP μ = lapDir μ` on `N(Q')`.
* **`Rproj_eq_strat`** : `R v = v − XΓ⁻¹X*v`, `X = LinvP QpP*`, `Γ = X*X`, for every `v` (no mask needed: the padding rows
  make `range X ⊇ L²(Ω₀ᶜ)`).
* **`Tfull_eq_T_strat`**, **`Wop_eq_W_strat`** : for ANY DL13 `GamHyp` on `(SiteL2, BondFnL2, YP G)` whose operators are
  `D = Dm`, `Qp = QpP`, `Linv = LinvP`: `Tfull = T`, `Wop = W`.
* `LP_isUnit_of_coercive`, `exists_Gami_of_ext` : non-vacuity inputs (a GamHyp-type `Gami` exists once `QpP` has a
  right inverse with an energy bound).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M1Site

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

variable {L : PeriodicLatticeExtent}

/-- constraint rows of `Q'` (3.21): `(j, y)` with `j ≤ k`, `y ∈ Λ_j`. -/
def QIdx (G : TowerGeom L) : Type := {p : Fin (G.k + 1) × PeriodicLatticeSite L // p.2 ∈ G.Lam p.1.val}

/-- Dirichlet padding rows: the sites off `Ω₀`. -/
def OffIdx (G : TowerGeom L) : Type := {x : PeriodicLatticeSite L // x ∉ G.Om0}

open Classical in
noncomputable instance instFintypeQIdx (G : TowerGeom L) : Fintype (QIdx G) := by
  unfold QIdx; exact Subtype.fintype _

open Classical in
noncomputable instance instFintypeOffIdx (G : TowerGeom L) : Fintype (OffIdx G) := by
  unfold OffIdx; exact Subtype.fintype _

/-- padded row index -/
abbrev PIdx (G : TowerGeom L) : Type := QIdx G ⊕ OffIdx G

/-- the padded constraint space `L²(rows)` -/
abbrev YP (G : TowerGeom L) : Type := PiLp 2 (fun _ : PIdx G => SuTwo)

/-- the row weight `a_j ℓ^j` of `Qpa` (ZR2Ops2). -/
noncomputable def wq (G : TowerGeom L) (a : ℝ) (j : ℕ) : ℝ := ajSeq a G.ell j * (G.ell : ℝ) ^ j

/-- the padded, weighted, stratified constraint map. -/
noncomputable def QpP (G : TowerGeom L) (U : Cfg L) (a : ℝ) : SiteL2 L →L[ℝ] YP G :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 (Sum.elim
        (fun q : QIdx G => Real.sqrt (wq G a q.1.1.val) • Qlev G U q.1.1.val q.1.2 (siteMask G.Om0 f))
        (fun x : OffIdx G => f x.1))
      map_add' := fun f g => by
        refine PiLp.ext (fun p => ?_)
        cases p <;> simp [map_add, smul_add]
      map_smul' := fun c f => by
        refine PiLp.ext (fun p => ?_)
        cases p <;> simp [map_smul, smul_comm c] }

theorem QpP_inl (G : TowerGeom L) (U : Cfg L) (a : ℝ) (f : SiteL2 L) (q : QIdx G) :
    QpP G U a f (Sum.inl q) = Real.sqrt (wq G a q.1.1.val) • Qlev G U q.1.1.val q.1.2 (siteMask G.Om0 f) := rfl

theorem QpP_inr (G : TowerGeom L) (U : Cfg L) (a : ℝ) (f : SiteL2 L) (x : OffIdx G) :
    QpP G U a f (Sum.inr x) = f x.1 := rfl

/-- the masked gradient `D ∘ Ω₀` -/
noncomputable def Dm (G : TowerGeom L) (U : Cfg L) : SiteL2 L →L[ℝ] BondFnL2 L :=
  gradL2 U ∘L siteMask G.Om0

/-- `Δ'_a + (1 − Ω₀)`: the operator inverted in `Gp` -/
noncomputable def LP (G : TowerGeom L) (U : Cfg L) (a : ℝ) : SiteL2 L →L[ℝ] SiteL2 L :=
  DelpA G U a + (1 - siteMask G.Om0)

noncomputable def LinvP (G : TowerGeom L) (U : Cfg L) (a : ℝ) : SiteL2 L →L[ℝ] SiteL2 L :=
  Ring.inverse (LP G U a)

theorem Gp_eq (G : TowerGeom L) (U : Cfg L) (a : ℝ) : Gp G U a = LinvP G U a ∘L siteMask G.Om0 := rfl

/-- `X = LinvP QpP*` -/
noncomputable def Xop (G : TowerGeom L) (U : Cfg L) (a : ℝ) : YP G →L[ℝ] SiteL2 L :=
  LinvP G U a ∘L ContinuousLinearMap.adjoint (QpP G U a)

/-! ## 1. masks -/

theorem siteMask_adjoint (S : Set (PeriodicLatticeSite L)) :
    ContinuousLinearMap.adjoint (siteMask S) = siteMask S := by
  ext1 f
  refine ext_inner_left ℝ (fun g => ?_)
  rw [ContinuousLinearMap.adjoint_inner_right, siteMask_symm]

theorem siteMask_off (S : Set (PeriodicLatticeSite L)) (f : SiteL2 L) (x : PeriodicLatticeSite L) (hx : x ∉ S) :
    siteMask S f x = 0 := by
  classical
  rw [siteMask_apply, if_neg hx]

theorem siteMask_on (S : Set (PeriodicLatticeSite L)) (f : SiteL2 L) (x : PeriodicLatticeSite L) (hx : x ∈ S) :
    siteMask S f x = f x := by
  classical
  rw [siteMask_apply, if_pos hx]

theorem siteMask_eq_self (S : Set (PeriodicLatticeSite L)) (f : SiteL2 L) (hf : ∀ x, x ∉ S → f x = 0) :
    siteMask S f = f := by
  classical
  refine PiLp.ext (fun x => ?_)
  rw [siteMask_apply]
  split_ifs with h
  · rfl
  · exact (hf x h).symm

/-- `⟪g, f − Ω₀ f⟫ = Σ_{x ∉ Ω₀} ⟪g x, f x⟫` -/
theorem inner_one_sub_mask (G : TowerGeom L) (f g : SiteL2 L) :
    ⟪g, (1 - siteMask G.Om0) f⟫ = ∑ x : OffIdx G, ⟪g x.1, f x.1⟫ := by
  classical
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, PiLp.inner_apply]
  have e : ∀ x : PeriodicLatticeSite L, ⟪g x, (f - siteMask G.Om0 f) x⟫
      = if x ∉ G.Om0 then ⟪g x, f x⟫ else 0 := by
    intro x
    rw [PiLp.sub_apply]
    by_cases hx : x ∈ G.Om0
    · rw [siteMask_on _ _ _ hx, sub_self, inner_zero_right, if_neg (not_not.mpr hx)]
    · rw [siteMask_off _ _ _ hx, sub_zero, if_pos hx]
  rw [Finset.sum_congr rfl (fun x _ => e x), ← Finset.sum_filter]
  exact Finset.sum_subtype (p := fun x => x ∉ G.Om0) _ (fun x => by simp) (fun x => ⟪g x, f x⟫)

/-! ## 2. the stratified `Qpa` as a row sum -/

open Classical in
theorem inner_Qpa_rows (G : TowerGeom L) (U : Cfg L) (a : ℝ) (g f : SiteL2 L) :
    ⟪g, Qpa G U a f⟫ = ∑ q : QIdx G, wq G a q.1.1.val * ⟪Qlev G U q.1.1.val q.1.2 g, Qlev G U q.1.1.val q.1.2 f⟫ := by
  have h1 : ⟪g, Qpa G U a f⟫ = ∑ j ∈ Finset.range (G.k + 1), ∑ y : PeriodicLatticeSite L,
      if y ∈ G.Lam j then wq G a j * ⟪Qlev G U j y g, Qlev G U j y f⟫ else 0 := by
    simp only [Qpa, ContinuousLinearMap.sum_apply, inner_sum]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun y _ => ?_))
    split_ifs
    · simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, real_inner_smul_right,
        ContinuousLinearMap.adjoint_inner_right, wq]
    · simp
  rw [h1, ← Fin.sum_univ_eq_sum_range (fun j => ∑ y : PeriodicLatticeSite L,
      if y ∈ G.Lam j then wq G a j * ⟪Qlev G U j y g, Qlev G U j y f⟫ else 0)]
  rw [← Fintype.sum_prod_type' (fun (j : Fin (G.k + 1)) (y : PeriodicLatticeSite L) =>
      if y ∈ G.Lam j.val then wq G a j.val * ⟪Qlev G U j.val y g, Qlev G U j.val y f⟫ else 0)]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (p := fun p : Fin (G.k + 1) × PeriodicLatticeSite L => p.2 ∈ G.Lam p.1.val) _
    (fun p => by simp) (fun p => wq G a p.1.val * ⟪Qlev G U p.1.val p.2 g, Qlev G U p.1.val p.2 f⟫)

/-- **general-tower `DelpA_eq_L` (unpadded form)**. -/
theorem DelpA_eq_L_strat (G : TowerGeom L) (U : Cfg L) (a : ℝ) (g f : SiteL2 L) :
    ⟪g, DelpA G U a f⟫ = ⟪Dm G U g, Dm G U f⟫
      + ∑ q : QIdx G, wq G a q.1.1.val *
          ⟪Qlev G U q.1.1.val q.1.2 (siteMask G.Om0 g), Qlev G U q.1.1.val q.1.2 (siteMask G.Om0 f)⟫ := by
  unfold DelpA
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← siteMask_symm,
    ContinuousLinearMap.add_apply, inner_add_right, inner_Qpa_rows]
  congr 1
  simp only [Dm, lapFull, gradAdj, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]

theorem inner_QpP (G : TowerGeom L) (U : Cfg L) (a : ℝ) (hw : ∀ j, 0 ≤ wq G a j) (g f : SiteL2 L) :
    ⟪QpP G U a g, QpP G U a f⟫ = ∑ q : QIdx G, wq G a q.1.1.val *
          ⟪Qlev G U q.1.1.val q.1.2 (siteMask G.Om0 g), Qlev G U q.1.1.val q.1.2 (siteMask G.Om0 f)⟫
      + ∑ x : OffIdx G, ⟪g x.1, f x.1⟫ := by
  rw [PiLp.inner_apply, Fintype.sum_sum_type]
  congr 1
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [QpP_inl, QpP_inl, real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
    Real.mul_self_sqrt (hw _)]

/-- **general-tower `DelpA_eq_L` (padded form)**: `⟪g, LP f⟫ = ⟪Dm g, Dm f⟫ + ⟪QpP g, QpP f⟫`. -/
theorem inner_LP (G : TowerGeom L) (U : Cfg L) (a : ℝ) (hw : ∀ j, 0 ≤ wq G a j) (g f : SiteL2 L) :
    ⟪g, LP G U a f⟫ = ⟪Dm G U g, Dm G U f⟫ + ⟪QpP G U a g, QpP G U a f⟫ := by
  rw [LP, ContinuousLinearMap.add_apply, inner_add_right, DelpA_eq_L_strat, inner_QpP G U a hw,
    inner_one_sub_mask]
  ring

theorem LP_eq_L (G : TowerGeom L) (U : Cfg L) (a : ℝ) (hw : ∀ j, 0 ≤ wq G a j) :
    LP G U a = ContinuousLinearMap.adjoint (Dm G U) ∘L Dm G U
      + ContinuousLinearMap.adjoint (QpP G U a) ∘L QpP G U a := by
  ext1 f
  refine ext_inner_left ℝ (fun g => ?_)
  rw [inner_LP G U a hw]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    inner_add_right, ContinuousLinearMap.adjoint_inner_right]

theorem LP_symm (G : TowerGeom L) (U : Cfg L) (a : ℝ) (hw : ∀ j, 0 ≤ wq G a j) (f g : SiteL2 L) :
    ⟪LP G U a f, g⟫ = ⟪f, LP G U a g⟫ := by
  rw [real_inner_comm, inner_LP G U a hw, inner_LP G U a hw, real_inner_comm (Dm G U g),
    real_inner_comm (QpP G U a g)]

/-! ## 3. `N(Q')` = kernel of the padded map -/

theorem QpP_eq_zero_iff (G : TowerGeom L) (U : Cfg L) (a : ℝ) (hw : ∀ j, 0 < wq G a j) (μ : SiteL2 L) :
    QpP G U a μ = 0 ↔ μ ∈ NQp G U := by
  constructor
  · intro h
    have hoff : ∀ x, x ∉ G.Om0 → μ x = 0 := by
      intro x hx
      have := congrArg (fun v : YP G => v (Sum.inr ⟨x, hx⟩)) h
      simpa [QpP_inr] using this
    refine ⟨hoff, fun j hj y hy => ?_⟩
    have := congrArg (fun v : YP G => v (Sum.inl ⟨(⟨j, Nat.lt_succ_of_le hj⟩, y), hy⟩)) h
    simp only [QpP_inl, PiLp.zero_apply] at this
    rw [siteMask_eq_self _ _ hoff] at this
    have hs : Real.sqrt (wq G a j) ≠ 0 := (Real.sqrt_pos.mpr (hw j)).ne'
    exact (smul_eq_zero.mp this).resolve_left hs
  · intro h
    refine PiLp.ext (fun p => ?_)
    cases p with
    | inl q =>
      rw [QpP_inl, siteMask_eq_self _ _ h.1, h.2 q.1.1.val (Nat.lt_succ_iff.mp q.1.1.isLt) q.1.2 q.2, smul_zero]
      rfl
    | inr x => rw [QpP_inr, h.1 x.1 x.2]; rfl

theorem Qpa_of_NQp (G : TowerGeom L) (U : Cfg L) (a : ℝ) (μ : SiteL2 L) (hμ : μ ∈ NQp G U) :
    Qpa G U a μ = 0 := by
  refine ext_inner_left ℝ (fun g => ?_)
  rw [inner_Qpa_rows, inner_zero_right]
  refine Finset.sum_eq_zero (fun q _ => ?_)
  rw [hμ.2 q.1.1.val (Nat.lt_succ_iff.mp q.1.1.isLt) q.1.2 q.2, inner_zero_right, mul_zero]

theorem LP_of_NQp (G : TowerGeom L) (U : Cfg L) (a : ℝ) (μ : SiteL2 L) (hμ : μ ∈ NQp G U) :
    LP G U a μ = lapDir G U μ := by
  have hm : siteMask G.Om0 μ = μ := siteMask_eq_self _ _ hμ.1
  simp only [LP, DelpA, lapDir, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hm, sub_self, add_zero, map_add,
    Qpa_of_NQp G U a μ hμ, map_zero]

/-! ## 4. the inverse -/

section inv
variable (G : TowerGeom L) (U : Cfg L) (a : ℝ) (hu : IsUnit (LP G U a))
include hu

theorem LP_LinvP (x : SiteL2 L) : LP G U a (LinvP G U a x) = x := by
  have h := Ring.mul_inverse_cancel _ hu
  have := congrArg (fun T : SiteL2 L →L[ℝ] SiteL2 L => T x) h
  simpa [LinvP] using this

theorem LinvP_LP (x : SiteL2 L) : LinvP G U a (LP G U a x) = x := by
  have h := Ring.inverse_mul_cancel _ hu
  have := congrArg (fun T : SiteL2 L →L[ℝ] SiteL2 L => T x) h
  simpa [LinvP] using this

variable (hw : ∀ j, 0 ≤ wq G a j)
include hw

theorem LinvP_symm (x y : SiteL2 L) : ⟪LinvP G U a x, y⟫ = ⟪x, LinvP G U a y⟫ := by
  conv_lhs => rw [← LP_LinvP G U a hu y]
  rw [← LP_symm G U a hw, LP_LinvP G U a hu]

theorem LinvP_adjoint : ContinuousLinearMap.adjoint (LinvP G U a) = LinvP G U a := by
  ext1 f
  refine ext_inner_left ℝ (fun g => ?_)
  rw [ContinuousLinearMap.adjoint_inner_right, LinvP_symm G U a hu hw]

theorem adjXop_apply (v : SiteL2 L) :
    ContinuousLinearMap.adjoint (Xop G U a) v = QpP G U a (LinvP G U a v) := by
  rw [Xop, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, LinvP_adjoint G U a hu hw]
  rfl

theorem LP_Xop (z : YP G) : LP G U a (Xop G U a z) = ContinuousLinearMap.adjoint (QpP G U a) z := by
  rw [Xop, ContinuousLinearMap.comp_apply, LP_LinvP G U a hu]

end inv

/-! ## 5. the gauge-fixing projection in closed form, general tower -/

/-- elements of `Δ_U N(Q')` are supported in `Ω₀` -/
theorem RImage_mask (G : TowerGeom L) (U : Cfg L) (w : SiteL2 L) (hw : w ∈ RImage G U) :
    siteMask G.Om0 w = w := by
  obtain ⟨μ, -, rfl⟩ := Submodule.mem_map.mp hw
  show siteMask G.Om0 (lapDir G U μ) = lapDir G U μ
  simp only [lapDir, ContinuousLinearMap.comp_apply, siteMask_idem]

theorem Rproj_mask_right (G : TowerGeom L) (U : Cfg L) (v : SiteL2 L) :
    Rproj G U (siteMask G.Om0 v) = Rproj G U v := by
  show (RImage G U).starProjection (siteMask G.Om0 v) = Rproj G U v
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.starProjection_apply_mem _ _) ?_
  intro w hw
  have h1 : ⟪v - Rproj G U v, w⟫ = 0 := Submodule.starProjection_inner_eq_zero v w hw
  have h2 : ⟪v - siteMask G.Om0 v, w⟫ = 0 := by
    rw [← RImage_mask G U w hw, ← siteMask_symm, map_sub, siteMask_idem, sub_self, inner_zero_left]
  have e : siteMask G.Om0 v - Rproj G U v = (v - Rproj G U v) - (v - siteMask G.Om0 v) := by abel
  rw [e, inner_sub_left, h1, h2, sub_zero]

theorem Rproj_mask_left (G : TowerGeom L) (U : Cfg L) (v : SiteL2 L) :
    siteMask G.Om0 (Rproj G U v) = Rproj G U v :=
  RImage_mask G U _ (Submodule.starProjection_apply_mem _ _)

/-- **`Rproj_eq_strat`**: `R v = v − X Γ⁻¹ X* v` at every tower. -/
theorem Rproj_eq_strat (G : TowerGeom L) (U : Cfg L) (a : ℝ) (hw : ∀ j, 0 < wq G a j) (hu : IsUnit (LP G U a))
    (Gi : YP G →L[ℝ] YP G)
    (hG1 : ∀ u, (ContinuousLinearMap.adjoint (Xop G U a) ∘L Xop G U a) (Gi u) = u) (v : SiteL2 L) :
    Rproj G U v = v - Xop G U a (Gi (ContinuousLinearMap.adjoint (Xop G U a) v)) := by
  have hw0 : ∀ j, 0 ≤ wq G a j := fun j => (hw j).le
  set X := Xop G U a with hX
  set z := Gi (ContinuousLinearMap.adjoint X v) with hz
  show (RImage G U).starProjection v = _
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · set lam := LinvP G U a (v - X z) with hlam
    have hQ : QpP G U a lam = 0 := by
      have e1 : QpP G U a lam = ContinuousLinearMap.adjoint X (v - X z) := by
        rw [hX, adjXop_apply G U a hu hw0]
      rw [e1, map_sub]
      have e2 : ContinuousLinearMap.adjoint X (X z) = ContinuousLinearMap.adjoint X v := by
        have := hG1 (ContinuousLinearMap.adjoint X v)
        rw [ContinuousLinearMap.comp_apply] at this
        rw [hz]; exact this
      rw [e2, sub_self]
    have hmem : lam ∈ NQp G U := (QpP_eq_zero_iff G U a hw lam).mp hQ
    refine Submodule.mem_map.mpr ⟨lam, hmem, ?_⟩
    show lapDir G U lam = v - X z
    rw [← LP_of_NQp G U a lam hmem, hlam, LP_LinvP G U a hu]
  · intro w hw'
    obtain ⟨μ, hμ, hμw⟩ := Submodule.mem_map.mp hw'
    rw [← hμw]
    show ⟪v - (v - X z), lapDir G U μ⟫ = 0
    rw [sub_sub_cancel, ← LP_of_NQp G U a μ hμ, ← LP_symm G U a hw0, hX, LP_Xop G U a hu hw0,
      ContinuousLinearMap.adjoint_inner_left, (QpP_eq_zero_iff G U a hw μ).mpr hμ, inner_zero_right]

/-! ## 6. `Tfull = T`, `Wop = W` for the abstract DL13/DL15 objects, general tower -/

section abstract
open AdalyFormal.DLayer

variable (G : TowerGeom L) (U : Cfg L) (a : ℝ) (hw : ∀ j, 0 < wq G a j) (hu : IsUnit (LP G U a))
  (H : GamHyp (SiteL2 L) (BondFnL2 L) (YP G))
  (hD : H.D = Dm G U) (hQ : H.Qp = QpP G U a) (hL : H.Linv = LinvP G U a)
include hw hu hD hQ hL

theorem Dm_adjoint : ContinuousLinearMap.adjoint (Dm G U) = siteMask G.Om0 ∘L gradAdj U := by
  rw [Dm, ContinuousLinearMap.adjoint_comp, siteMask_adjoint]
  rfl

theorem Tfull_eq_T_strat : Tfull G U = H.T := by
  have hG1 := H.hG1
  rw [hL, hQ] at hG1
  have hX : H.H.X = Xop G U a := by
    show H.Linv ∘L ContinuousLinearMap.adjoint H.Qp = _
    rw [hL, hQ]; rfl
  ext1 A
  have hR := Rproj_eq_strat G U a hw hu H.Gami hG1 (siteMask G.Om0 (gradAdj U A))
  have hDA : ContinuousLinearMap.adjoint H.D A = siteMask G.Om0 (gradAdj U A) := by
    rw [hD, Dm_adjoint G U a hw hu H hD hQ hL]; rfl
  calc Tfull G U A = Rproj G U (gradAdj U A) := rfl
    _ = Rproj G U (siteMask G.Om0 (gradAdj U A)) := (Rproj_mask_right G U _).symm
    _ = siteMask G.Om0 (gradAdj U A)
          - Xop G U a (H.Gami (ContinuousLinearMap.adjoint (Xop G U a) (siteMask G.Om0 (gradAdj U A)))) := hR
    _ = H.T A := by
      simp only [GamHyp.T, GamHyp.F, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.adjoint_comp, hX, hDA]

theorem Wop_eq_W_strat : Wop G U a = H.W := by
  have hT := Tfull_eq_T_strat G U a hw hu H hD hQ hL
  have hw0 : ∀ j, 0 ≤ wq G a j := fun j => (hw j).le
  ext1 A
  have key : siteMask G.Om0 (LinvP G U a (Rproj G U (gradAdj U A)))
      = LinvP G U a (siteMask G.Om0 (Rproj G U (gradAdj U A))) := by
    have h := (Gp_spec G U a hu (Rproj G U (gradAdj U A))).1
    rw [Gp_eq, ContinuousLinearMap.comp_apply, Rproj_mask_left] at h
    rw [Rproj_mask_left]
    exact h
  simp only [GamHyp.W, GamHyp.Z, ← hT, hD, hL, Dm, Wop, Tfull, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.one_apply, Gp_eq]
  rw [key]

end abstract

#print axioms siteMask_adjoint
#print axioms inner_one_sub_mask
#print axioms inner_Qpa_rows
#print axioms DelpA_eq_L_strat
#print axioms inner_QpP
#print axioms inner_LP
#print axioms LP_eq_L
#print axioms LP_symm
#print axioms QpP_eq_zero_iff
#print axioms Qpa_of_NQp
#print axioms LP_of_NQp
#print axioms LinvP_symm
#print axioms LinvP_adjoint
#print axioms adjXop_apply
#print axioms Rproj_mask_right
#print axioms Rproj_mask_left
#print axioms Rproj_eq_strat
#print axioms Tfull_eq_T_strat
#print axioms Wop_eq_W_strat

#print axioms QpP_inl
#print axioms QpP_inr
#print axioms Gp_eq
#print axioms siteMask_off
#print axioms siteMask_on
#print axioms siteMask_eq_self
#print axioms LP_LinvP
#print axioms LinvP_LP
#print axioms LP_Xop
#print axioms RImage_mask
#print axioms Dm_adjoint

end AdalyFormal.M1Site
