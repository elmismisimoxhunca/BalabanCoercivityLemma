set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## A. Finite-dimensional topology -/
section Topo

theorem tendsto_of_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {α : Type*} {l : Filter α} {g : α → E} {g₀ : E}
    (h : ∀ w : E, Tendsto (fun a => ⟪w, g a⟫) l (𝓝 ⟪w, g₀⟫)) : Tendsto g l (𝓝 g₀) := by
  let b := stdOrthonormalBasis ℝ E
  have e : ∀ x : E, x = ∑ i, ⟪b i, x⟫ • b i := fun x => (b.sum_repr' x).symm
  rw [e g₀]
  have hg : g = fun a => ∑ i, ⟪b i, g a⟫ • b i := funext fun a => e (g a)
  rw [hg]
  exact tendsto_finsetSum _ (fun i _ => (h (b i)).smul_const (b i))

theorem tendsto_clm_of_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : Type*} {l : Filter α} {f : α → E →L[ℝ] F} {f₀ : E →L[ℝ] F}
    (h : ∀ x, Tendsto (fun a => f a x) l (𝓝 (f₀ x))) : Tendsto f l (𝓝 f₀) := by
  let b := stdOrthonormalBasis ℝ E
  have e : ∀ g : E →L[ℝ] F, g = ∑ i, (innerSL ℝ (b i)).smulRight (g (b i)) := by
    intro g
    ext x
    have hx : x = ∑ i, ⟪b i, x⟫ • b i := (b.sum_repr' x).symm
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
    conv_lhs => rw [hx]
    simp only [map_sum, map_smul]
  rw [e f₀]
  have hf : f = fun a => ∑ i, (innerSL ℝ (b i)).smulRight (f a (b i)) := funext fun a => e (f a)
  rw [hf]
  refine tendsto_finsetSum _ (fun i _ => ?_)
  exact ((ContinuousLinearMap.smulRightL ℝ E F (innerSL ℝ (b i))).continuous.tendsto _).comp (h (b i))

theorem tendsto_clm_of_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] {α : Type*} {l : Filter α} {f : α → E →L[ℝ] F} {f₀ : E →L[ℝ] F}
    (h : ∀ x y, Tendsto (fun a => ⟪y, f a x⟫) l (𝓝 ⟪y, f₀ x⟫)) : Tendsto f l (𝓝 f₀) :=
  tendsto_clm_of_apply (fun x => tendsto_of_inner (fun y => h x y))

end Topo

/-! ## B. `𝔰𝔲(2)`-valued fields -/
section SuTwoFields

open AdalyFormal.Balaban.CovariantOperators (SuTwo)

theorem inner_suTwo (X Y : SuTwo) :
    ⟪X, Y⟫ = -(1 / 2 : ℝ) * (Matrix.trace ((X : Matrix (Fin 2) (Fin 2) ℂ) *
      (Y : Matrix (Fin 2) (Fin 2) ℂ))).re := rfl

theorem tendsto_suTwo_of_coe {α : Type*} {l : Filter α} {g : α → SuTwo} {g₀ : SuTwo}
    (h : Tendsto (fun a => ((g a : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) l
      (𝓝 ((g₀ : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ))) : Tendsto g l (𝓝 g₀) := by
  apply tendsto_of_inner
  intro w
  simp only [inner_suTwo]
  have hc : Continuous fun Y : Matrix (Fin 2) (Fin 2) ℂ =>
      -(1 / 2 : ℝ) * (Matrix.trace ((w : Matrix (Fin 2) (Fin 2) ℂ) * Y)).re :=
    continuous_const.mul (Complex.continuous_re.comp
      ((continuous_const.matrix_mul continuous_id).matrix_trace))
  exact (hc.tendsto _).comp h

theorem continuous_suTwo_of_coe {X : Type*} [TopologicalSpace X] {g : X → SuTwo}
    (h : Continuous fun x => ((g x : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) : Continuous g :=
  continuous_iff_continuousAt.mpr fun x => tendsto_suTwo_of_coe (h.tendsto x)

theorem tendsto_piLp_suTwo {ι : Type*} [Fintype ι] {α : Type*} {l : Filter α}
    {g : α → PiLp 2 (fun _ : ι => SuTwo)} {g₀ : PiLp 2 (fun _ : ι => SuTwo)}
    (h : ∀ i, Tendsto (fun a => ((WithLp.ofLp (g a) i : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) l
      (𝓝 ((WithLp.ofLp g₀ i : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ))) : Tendsto g l (𝓝 g₀) := by
  apply tendsto_of_inner
  intro w
  simp only [PiLp.inner_apply]
  refine tendsto_finsetSum _ (fun i _ => ?_)
  have hi := tendsto_suTwo_of_coe (h i)
  exact ((continuous_const.inner continuous_id).tendsto _).comp hi

theorem continuous_piLp_suTwo {ι : Type*} [Fintype ι] {X : Type*} [TopologicalSpace X]
    {g : X → PiLp 2 (fun _ : ι => SuTwo)}
    (h : ∀ i, Continuous fun x => ((WithLp.ofLp (g x) i : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) :
    Continuous g :=
  continuous_iff_continuousAt.mpr fun x => tendsto_piLp_suTwo (fun i => (h i).tendsto x)

theorem continuous_coe_suTwo {X : Type*} [TopologicalSpace X] {g : X → SuTwo} (h : Continuous g) :
    Continuous fun x => ((g x : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) :=
  continuous_subtype_val.comp h

end SuTwoFields

/-! ## C. Site-level operators along a continuous family of link configurations -/
section Family

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_coe_apply gradValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.D1Literal (ContFam SU2m)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy)
open AdalyFormal.Balaban.QjComposite (stepAverage)

variable {L : PeriodicLatticeExtent}

theorem cont_coarsePathHolonomy {V : ℝ → Cfg L} (hV : ContFam V) (s : ℕ) (p : List (Fin 3)) :
    ∀ y, Continuous fun ε => ((coarsePathHolonomy s (V ε) y p : SU2m) :
      Matrix (Fin 2) (Fin 2) ℂ) := by
  induction p with
  | nil =>
    intro y
    exact continuous_const
  | cons μ rest ih =>
    intro y
    show Continuous fun ε => (((V ε (y, μ)) * coarsePathHolonomy s (V ε)
      (AdalyFormal.Balaban.CoarseCurl.coarseShift y s μ) rest : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)
    exact (hV _).matrix_mul (ih _)

theorem cont_RMap_coe {X : Type*} [TopologicalSpace X] {g : X → SU2m}
    (hg : Continuous fun ε => ((g ε : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) {Y : X → SuTwo}
    (hY : Continuous fun ε => ((Y ε : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) :
    Continuous fun ε => ((RMap (g ε) (Y ε) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have e : (fun ε => ((RMap (g ε) (Y ε) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun ε => (g ε : Matrix (Fin 2) (Fin 2) ℂ) * (Y ε : Matrix (Fin 2) (Fin 2) ℂ) *
        star ((g ε : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext ε
    exact RMap_coe_apply _ _
  rw [e]
  exact (hg.matrix_mul hY).matrix_mul hg.star

theorem cont_gradL2 {V : ℝ → Cfg L} (hV : ContFam V) : Continuous fun ε => gradL2 (V ε) := by
  refine continuous_clm_apply.mpr (fun f => ?_)
  refine continuous_piLp_suTwo (fun b => ?_)
  show Continuous fun ε => ((gradValueCovariant (V ε) (WithLp.ofLp f) b : SuTwo) :
    Matrix (Fin 2) (Fin 2) ℂ)
  unfold gradValueCovariant
  simp only [Submodule.coe_sub]
  exact (cont_RMap_coe (hV b) continuous_const).sub continuous_const

theorem cont_adjoint {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] :
    Continuous fun M : E →L[ℝ] F => ContinuousLinearMap.adjoint M :=
  (ContinuousLinearMap.adjoint : (E →L[ℝ] F) ≃ₗᵢ⋆[ℝ] (F →L[ℝ] E)).continuous

theorem cont_gradAdj {V : ℝ → Cfg L} (hV : ContFam V) : Continuous fun ε => gradAdj (V ε) :=
  cont_adjoint.comp (cont_gradL2 hV)

theorem cont_lapFull {V : ℝ → Cfg L} (hV : ContFam V) : Continuous fun ε => lapFull (V ε) :=
  (cont_gradAdj hV).clm_comp (cont_gradL2 hV)

theorem Qcomposite_one' (bg : ℕ → Cfg L) (ell : ℕ) (lam : PeriodicLatticeSite L → SuTwo) :
    AdalyFormal.Balaban.QjComposite.Qcomposite bg ell 1 lam = stepAverage (ell ^ 0) (bg 0) ell lam :=
  rfl

theorem bgTower_zero' (G : TowerGeom L) (U : Cfg L) : bgTower G U 0 = U := rfl

theorem cont_Qlev {V : ℝ → Cfg L} (hV : ContFam V) (G : TowerGeom L) {j : ℕ} (hj : j ≤ 1)
    (y : PeriodicLatticeSite L) : Continuous fun ε => Qlev G (V ε) j y := by
  refine continuous_clm_apply.mpr (fun f => ?_)
  refine continuous_suTwo_of_coe ?_
  simp only [Qlev_apply]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · simp only [AdalyFormal.Balaban.QjComposite.Qcomposite_zero]
    exact continuous_const
  · simp only [Qcomposite_one', bgTower_zero', stepAverage, Submodule.coe_smul, Submodule.coe_sum]
    exact continuous_const.smul (continuous_finsetSum _ (fun x _ =>
      cont_RMap_coe (cont_coarsePathHolonomy hV _ _ _) continuous_const))

theorem cont_Qpa {V : ℝ → Cfg L} (hV : ContFam V) (G : TowerGeom L) (hk : G.k = 1) (a : ℝ) :
    Continuous fun ε => Qpa G (V ε) a := by
  classical
  unfold Qpa
  refine continuous_finsetSum _ (fun j hj => continuous_finsetSum _ (fun y _ => ?_))
  have hj1 : j ≤ 1 := by rw [Finset.mem_range] at hj; omega
  by_cases hy : y ∈ G.Lam j
  · simp only [hy, if_true]
    exact continuous_const.smul ((cont_adjoint.comp (cont_Qlev hV G hj1 y)).clm_comp
      (cont_Qlev hV G hj1 y))
  · simp only [hy, if_false]
    exact continuous_const

theorem cont_DelpA {V : ℝ → Cfg L} (hV : ContFam V) (G : TowerGeom L) (hk : G.k = 1) (a : ℝ) :
    Continuous fun ε => DelpA G (V ε) a := by
  unfold DelpA
  exact (continuous_const.clm_comp ((cont_lapFull hV).add (cont_Qpa hV G hk a))).clm_comp
    continuous_const

open AdalyFormal.M1Site in
theorem cont_LP {V : ℝ → Cfg L} (hV : ContFam V) (G : TowerGeom L) (hk : G.k = 1) (a : ℝ) :
    Continuous fun ε => LP G (V ε) a := by
  unfold LP
  exact (cont_DelpA hV G hk a).add continuous_const

open AdalyFormal.M1Site in
theorem cont_QpP {V : ℝ → Cfg L} (hV : ContFam V) (G : TowerGeom L) (hk : G.k = 1) (a : ℝ) :
    Continuous fun ε => QpP G (V ε) a := by
  refine continuous_clm_apply.mpr (fun f => ?_)
  refine continuous_piLp_suTwo (fun p => ?_)
  cases p with
  | inl q =>
    have hj : q.1.1.val ≤ 1 := by have := q.1.1.isLt; omega
    simp only [QpP_inl, Submodule.coe_smul]
    exact continuous_const.smul (continuous_coe_suTwo
      ((cont_Qlev hV G hj _).clm_apply continuous_const))
  | inr x =>
    simp only [QpP_inr]
    exact continuous_const

end Family

/-! ## D. The gauge projection, `W` and `T` near a configuration where the constraint Gram is a unit

The frozen `M1Site.Rproj_eq_strat` gives `R v = v - X Γ⁻¹ X* v`, `X = (Δ'_a + 1 - Ω₀)⁻¹ Q'*`,
`Γ = X* X`, at every configuration where `Δ'_a + 1 - Ω₀` and `Γ` are units.  Both conditions are open,
so near such a configuration the projection is a continuous expression. -/
section Gauge

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.M1Site
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.D1Literal (ContFam SU2m)

variable {L : PeriodicLatticeExtent}

/-- `Γ = X* X`. -/
noncomputable def Gam (G : TowerGeom L) (U : Cfg L) (a : ℝ) : YP G →L[ℝ] YP G :=
  ContinuousLinearMap.adjoint (Xop G U a) ∘L Xop G U a

theorem Rproj_formula (G : TowerGeom L) (U : Cfg L) (a : ℝ) (hw : ∀ j, 0 < wq G a j)
    (hu : IsUnit (LP G U a)) (hΓ : IsUnit (Gam G U a)) :
    Rproj G U = 1 - Xop G U a ∘L (Ring.inverse (Gam G U a) ∘L
      ContinuousLinearMap.adjoint (Xop G U a)) := by
  have hG1 : ∀ u, (ContinuousLinearMap.adjoint (Xop G U a) ∘L Xop G U a)
      (Ring.inverse (Gam G U a) u) = u := by
    intro u
    have h := Ring.mul_inverse_cancel _ hΓ
    exact congrArg (fun T : YP G →L[ℝ] YP G => T u) h
  ext1 v
  rw [Rproj_eq_strat G U a hw hu _ hG1 v]
  simp only [sub_apply, one_apply_eq_self,
    ContinuousLinearMap.comp_apply]

theorem continuousAt_inverse_comp {X : Type*} [TopologicalSpace X] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : X → E →L[ℝ] E} {x₀ : X} (hf : ContinuousAt f x₀) (hu : IsUnit (f x₀)) :
    ContinuousAt (fun x => Ring.inverse (f x)) x₀ := by
  have h1 := NormedRing.inverse_continuousAt hu.unit
  rw [hu.unit_spec] at h1
  exact h1.comp hf

theorem continuousAt_clm_comp {X : Type*} [TopologicalSpace X] {E F G' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G'] [NormedSpace ℝ G'] {g : X → F →L[ℝ] G'} {f : X → E →L[ℝ] F} {x₀ : X}
    (hg : ContinuousAt g x₀) (hf : ContinuousAt f x₀) :
    ContinuousAt (fun x => (g x).comp (f x)) x₀ := by
  have hc : Continuous (fun p : (F →L[ℝ] G') × (E →L[ℝ] F) => p.1.comp p.2) :=
    continuous_fst.clm_comp continuous_snd
  exact (hc.tendsto (g x₀, f x₀)).comp (hg.prodMk_nhds hf)

section
variable {V : ℝ → Cfg L} (hV : ContFam V) (G : TowerGeom L) (hk : G.k = 1) (a : ℝ) {ε₀ : ℝ}
  (hu : IsUnit (LP G (V ε₀) a))
include hV hk hu

theorem continuousAt_LinvP : ContinuousAt (fun ε => LinvP G (V ε) a) ε₀ :=
  continuousAt_inverse_comp (cont_LP hV G hk a).continuousAt hu

theorem continuousAt_Xop : ContinuousAt (fun ε => Xop G (V ε) a) ε₀ :=
  continuousAt_clm_comp (continuousAt_LinvP hV G hk a hu)
    (cont_adjoint.comp (cont_QpP hV G hk a)).continuousAt

theorem continuousAt_Gam : ContinuousAt (fun ε => Gam G (V ε) a) ε₀ :=
  continuousAt_clm_comp (cont_adjoint.continuousAt.comp (continuousAt_Xop hV G hk a hu))
    (continuousAt_Xop hV G hk a hu)

variable (hw : ∀ j, 0 < wq G a j) (hΓ : IsUnit (Gam G (V ε₀) a))
include hw hΓ

theorem continuousAt_Rproj : ContinuousAt (fun ε => Rproj G (V ε)) ε₀ := by
  have hX := continuousAt_Xop hV G hk a hu
  have hGc := continuousAt_Gam hV G hk a hu
  have hGi := continuousAt_inverse_comp hGc hΓ
  have hF : ContinuousAt (fun ε => (1 : SiteL2 L →L[ℝ] SiteL2 L) - Xop G (V ε) a ∘L
      (Ring.inverse (Gam G (V ε) a) ∘L ContinuousLinearMap.adjoint (Xop G (V ε) a))) ε₀ :=
    continuousAt_const.sub (continuousAt_clm_comp hX
      (continuousAt_clm_comp hGi (cont_adjoint.continuousAt.comp hX)))
  have h1 : ∀ᶠ ε in 𝓝 ε₀, IsUnit (LP G (V ε) a) :=
    ((cont_LP hV G hk a).tendsto ε₀).eventually
      ((Units.isOpen (R := SiteL2 L →L[ℝ] SiteL2 L)).mem_nhds hu)
  have h2 : ∀ᶠ ε in 𝓝 ε₀, IsUnit (Gam G (V ε) a) :=
    hGc.eventually ((Units.isOpen (R := YP G →L[ℝ] YP G)).mem_nhds hΓ)
  refine hF.congr ?_
  filter_upwards [h1, h2] with ε hε1 hε2
  exact (Rproj_formula G (V ε) a hw hε1 hε2).symm

theorem continuousAt_Tfull : ContinuousAt (fun ε => Tfull G (V ε)) ε₀ :=
  continuousAt_clm_comp (continuousAt_Rproj hV G hk a hu hw hΓ) (cont_gradAdj hV).continuousAt

theorem continuousAt_Wop : ContinuousAt (fun ε => Wop G (V ε) a) ε₀ := by
  have hR := continuousAt_Rproj hV G hk a hu hw hΓ
  have hL := continuousAt_LinvP hV G hk a hu
  unfold Wop
  exact continuousAt_const.sub (continuousAt_clm_comp (cont_gradL2 hV).continuousAt
    (continuousAt_clm_comp (continuousAt_clm_comp hL continuousAt_const)
      (continuousAt_clm_comp hR (cont_gradAdj hV).continuousAt)))

end

end Gauge

/-! ## E. The Dirichlet operator is a unit at every configuration (frozen `CvOX1`, outside the
`DrEquiv` closure; statements and proofs copied verbatim up to the namespace) -/
section DirichletUnit

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap gradValueCovariant)
open AdalyFormal.Balaban.SuTwoInner (hsInner hsInner_RMap hsInner_self_nonneg hsInner_self_eq_zero)

open Fin.NatCast

variable {L : PeriodicLatticeExtent}

theorem ajSeq_pos {a : ℝ} (ha : 0 < a) {ell : ℕ} (hell : 2 ≤ ell) (j : ℕ) : 0 < ajSeq a ell j := by
  unfold ajSeq
  split_ifs with h
  · exact ha
  · unfold AdalyFormal.Balaban.ConstantA.aSeq
    have hl : (2 : ℝ) ≤ ell := by exact_mod_cast hell
    have hpos : (0 : ℝ) < (ell : ℝ) * ell := by positivity
    have hd : 0 < a / ((ell : ℝ) * ell) := by positivity
    have h4 : (4 : ℝ) ≤ (ell : ℝ) * ell := by nlinarith
    have hda : a / ((ell : ℝ) * ell) < a := by
      rw [div_lt_iff₀ hpos]; nlinarith [mul_le_mul_of_nonneg_left h4 ha.le]
    exact AdalyFormal.Balaban.ConstantA.aSeqAux_pos a _ ha hd hda _

theorem Qpa_nonneg (G : TowerGeom L) (U : Cfg L) {a : ℝ} (ha : 0 < a) (hell : 2 ≤ G.ell) (f : SiteL2 L) :
    0 ≤ ⟪f, Qpa G U a f⟫ := by
  rw [inner_Qpa]
  refine Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun y _ => ?_))
  split_ifs
  · exact mul_nonneg (mul_nonneg (ajSeq_pos ha hell j).le (pow_nonneg (Nat.cast_nonneg _) _)) (sq_nonneg _)
  · exact le_rfl


theorem delpA_inner_ge (G : TowerGeom L) (U : Cfg L) {a : ℝ} (ha : 0 < a) (hell : 2 ≤ G.ell) (f : SiteL2 L) :
    ‖gradL2 U (siteMask G.Om0 f)‖ ^ 2 + ‖f - siteMask G.Om0 f‖ ^ 2 ≤ ⟪f, (DelpA G U a + (1 - siteMask G.Om0)) f⟫ := by
  set m := siteMask G.Om0 with hm
  have hsym : ∀ u v : SiteL2 L, ⟪m u, v⟫ = ⟪u, m v⟫ := fun u v => siteMask_symm _ u v
  have hidem : ∀ u : SiteL2 L, m (m u) = m u := fun u => siteMask_idem _ u
  have e1 : ⟪f, DelpA G U a f⟫ = ⟪m f, lapFull U (m f)⟫ + ⟪m f, Qpa G U a (m f)⟫ := by
    unfold DelpA
    simp only [ContinuousLinearMap.comp_apply, add_apply]
    rw [← hsym, inner_add_right]
  have e2 : ⟪f, ((1 : SiteL2 L →L[ℝ] SiteL2 L) - m) f⟫ = ‖f - m f‖ ^ 2 := by
    simp only [sub_apply, one_apply_eq_self]
    rw [← real_inner_self_eq_norm_sq]
    have h0 : ⟪m f, f - m f⟫ = 0 := by
      rw [inner_sub_right]
      have a1 : ⟪m f, m f⟫ = ⟪f, m f⟫ := by rw [hsym, hidem]
      have a2 : ⟪m f, f⟫ = ⟪f, m f⟫ := real_inner_comm _ _
      rw [a1, a2, sub_self]
    have hdec : f = (f - m f) + m f := by abel
    calc ⟪f, f - m f⟫ = ⟪(f - m f) + m f, f - m f⟫ := by rw [← hdec]
      _ = ⟪f - m f, f - m f⟫ := by rw [inner_add_left, h0, add_zero]
  have e3 : ⟪m f, lapFull U (m f)⟫ = ‖gradL2 U (m f)‖ ^ 2 := by
    unfold lapFull gradAdj
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  have e4 := Qpa_nonneg G U ha hell (m f)
  show _ ≤ ⟪f, DelpA G U a f + ((1 : SiteL2 L →L[ℝ] SiteL2 L) - m) f⟫
  rw [inner_add_right, e1, e2, e3]
  linarith

/-- covariantly constant site fields have constant `hsInner (f x) (f x)`. -/
theorem covConst_norm (U : Cfg L) (f : SiteL2 L) (h : gradL2 U f = 0) (x y : PeriodicLatticeSite L) :
    hsInner (f x) (f x) = hsInner (f y) (f y) := by
  have hb : ∀ b : AdalyFormal.Balaban.AdmissibleSubspace.Bond L, RMap (U b) (f (periodicLatticeShift b.1 b.2)) = f b.1 := by
    intro b
    have := congrFun (congrArg WithLp.ofLp h) b
    rw [gradL2_apply] at this
    simp only [gradValueCovariant] at this
    exact sub_eq_zero.mp this
  have hstep : ∀ (z : PeriodicLatticeSite L) (μ : Fin 3), hsInner (f (periodicLatticeShift z μ)) (f (periodicLatticeShift z μ)) = hsInner (f z) (f z) := by
    intro z μ
    have := hb (z, μ)
    simp only [] at this
    rw [← hsInner_RMap (U (z, μ)) (f (periodicLatticeShift z μ)) (f (periodicLatticeShift z μ)), this]
  have hiter : ∀ (z : PeriodicLatticeSite L) (μ : Fin 3) (j : ℕ),
      hsInner (f (Function.update z μ (z μ + (Nat.cast j : Fin (L μ + 1))))) (f (Function.update z μ (z μ + (Nat.cast j : Fin (L μ + 1))))) = hsInner (f z) (f z) := by
    intro z μ j
    induction j with
    | zero => simp
    | succ j ih =>
      have : Function.update z μ (z μ + (Nat.cast (j + 1) : Fin (L μ + 1))) =
          periodicLatticeShift (Function.update z μ (z μ + (Nat.cast j : Fin (L μ + 1)))) μ := by
        unfold periodicLatticeShift
        rw [Function.update_self, Function.update_idem]
        congr 1
        rw [Nat.cast_succ]
        abel
      rw [this, hstep, ih]
  have hupd : ∀ (z : PeriodicLatticeSite L) (μ : Fin 3) (v : Fin (L μ + 1)),
      hsInner (f (Function.update z μ v)) (f (Function.update z μ v)) = hsInner (f z) (f z) := by
    intro z μ v
    have := hiter z μ (v - z μ).val
    rw [Fin.cast_val_eq_self, add_sub_cancel] at this
    exact this
  have hall : ∀ z w : PeriodicLatticeSite L, hsInner (f w) (f w) = hsInner (f z) (f z) := by
    intro z w
    have hw : w = Function.update (Function.update (Function.update z 0 (w 0)) 1 (w 1)) 2 (w 2) := by
      funext ν
      fin_cases ν <;> simp [Function.update]
    rw [hw, hupd, hupd, hupd]
  exact (hall x y).symm

theorem delpA_unit (G : TowerGeom L) (U : Cfg L) {a : ℝ} (ha : 0 < a) (hell : 2 ≤ G.ell)
    (hout : ∃ x : PeriodicLatticeSite L, x ∉ G.Om0) :
    IsUnit (DelpA G U a + (1 - siteMask G.Om0)) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  set X : SiteL2 L →L[ℝ] SiteL2 L := DelpA G U a + (1 - siteMask G.Om0) with hX
  have hinj : Function.Injective X := by
    refine (injective_iff_map_eq_zero X).mpr (fun f hf => ?_)
    have h1 := delpA_inner_ge G U ha hell f
    rw [hf, inner_zero_right] at h1
    have hs1 := sq_nonneg ‖gradL2 U (siteMask G.Om0 f)‖
    have hs2 := sq_nonneg ‖f - siteMask G.Om0 f‖
    have hD : ‖gradL2 U (siteMask G.Om0 f)‖ ^ 2 = 0 := by linarith
    have hR : ‖f - siteMask G.Om0 f‖ ^ 2 = 0 := by linarith
    have hfm : f = siteMask G.Om0 f :=
      sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff (two_ne_zero)).mp hR))
    have hDm : gradL2 U (siteMask G.Om0 f) = 0 := norm_eq_zero.mp ((pow_eq_zero_iff (two_ne_zero)).mp hD)
    have hDf : gradL2 U f = 0 := by rw [← hfm] at hDm; exact hDm
    obtain ⟨x0, hx0⟩ := hout
    have hx0f : f x0 = 0 := by
      have : (siteMask G.Om0 f) x0 = 0 := by rw [siteMask_apply, if_neg hx0]
      rw [← hfm] at this; exact this
    ext x
    have := covConst_norm U f hDf x x0
    rw [hx0f] at this
    have h0 : hsInner (f x) (f x) = 0 := by
      rw [this]; exact AdalyFormal.Balaban.DeltaKU.hsInner_zero_right _
    have := hsInner_self_eq_zero h0
    simp [this]
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (X : SiteL2 L →ₗ[ℝ] SiteL2 L))).mp hinj⟩


theorem wq_pos (G : TowerGeom L) {a : ℝ} (ha : 0 < a) (hell : 2 ≤ G.ell) (j : ℕ) :
    0 < AdalyFormal.M1Site.wq G a j := by
  unfold AdalyFormal.M1Site.wq
  have : (0 : ℝ) < G.ell := by exact_mod_cast (by omega : 0 < G.ell)
  exact mul_pos (ajSeq_pos ha hell j) (pow_pos this j)

end DirichletUnit

end AdalyFormal.Round9.Guarded.AnalyticR2
