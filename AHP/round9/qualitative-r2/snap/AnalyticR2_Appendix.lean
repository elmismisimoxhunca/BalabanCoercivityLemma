
/-!
Round 9 (analytic route, pass 2): the soft premise of pass 1 is a theorem.

Pass 1 (`AnalyticR1`) reduced `GoalNeg2` to `InteriorSoft ∧ VacuumLeftSpectral`.  This
appendix proves `InteriorSoft`: along the curved dilated family `ε ↦ dilU q R ε 1` (curvature
on the round-4 defect line, trivial exterior), for every scale `q > 0` and every even radius
`R ≥ 18`, the all-plaquette carrier and the dressing `W` are continuous at `ε = 0`, and the
localized correction satisfies `Δ⁽²⁾(ε)/ε → D₁`.  The proof is soft analysis of the frozen
assembly:
* the gauge projection is written with the frozen closed form `M1Site.Rproj_eq_strat`
  (`R = 1 - X Γ⁻¹ X*`), continuous where the Dirichlet operator and `Γ` are units;
* the raw blocking step is jointly smooth in (curvature, field) (the frozen `SG` calculus
  over the parameter space `ℝ × X`), so its first and second field jets are continuous;
* the localized source is smooth in the curvature and vanishes at the flat point;
* at the flat point the Dirichlet operator, `Γ` (frozen `MS6.exists_Gami_strat`) and `Q*`
  (frozen `W6F.qs_injective_strat`) are units/injective, and the flat localized carrier of
  the dilated tower is positive definite: a vanishing form forces a curl-free field, which
  is the gradient of an explicit longitudinal potential; the level-1 constraint rows
  telescope along the longitudinal chain of blocks, and the frozen final step applies.

Consequences: `goalNeg2_of_vacuumLeftSpectral : VacuumLeftSpectral → GoalNeg2` and
`cofinalTwistSeparation_of_twistVacuumCrossing : CofinalTwistVacuumCrossing →
CofinalTwistSeparation`.  Both premises are spectral statements about the vacuum (zero
curvature) operators only.  Neither premise is proved here; no pinned goal is proved here.
-/
set_option autoImplicit false
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

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## F. Jets of the raw averaging along a smooth family of backgrounds

The frozen `SG` calculus (`R2Raw3`, `R2RawX`) is stated over an arbitrary normed parameter space.
Taking the parameter space `ℝ × X` (curvature, coordinate field), the frozen proof of `SG_rawStep`
goes through with the background varying smoothly: the raw one-step averaging is jointly smooth in
(curvature, field) at `(0, 0)` whenever the background at curvature `0` is regular.  Its first and
second field derivatives at the zero field (the printed jets `QlinStepL`, `D2StepL`) are therefore
continuous in the curvature at `0` (`ContDiffAt.fderiv`). -/
section Jets

open scoped Matrix Matrix.Norms.Frobenius
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge cPlusS coarseBondVar gammaVarStrided loopVar)

variable {L : PeriodicLatticeExtent}

theorem tendsto_clm_of_apply' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : Type*} {l : Filter α} {f : α → E →L[ℝ] F} {f₀ : E →L[ℝ] F}
    (h : ∀ x, Tendsto (fun a => f a x) l (𝓝 (f₀ x))) : Tendsto f l (𝓝 f₀) := by
  let b := Module.finBasis ℝ E
  let c : Fin (Module.finrank ℝ E) → E →L[ℝ] ℝ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  have e : ∀ g : E →L[ℝ] F, g = ∑ i, (c i).smulRight (g (b i)) := by
    intro g
    ext x
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, c,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul]
  rw [e f₀]
  have hf : f = fun a => ∑ i, (c i).smulRight (f a (b i)) := funext fun a => e (f a)
  rw [hf]
  refine tendsto_finsetSum _ (fun i _ => ?_)
  exact ((ContinuousLinearMap.smulRightL ℝ E F (c i)).continuous.tendsto _).comp (h (b i))

/-- Smooth links at curvature `0` (Frobenius matrix norm). -/
def SmoothAt0 (V : ℝ → PeriodicLinkConfiguration SU2 L) : Prop :=
  ∀ b, ContDiffAt ℝ ⊤ (fun ε => ((V ε b : SU2) : M2)) 0

section Fam
variable (V : ℝ → PeriodicLinkConfiguration SU2 L) (hV : SmoothAt0 V)

include hV in
theorem SG_V0 (b : PeriodicLatticeEdge L) : SG (fun q : ℝ × XS L => V q.1 b) := by
  show ContDiffAt ℝ ⊤ (fun q : ℝ × XS L => ((V q.1 b : SU2) : M2)) 0
  exact ContDiffAt.comp (g := fun ε : ℝ => ((V ε b : SU2) : M2)) (f := fun q : ℝ × XS L => q.1)
    (0 : ℝ × XS L) (hV b) contDiffAt_fst

theorem SG_V1 (b : PeriodicLatticeEdge L) : SG (fun q : ℝ × XS L => expCfgX q.2 b) := by
  have h : ContDiffAt ℝ ⊤ (fun a : XS L => ((expCfgX a b : SU2) : M2)) 0 := SG_expCfgX b
  show ContDiffAt ℝ ⊤ (fun q : ℝ × XS L => ((expCfgX q.2 b : SU2) : M2)) 0
  exact ContDiffAt.comp (g := fun a : XS L => ((expCfgX a b : SU2) : M2)) (f := fun q : ℝ × XS L => q.2)
    (0 : ℝ × XS L) h contDiffAt_snd

include hV in
theorem SG_prod (b : PeriodicLatticeEdge L) :
    SG (fun q : ℝ × XS L => expCfgX q.2 b * V q.1 b) :=
  (SG_V1 b).mul (SG_V0 V hV b)

theorem SG_loopVar_fam (s ell : ℕ) (W : ℝ × XS L → PeriodicLinkConfiguration SU2 L)
    (hW : ∀ b, SG (fun q => W q b)) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) :
    SG (fun q => loopVar s ell (W q) c x) := by
  unfold loopVar gammaVarStrided coarseBondVar
  have h := fun (p : List (Fin 3)) (y : PeriodicLatticeSite L) => SG.hol s W hW p y
  exact (((h _ _).mul (h _ _)).mul (h _ _).inv).mul (h _ _).inv

theorem SG_sbg_fam (s ell : ℕ) (W : ℝ × XS L → PeriodicLinkConfiguration SU2 L)
    (hW : ∀ b, SG (fun q => W q b)) (c : PeriodicLatticeEdge L)
    (hreg : ∀ x ∈ stepBlockOf c.1 s ell, ((loopVar s ell (W 0) c x : SU2) : M2) ∈ LogReg) :
    SG (fun q => stridedBlockedGauge su2LogExp s ell (W q) c) := by
  unfold stridedBlockedGauge
  have h := fun (p : List (Fin 3)) (y : PeriodicLatticeSite L) => SG.hol s W hW p y
  refine SG.mul ?_ (by unfold coarseBondVar; exact h _ _)
  have := SG_su2Exp_sum_log (E := ℝ × XS L) (stepBlockOf c.1 s ell) (((ell : ℚ) ^ 3)⁻¹)
    (fun x q => loopVar s ell (W q) c x) (fun x _ => SG_loopVar_fam s ell W hW c x)
    (fun x hx => hreg x hx)
  simpa [su2LogExp_log, su2LogExp_exp] using this

include hV in
theorem SG_rProd_fam (s : ℕ) (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    SG (fun q : ℝ × XS L => rProd s (V q.1) (expCfgX q.2) y p) := by
  have h1 := SG.hol (E := ℝ × XS L) s (fun q => fun b => expCfgX q.2 b * V q.1 b)
    (fun b => SG_prod V hV b) p y
  have h2 := SG.hol (E := ℝ × XS L) s (fun q => V q.1) (fun b => SG_V0 V hV b) p y
  have e : (fun q : ℝ × XS L => rProd s (V q.1) (expCfgX q.2) y p)
      = fun q => coarsePathHolonomy s (fun b => expCfgX q.2 b * V q.1 b) y p *
          (coarsePathHolonomy s (V q.1) y p)⁻¹ := by
    funext q
    exact rProd_eq s (V q.1) (expCfgX q.2) y p
  rw [e]
  exact SG.mul_inv h1 h2

include hV in
theorem SG_su2Exp_sBlock_fam (s ell : ℕ) (y : PeriodicLatticeSite L) :
    SG (fun q : ℝ × XS L => su2Exp (sBlock s ell (V q.1) (expCfgX q.2) y)) := by
  unfold sBlock
  exact SG_su2Exp_sum_log (E := ℝ × XS L) (stepBlockOf y s ell) (((ell : ℚ) ^ 3)⁻¹)
    (fun x q => rProd s (V q.1) (expCfgX q.2) y (coarseGammaPath s y x))
    (fun x _ => SG_rProd_fam V hV s y _)
    (fun x _ => by
      show ((rProd s (V 0) (expCfgX (0 : XS L)) y _ : SU2) : M2) ∈ LogReg
      rw [rProd_expCfgX_zero]; exact one_mem_LogReg)

include hV in
theorem SG_su2Exp_neg_sBlock_fam (s ell : ℕ) (y : PeriodicLatticeSite L) :
    SG (fun q : ℝ × XS L => su2Exp (-(sBlock s ell (V q.1) (expCfgX q.2) y))) := by
  have := SG_su2Exp_sum_log (E := ℝ × XS L) (stepBlockOf y s ell) (-((ell : ℚ) ^ 3)⁻¹)
    (fun x q => rProd s (V q.1) (expCfgX q.2) y (coarseGammaPath s y x))
    (fun x _ => SG_rProd_fam V hV s y _)
    (fun x _ => by
      show ((rProd s (V 0) (expCfgX (0 : XS L)) y _ : SU2) : M2) ∈ LogReg
      rw [rProd_expCfgX_zero]; exact one_mem_LogReg)
  unfold sBlock
  simpa [neg_smul, Finset.sum_neg_distrib] using this

include hV in
/-- The raw one-step averaging is jointly smooth in (curvature, field) at `(0, 0)`. -/
theorem SG_rawStep_fam (s ell : ℕ) (hreg : RegBg s ell (V 0)) (c : PeriodicLatticeEdge L) :
    SG (fun q : ℝ × XS L => rawStep s ell (V q.1) (expCfgX q.2) c) := by
  have e : (fun q : ℝ × XS L => rawStep s ell (V q.1) (expCfgX q.2) c)
      = fun q => su2Exp (-(sBlock s ell (V q.1) (expCfgX q.2) c.1))
        * stridedBlockedGauge su2LogExp s ell (fun b => expCfgX q.2 b * V q.1 b) c
        * su2Exp (sBlock s ell (V q.1) (expCfgX q.2) (cPlusS s ell c))
        * (stridedBlockedGauge su2LogExp s ell (V q.1) c)⁻¹ := by
    funext q; exact rawStep_simp s ell (V q.1) (expCfgX q.2) c
  unfold SG; rw [e]
  have h1 := SG_su2Exp_neg_sBlock_fam V hV s ell c.1
  have h2 : SG (fun q : ℝ × XS L =>
      stridedBlockedGauge su2LogExp s ell (fun b => expCfgX q.2 b * V q.1 b) c) := by
    refine SG_sbg_fam s ell (fun q => fun b => expCfgX q.2 b * V q.1 b) (fun b => SG_prod V hV b) c ?_
    intro x hx
    have e0 : (fun b => expCfgX (0 : XS L) b * V 0 b) = V 0 := by
      funext b; rw [expCfgX_zero]; exact one_mul _
    show ((loopVar s ell (fun b => expCfgX ((0 : ℝ × XS L).2) b * V ((0 : ℝ × XS L).1) b) c x : SU2) : M2)
      ∈ LogReg
    rw [show ((0 : ℝ × XS L).2) = (0 : XS L) from rfl, show ((0 : ℝ × XS L).1) = (0 : ℝ) from rfl, e0]
    exact hreg c x hx
  have h3 := SG_su2Exp_sBlock_fam V hV s ell (cPlusS s ell c)
  have h4 : SG (fun q : ℝ × XS L => (stridedBlockedGauge su2LogExp s ell (V q.1) c)⁻¹) := by
    refine SG.inv (SG_sbg_fam s ell (fun q => V q.1) (fun b => SG_V0 V hV b) c ?_)
    intro x hx
    exact hreg c x hx
  exact (((h1.mul h2).mul h3).mul h4)

include hV in
theorem contDiffAt_qStep_fam (s ell : ℕ) (hreg : RegBg s ell (V 0)) (c : PeriodicLatticeEdge L) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × XS L => qStepX s ell (V q.1) q.2 c) 0 := by
  have h1 : ContDiffAt ℝ ⊤ (fun q : ℝ × XS L => su2Log (rawStep s ell (V q.1) (expCfgX q.2) c)) 0 :=
    AdalyFormal.Balaban.SmoothLog.su2Log_comp_contDiffAt
      (G := fun q : ℝ × XS L => rawStep s ell (V q.1) (expCfgX q.2) c)
      (SG_rawStep_fam V hV s ell hreg c) (rawStep_expCfgX_zero s ell (V 0) c)
  exact fromM2L.contDiff.contDiffAt.comp (0 : ℝ × XS L) h1

include hV in
/-- First jet: continuity in the curvature of the field derivative at the zero field. -/
theorem continuousAt_fderiv_qStep (s ell : ℕ) (hreg : RegBg s ell (V 0)) (c : PeriodicLatticeEdge L) :
    ContinuousAt (fun ε => fderiv ℝ (qStepComp s ell (V ε) c) 0) 0 := by
  have h := contDiffAt_qStep_fam V hV s ell hreg c
  have h2 : ContDiffAt ℝ 0 (fun ε : ℝ => fderiv ℝ (fun a : XS L => qStepX s ell (V ε) a c)
      ((fun _ : ℝ => (0 : XS L)) ε)) 0 :=
    ContDiffAt.fderiv (f := fun (ε : ℝ) (a : XS L) => qStepX s ell (V ε) a c)
      (g := fun _ : ℝ => (0 : XS L)) h contDiffAt_const (by simp)
  exact h2.continuousAt

include hV in
/-- Second jet: continuity in the curvature of the second field derivative at the zero field. -/
theorem continuousAt_fderiv2_qStep (s ell : ℕ) (hreg : RegBg s ell (V 0)) (c : PeriodicLatticeEdge L) :
    ContinuousAt (fun ε => fderiv ℝ (fderiv ℝ (qStepComp s ell (V ε) c)) 0) 0 := by
  have h := contDiffAt_qStep_fam V hV s ell hreg c
  have hl : ContDiffAt ℝ ⊤ (fun z : (ℝ × XS L) × XS L => ((z.1.1, z.2) : ℝ × XS L))
      ((0 : ℝ × XS L), (0 : XS L)) :=
    (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hΦ' : ContDiffAt ℝ ⊤ ((fun q : ℝ × XS L => qStepX s ell (V q.1) q.2 c) ∘
      (fun z : (ℝ × XS L) × XS L => ((z.1.1, z.2) : ℝ × XS L))) ((0 : ℝ × XS L), (0 : XS L)) :=
    ContDiffAt.comp (g := fun q : ℝ × XS L => qStepX s ell (V q.1) q.2 c)
      (f := fun z : (ℝ × XS L) × XS L => ((z.1.1, z.2) : ℝ × XS L)) ((0 : ℝ × XS L), (0 : XS L)) h hl
  have hΦ : ContDiffAt ℝ ⊤ (Function.uncurry fun (x : ℝ × XS L) (b : XS L) =>
      qStepX s ell (V x.1) b c) ((0 : ℝ × XS L), (fun x : ℝ × XS L => x.2) 0) := hΦ'
  have hΨ : ContDiffAt ℝ ⊤ (fun x : ℝ × XS L =>
      fderiv ℝ (fun b : XS L => qStepX s ell (V x.1) b c) x.2) 0 :=
    ContDiffAt.fderiv (f := fun (x : ℝ × XS L) (b : XS L) => qStepX s ell (V x.1) b c)
      (g := fun x : ℝ × XS L => x.2) hΦ contDiffAt_snd (by simp)
  have h2 : ContDiffAt ℝ 0 (fun ε : ℝ => fderiv ℝ (fun a : XS L =>
      fderiv ℝ (fun b : XS L => qStepX s ell (V ε) b c) a) ((fun _ : ℝ => (0 : XS L)) ε)) 0 :=
    ContDiffAt.fderiv (f := fun (ε : ℝ) (a : XS L) =>
        fderiv ℝ (fun b : XS L => qStepX s ell (V ε) b c) a)
      (g := fun _ : ℝ => (0 : XS L)) hΨ contDiffAt_const (by simp)
  exact h2.continuousAt

end Fam

end Jets

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## G. The assembled pinned data along a smooth curvature family

For a family `ε ↦ V ε` of backgrounds with smooth links and a regular flat point, on a tower of
depth one (`k = 1`): the bond-sector constraint map `Q` is continuous at `ε = 0`, the second jet
`C²` is jointly continuous, and every assembled carrier `dataS sD sJ` is continuous at `ε = 0` as
soon as `W` and `T` are.  The constrained inverse `H` is continuous wherever the carrier and
`Q G Q*` are units.  If the source `J` vanishes at `ε = 0` and has a curvature derivative, the
localized correction `Δ⁽²⁾(ε)/ε` converges. -/
section Assembly

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.D1Literal (ContFam)

variable {L : PeriodicLatticeExtent}

theorem tendsto_clm_apply₂ {α : Type*} {l : Filter α} {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : α → E →L[ℝ] F} {x : α → E}
    {f₀ : E →L[ℝ] F} {x₀ : E} (hf : Tendsto f l (𝓝 f₀)) (hx : Tendsto x l (𝓝 x₀)) :
    Tendsto (fun a => f a (x a)) l (𝓝 (f₀ x₀)) :=
  ((continuous_fst.clm_apply continuous_snd).tendsto (f₀, x₀)).comp (hf.prodMk_nhds hx)

/-- The coordinate map of `𝔰𝔲(2)`-valued bond fields, as a bounded operator. -/
noncomputable def suCoordL : BondFnL2 L →L[ℝ] XS L := LinearMap.toContinuousLinearMap suCoord

theorem QfullOf_apply (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L) (p : BIdx G) :
    WithLp.ofLp (QfullOf G U A) p
      = (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (QlinB G U p.1 A)) p.2.1 := rfl

theorem C2fullOf_apply (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L) (p : BIdx G) :
    WithLp.ofLp (C2fullOf G U A) p
      = (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (C2rawB G U p.1 A)) p.2.1 := rfl

theorem QlinB_one_coe (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L) (c : PeriodicLatticeEdge L) :
    ((WithLp.ofLp (QlinB G U 1 A) c : SuTwo) : M2) =
      toM2 (fderiv ℝ (qStepComp (G.ell ^ 0) G.ell U c) 0 (suCoord A)) := rfl

theorem C2rawB_zero' (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L) : C2rawB G U 0 A = 0 := by
  refine PiLp.ext (fun b => ?_)
  apply Subtype.ext
  show (((1 / 2 : ℝ) • suCoordInv (D2CompL G.ell (bgTower G U) 0 (suCoord A) (suCoord A))) b : M2) = 0
  simp [D2CompL, suCoordInv]

theorem C2rawB_one_coe (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L) (c : PeriodicLatticeEdge L) :
    ((WithLp.ofLp (C2rawB G U 1 A) c : SuTwo) : M2) =
      (1 / 2 : ℝ) • toM2 (fderiv ℝ (fderiv ℝ (qStepComp (G.ell ^ 0) G.ell U c)) 0
        (suCoord A) (suCoord A)) := by
  show (((1 / 2 : ℝ) • suCoordInv (D2CompL G.ell (bgTower G U) 1 (suCoord A) (suCoord A))) c : M2) = _
  simp only [D2CompL, LinearMap.mk₂_apply, QlinCompL_zero, ContinuousLinearMap.id_apply]
  simp [D2StepL_apply, suCoordInv]
  rfl

section BondSector
variable (V : ℝ → Cfg L) (hV : SmoothAt0 V)
  (G : TowerGeom L) (hk : G.k = 1) (hreg : RegBg (G.ell ^ 0) G.ell (V 0))

include hV hreg in
theorem tendsto_QlinB1_coe (A : BondFnL2 L) (c : PeriodicLatticeEdge L) :
    Tendsto (fun ε => ((WithLp.ofLp (QlinB G (V ε) 1 A) c : SuTwo) : M2)) (𝓝 0)
      (𝓝 ((WithLp.ofLp (QlinB G (V 0) 1 A) c : SuTwo) : M2)) := by
  simp only [QlinB_one_coe]
  have h := continuousAt_fderiv_qStep V hV (G.ell ^ 0) G.ell hreg c
  exact (toM2L.continuous.tendsto _).comp (tendsto_clm_apply₂ h tendsto_const_nhds)

include hV hreg hk in
theorem continuousAt_QfullOf : ContinuousAt (fun ε => QfullOf G (V ε)) 0 := by
  refine tendsto_clm_of_apply (fun A => tendsto_piLp_suTwo (fun p => ?_))
  obtain ⟨⟨j, hj⟩, r⟩ := p
  have hj1 : j = 0 ∨ j = 1 := by omega
  rcases hj1 with rfl | rfl
  · simp only [QfullOf_apply, QlinB_zero]
    exact tendsto_const_nhds
  · simp only [QfullOf_apply, Submodule.coe_smul]
    exact (tendsto_QlinB1_coe V hV G hreg A r.1).const_smul _

include hV hreg hk in
theorem tendsto_C2fullOf {X : ℝ → BondFnL2 L} {X₀ : BondFnL2 L} (hX : Tendsto X (𝓝 0) (𝓝 X₀)) :
    Tendsto (fun ε => C2fullOf G (V ε) (X ε)) (𝓝 0) (𝓝 (C2fullOf G (V 0) X₀)) := by
  refine tendsto_piLp_suTwo (fun p => ?_)
  obtain ⟨⟨j, hj⟩, r⟩ := p
  have hj1 : j = 0 ∨ j = 1 := by omega
  rcases hj1 with rfl | rfl
  · simp only [C2fullOf_apply, C2rawB_zero']
    exact tendsto_const_nhds
  · simp only [C2fullOf_apply, Submodule.coe_smul, C2rawB_one_coe]
    have h2 := continuousAt_fderiv2_qStep V hV (G.ell ^ 0) G.ell hreg r.1
    have hs : Tendsto (fun ε => suCoord (X ε)) (𝓝 0) (𝓝 (suCoord X₀)) :=
      ((suCoordL (L := L)).continuous.tendsto _).comp hX
    exact (((toM2L.continuous.tendsto _).comp
      (tendsto_clm_apply₂ (tendsto_clm_apply₂ h2 hs) hs)).const_smul _).const_smul _

end BondSector

theorem Ginv_dataS_eq (sD sJ : PlaqSel) (P : IngrBParams) :
    (dataS sD sJ P).Ginv = (pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G))
      + (ContinuousLinearMap.adjoint ((Tfull P.G P.U).comp (iE P.G))).comp
          ((Tfull P.G P.U).comp (iE P.G))
      + (pE P.G).comp ((MassFull P.G P.a (bondSectorOf P.G P.U)).comp (iE P.G)) := rfl

/-- The assembled data along a curvature family, typed on the fixed carrier of the tower. -/
noncomputable def dataFam (sD sJ : PlaqSel) {ell k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell : 0 < ell) (S : Tower (scaleUp ell k Lu)) (V : ℝ → Cfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) :
    ℝ → BaseDataS ↥(bondSupp (geomOf ell k S)) (SiteL2 (scaleUp ell k Lu)) (FSp (geomOf ell k S)) :=
  fun ε => dataS sD sJ (gparams ell k Lu hell S (V ε) a Lam)

theorem Ginv_dataFam_eq (sD sJ : PlaqSel) {ell k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell : 0 < ell) (S : Tower (scaleUp ell k Lu)) (V : ℝ → Cfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (ε : ℝ) :
    (dataFam sD sJ hell S V a Lam ε).Ginv =
      (pE (geomOf ell k S)).comp ((DpiFullS sD (geomOf ell k S) (V ε) a).comp (iE (geomOf ell k S)))
      + (ContinuousLinearMap.adjoint ((Tfull (geomOf ell k S) (V ε)).comp (iE (geomOf ell k S)))).comp
          ((Tfull (geomOf ell k S) (V ε)).comp (iE (geomOf ell k S)))
      + (pE (geomOf ell k S)).comp ((MassFull (geomOf ell k S) a
          (bondSectorOf (geomOf ell k S) (V ε))).comp (iE (geomOf ell k S))) := rfl

/-- Continuity of every assembled carrier at `ε = 0`, from continuity of `W`, `T` and `Q`. -/
theorem continuousAt_Ginv_dataS (sD sJ : PlaqSel) {ell k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell : 0 < ell) (S : Tower (scaleUp ell k Lu)) (V : ℝ → Cfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (hVc : ContFam V)
    (hW : ContinuousAt (fun ε => Wop (geomOf ell k S) (V ε) a) 0)
    (hT : ContinuousAt (fun ε => Tfull (geomOf ell k S) (V ε)) 0)
    (hQ : ContinuousAt (fun ε => QfullOf (geomOf ell k S) (V ε)) 0) :
    ContinuousAt (fun ε => (dataFam sD sJ hell S V a Lam ε).Ginv) 0 := by
  simp only [Ginv_dataFam_eq]
  have hΔ : ContinuousAt (fun ε => DeltaS sD (geomOf ell k S) (V ε)) 0 :=
    (AdalyFormal.D1Literal.cont_deltaKLocCLM hVc (sD _ (geomOf ell k S))).continuousAt
  have hDpi : ContinuousAt (fun ε => DpiFullS sD (geomOf ell k S) (V ε) a) 0 :=
    continuousAt_clm_comp (cont_adjoint.continuousAt.comp hW) (continuousAt_clm_comp hΔ hW)
  have hTi : ContinuousAt (fun ε => (Tfull (geomOf ell k S) (V ε)).comp (iE (geomOf ell k S))) 0 :=
    continuousAt_clm_comp hT continuousAt_const
  have hM : ContinuousAt (fun ε => MassFull (geomOf ell k S) a (bondSectorOf (geomOf ell k S) (V ε))) 0 :=
    continuousAt_clm_comp (cont_adjoint.continuousAt.comp hQ)
      (continuousAt_clm_comp continuousAt_const hQ)
  refine ((continuousAt_clm_comp continuousAt_const (continuousAt_clm_comp hDpi continuousAt_const)).add
    (continuousAt_clm_comp (cont_adjoint.continuousAt.comp hTi) hTi)).add ?_
  exact continuousAt_clm_comp continuousAt_const (continuousAt_clm_comp hM continuousAt_const)

/-- The constrained inverse `H = G Q* (Q G Q*)⁻¹` is continuous where both inverses are units. -/
theorem continuousAt_H {E S F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (D : ℝ → BaseDataS E S F) (hGinv : ContinuousAt (fun ε => (D ε).Ginv) 0)
    (hQ : ContinuousAt (fun ε => (D ε).Q) 0) (hQs : ContinuousAt (fun ε => (D ε).Qs) 0)
    (hu : IsUnit (D 0).Ginv) (hN : IsUnit (((D 0).Q.comp (D 0).G).comp (D 0).Qs)) :
    ContinuousAt (fun ε => (D ε).H) 0 := by
  have hG : ContinuousAt (fun ε => (D ε).G) 0 := continuousAt_inverse_comp hGinv hu
  have hNc : ContinuousAt (fun ε => ((D ε).Q.comp (D ε).G).comp (D ε).Qs) 0 :=
    continuousAt_clm_comp (continuousAt_clm_comp hQ hG) hQs
  exact continuousAt_clm_comp (continuousAt_clm_comp hG hQs) (continuousAt_inverse_comp hNc hN)

theorem inner_polarization {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : E →L[ℝ] E) (hM : ∀ x y, ⟪M x, y⟫ = ⟪x, M y⟫) (x y : E) :
    ⟪y, M x⟫ = (⟪x + y, M (x + y)⟫ - ⟪x - y, M (x - y)⟫) / 4 := by
  have h1 : ⟪x, M y⟫ = ⟪y, M x⟫ := by rw [← hM, real_inner_comm]
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, h1]
  ring

/-- The quadratic form of `Δ⁽²⁾(ε)/ε` converges to `2⟪H(0) C²(0) A, J'⟫`. -/
theorem tendsto_Delta2_div_form {E S F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (D : ℝ → BaseDataS E S F) (hL : ∀ ε, (D ε).Laws)
    (hH : ContinuousAt (fun ε => (D ε).H) 0)
    (hC2 : ∀ A, Tendsto (fun ε => (D ε).C2 A) (𝓝 0) (𝓝 ((D 0).C2 A)))
    (J' : E) (hJ : Tendsto (fun ε => ε⁻¹ • (D ε).J) (𝓝[≠] 0) (𝓝 J')) (A : E) :
    Tendsto (fun ε => ⟪A, (ε⁻¹ • (D ε).Delta2 (hL ε)) A⟫) (𝓝[≠] 0)
      (𝓝 (2 * ⟪(D 0).H ((D 0).C2 A), J'⟫)) := by
  have e : ∀ ε : ℝ, ⟪A, (ε⁻¹ • (D ε).Delta2 (hL ε)) A⟫
      = 2 * ⟪(D ε).H ((D ε).C2 A), ε⁻¹ • (D ε).J⟫ := by
    intro ε
    rw [smul_apply, real_inner_smul_right, ((D ε).Delta2_spec (hL ε)).2 A,
      real_inner_smul_right]
    ring
  simp only [e]
  have hHC : Tendsto (fun ε => (D ε).H ((D ε).C2 A)) (𝓝[≠] 0) (𝓝 ((D 0).H ((D 0).C2 A))) :=
    tendsto_clm_apply₂ (hH.tendsto.mono_left nhdsWithin_le_nhds)
      ((hC2 A).mono_left nhdsWithin_le_nhds)
  exact (Filter.Tendsto.inner (𝕜 := ℝ) hHC hJ).const_mul (2 : ℝ)

/-- **The first-order coefficient of the localized correction.**  If `H` is continuous at `0`, the
second jet `C²` converges pointwise, and the source has a curvature derivative `J'` (with
`J(0) = 0` built into the hypothesis), then `Δ⁽²⁾(ε)/ε` converges. -/
theorem tendsto_Delta2_div {E S F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (D : ℝ → BaseDataS E S F) (hL : ∀ ε, (D ε).Laws)
    (hH : ContinuousAt (fun ε => (D ε).H) 0)
    (hC2 : ∀ A, Tendsto (fun ε => (D ε).C2 A) (𝓝 0) (𝓝 ((D 0).C2 A)))
    (J' : E) (hJ : Tendsto (fun ε => ε⁻¹ • (D ε).J) (𝓝[≠] 0) (𝓝 J')) :
    ∃ D₁ : E →L[ℝ] E, Tendsto (fun ε => ε⁻¹ • (D ε).Delta2 (hL ε)) (𝓝[≠] 0) (𝓝 D₁) := by
  obtain ⟨β, hβ⟩ := (hL 0).C2_quad
  let β1 : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun x y => 2 * ⟪(D 0).H (β x y), J'⟫)
    (fun x1 x2 y => by simp only [map_add, LinearMap.add_apply, inner_add_left]; ring)
    (fun c x y => by simp only [map_smul, LinearMap.smul_apply, real_inner_smul_left, smul_eq_mul]; ring)
    (fun x y1 y2 => by simp only [map_add, inner_add_left]; ring)
    (fun c x y => by simp only [map_smul, real_inner_smul_left, smul_eq_mul]; ring)
  refine ⟨symmOp β1, ?_⟩
  have hdiag : ∀ A, Tendsto (fun ε => ⟪A, (ε⁻¹ • (D ε).Delta2 (hL ε)) A⟫) (𝓝[≠] 0)
      (𝓝 ⟪A, symmOp β1 A⟫) := by
    intro A
    rw [inner_symmOp_diag]
    have e2 : β1 A A = 2 * ⟪(D 0).H ((D 0).C2 A), J'⟫ := by
      simp only [β1, LinearMap.mk₂_apply, hβ A]
    rw [e2]
    exact tendsto_Delta2_div_form D hL hH hC2 J' hJ A
  have hsym : ∀ ε : ℝ, ∀ x y, ⟪(ε⁻¹ • (D ε).Delta2 (hL ε)) x, y⟫ = ⟪x, (ε⁻¹ • (D ε).Delta2 (hL ε)) y⟫ := by
    intro ε x y
    simp only [smul_apply, real_inner_smul_left, real_inner_smul_right,
      ((D ε).Delta2_spec (hL ε)).1 x y]
  apply tendsto_clm_of_inner
  intro x y
  have e1 : ∀ ε : ℝ, ⟪y, (ε⁻¹ • (D ε).Delta2 (hL ε)) x⟫ =
      (⟪x + y, (ε⁻¹ • (D ε).Delta2 (hL ε)) (x + y)⟫ - ⟪x - y, (ε⁻¹ • (D ε).Delta2 (hL ε)) (x - y)⟫) / 4 :=
    fun ε => inner_polarization _ (hsym ε) x y
  rw [inner_polarization (symmOp β1) (symmOp_symm β1) x y]
  simp only [e1]
  exact ((hdiag (x + y)).sub (hdiag (x - y))).div_const 4

/-- Any limit of `Δ⁽²⁾(ε)/ε` along `ε ↓ 0` has the quadratic form `A ↦ 2⟪H(0) C²(0) A, J'⟫`. -/
theorem limit_Delta2_div_form {E S F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (D : ℝ → BaseDataS E S F) (hL : ∀ ε, (D ε).Laws)
    (hH : ContinuousAt (fun ε => (D ε).H) 0)
    (hC2 : ∀ A, Tendsto (fun ε => (D ε).C2 A) (𝓝 0) (𝓝 ((D 0).C2 A)))
    (J' : E) (hJ : Tendsto (fun ε => ε⁻¹ • (D ε).J) (𝓝[≠] 0) (𝓝 J'))
    (D₁ : E →L[ℝ] E) (hD₁ : Tendsto (fun ε => ε⁻¹ • (D ε).Delta2 (hL ε)) (𝓝[>] 0) (𝓝 D₁)) (A : E) :
    ⟪A, D₁ A⟫ = 2 * ⟪(D 0).H ((D 0).C2 A), J'⟫ := by
  have h1 : Tendsto (fun ε => ⟪A, (ε⁻¹ • (D ε).Delta2 (hL ε)) A⟫) (𝓝[>] 0) (𝓝 ⟪A, D₁ A⟫) :=
    (Filter.Tendsto.inner (𝕜 := ℝ) tendsto_const_nhds (tendsto_clm_apply₂ hD₁ tendsto_const_nhds))
  have h2 := (tendsto_Delta2_div_form D hL hH hC2 J' hJ A).mono_left
    (nhdsWithin_mono _ (fun x (hx : (0 : ℝ) < x) => ne_of_gt hx))
  exact tendsto_nhds_unique h1 h2

end Assembly

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## H. The curvature derivative of the localized source

The localized source `J = D* Im ∂U` (`ZLocJ.JSU2Loc`) is a finite expression in link matrices,
plaquette holonomies, the trace and conjugate transposes; along a family with smooth links it is
smooth, it vanishes at the flat point (`JSU2Loc_trivial`), so `J(ε)/ε` converges. -/
section SourceSmooth

open scoped Matrix Matrix.Norms.Frobenius
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2 (SG SG.mul SG.inv conjTR conjTR_apply)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.DeltaPrime (holonomyElem holonomyElemInv imHolonomy)
open AdalyFormal.Balaban.SourceJ (piProj DstarDir)
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwo conjByAmbient)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)
open AdalyFormal.IngredientFamily (JSU2Loc JfieldLoc FnuMuLoc)

variable {L : PeriodicLatticeExtent} (V : ℝ → PeriodicLinkConfiguration SU2 L) (hV : SmoothAt0 V)
include hV

theorem SG_holonomyElem (p : PeriodicLatticePlaquette L) :
    SG (fun ε => holonomyElem (V ε) p) := by
  have hS : ∀ b, SG (fun ε => V ε b) := hV
  have e : (fun ε => holonomyElem (V ε) p) = fun ε =>
      V ε (p.1, p.2.1.1) * V ε (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) *
        (V ε (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹ * (V ε (p.1, p.2.1.2))⁻¹ := by
    funext ε; rfl
  rw [e]
  exact (((hS _).mul (hS _)).mul (hS _).inv).mul (hS _).inv

theorem cd_imHolonomy (p : PeriodicLatticePlaquette L) :
    ContDiffAt ℝ ⊤ (fun ε => imHolonomy (V ε) p) 0 := by
  have h1 : ContDiffAt ℝ ⊤ (fun ε => ((holonomyElem (V ε) p : SU2) : M2)) 0 := SG_holonomyElem V hV p
  have h2 : ContDiffAt ℝ ⊤ (fun ε => ((holonomyElemInv (V ε) p : SU2) : M2)) 0 :=
    (SG_holonomyElem V hV p).inv
  exact (h1.sub h2).const_smul _

omit hV in
theorem cd_piProj {f : ℝ → M2} (hf : ContDiffAt ℝ ⊤ f 0) :
    ContDiffAt ℝ ⊤ (fun ε => piProj (f ε)) 0 := by
  have htr : ContDiffAt ℝ ⊤ (fun ε => Matrix.trace (f ε)) 0 :=
    (((Matrix.traceLinearMap (Fin 2) ℝ ℂ).toContinuousLinearMap).contDiff.contDiffAt).comp 0 hf
  simp only [piProj]
  exact hf.sub ((htr.div_const 2).smul contDiffAt_const)

theorem cd_FnuMuLoc (P : Set (PeriodicLatticePlaquette L)) (ν μ : Fin 3) (y : PeriodicLatticeSite L) :
    ContDiffAt ℝ ⊤ (fun ε => FnuMuLoc P (V ε) ν μ y) 0 := by
  classical
  unfold FnuMuLoc
  by_cases hlt : ν < μ
  · simp only [dif_pos hlt]
    by_cases hp : (y, (⟨(ν, μ), hlt⟩ : PeriodicPlaquetteDirections)) ∈ P
    · simp only [if_pos hp]
      exact cd_piProj (cd_imHolonomy V hV _)
    · simp only [if_neg hp]
      exact contDiffAt_const
  · simp only [dif_neg hlt]
    by_cases hgt : μ < ν
    · simp only [dif_pos hgt]
      by_cases hp : (y, (⟨(μ, ν), hgt⟩ : PeriodicPlaquetteDirections)) ∈ P
      · simp only [if_pos hp]
        exact (cd_piProj (cd_imHolonomy V hV _)).neg
      · simp only [if_neg hp]
        exact contDiffAt_const
    · simp only [dif_neg hgt]
      exact contDiffAt_const

theorem cd_DstarDir (ν : Fin 3) {Gf : ℝ → PeriodicLatticeSite L → M2}
    (hG : ∀ y, ContDiffAt ℝ ⊤ (fun ε => Gf ε y) 0) (x : PeriodicLatticeSite L) :
    ContDiffAt ℝ ⊤ (fun ε => DstarDir (V ε) ν (Gf ε) x) 0 := by
  have hS : ∀ b, SG (fun ε => V ε b) := hV
  have hg : ContDiffAt ℝ ⊤ (fun ε => (((V ε (periodicLatticeShiftBack x ν, ν))⁻¹ : SU2) : M2)) 0 :=
    (hS _).inv
  have hgH : ContDiffAt ℝ ⊤ (fun ε => ((((V ε (periodicLatticeShiftBack x ν, ν))⁻¹ : SU2) : M2))ᴴ) 0 :=
    conjTR.contDiff.contDiffAt.comp 0 hg
  have e : (fun ε => DstarDir (V ε) ν (Gf ε) x) = fun ε =>
      (((V ε (periodicLatticeShiftBack x ν, ν))⁻¹ : SU2) : M2) * Gf ε (periodicLatticeShiftBack x ν) *
        ((((V ε (periodicLatticeShiftBack x ν, ν))⁻¹ : SU2) : M2))ᴴ - Gf ε x := by
    funext ε; rfl
  rw [e]
  exact ((hg.mul (hG _)).mul hgH).sub (hG x)

theorem cd_JfieldLoc (P : Set (PeriodicLatticePlaquette L)) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ContDiffAt ℝ ⊤ (fun ε => JfieldLoc P (V ε) x μ) 0 := by
  classical
  unfold JfieldLoc
  refine ContDiffAt.sum (fun ν _ => ?_)
  by_cases h : ν = μ
  · simp only [if_pos h]
    exact contDiffAt_const
  · simp only [if_neg h]
    exact cd_DstarDir V hV ν (fun y => cd_FnuMuLoc V hV P ν μ y) x

theorem cd_JSU2Loc (P : Set (PeriodicLatticePlaquette L)) (b : PeriodicLatticeEdge L) :
    ContDiffAt ℝ ⊤ (fun ε => ((JSU2Loc 1 P (V ε) b : SuTwo) : M2)) 0 := by
  have e : (fun ε => ((JSU2Loc 1 P (V ε) b : SuTwo) : M2)) = fun ε =>
      ((-Complex.I) * (((1 : ℝ)⁻¹ ^ 3 : ℝ) : ℂ)) • JfieldLoc P (V ε) b.1 b.2 := by
    funext ε; rfl
  rw [e]
  exact (cd_JfieldLoc V hV P b.1 b.2).const_smul _

/-- The slope of one source component at the flat point. -/
theorem source_slope (P : Set (PeriodicLatticePlaquette L)) (b : PeriodicLatticeEdge L)
    (h0 : ((JSU2Loc 1 P (V 0) b : SuTwo) : M2) = 0) :
    ∃ d : M2, d ∈ suTwo ∧
      Tendsto (fun t : ℝ => t⁻¹ • ((JSU2Loc 1 P (V t) b : SuTwo) : M2)) (𝓝[≠] 0) (𝓝 d) := by
  have hc := cd_JSU2Loc V hV P b
  have hd := (hc.differentiableAt (by simp)).hasDerivAt
  have ht := hd.tendsto_slope_zero
  simp only [zero_add, h0, sub_zero] at ht
  refine ⟨_, ?_, ht⟩
  have hcl : IsClosed (suTwo : Set M2) := Submodule.closed_of_finiteDimensional _
  refine hcl.mem_of_tendsto ht (Filter.Eventually.of_forall (fun t => ?_))
  exact suTwo.smul_mem _ (JSU2Loc 1 P (V t) b).2

end SourceSmooth

section Source

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwo BondFnL2)
open AdalyFormal.IngredientFamily (JSU2Loc)

variable {L : PeriodicLatticeExtent}

/-- `J(ε)/ε` converges along a smooth family whose flat point is the trivial background. -/
theorem exists_source_derivative (V : ℝ → PeriodicLinkConfiguration SU2 L) (hV : SmoothAt0 V)
    (hV0 : V 0 = fun _ => 1) (P : Set (PeriodicLatticePlaquette L)) :
    ∃ J' : BondFnL2 L, Tendsto (fun ε : ℝ =>
      ε⁻¹ • (WithLp.toLp 2 (fun b => -(JSU2Loc 1 P (V ε) b)) : BondFnL2 L)) (𝓝[≠] 0) (𝓝 J') := by
  have h0 : ∀ b, ((JSU2Loc 1 P (V 0) b : SuTwo) : M2) = 0 := by
    intro b
    rw [hV0]
    have := AdalyFormal.IngredientFamily.JSU2Loc_trivial (L := L) 1 P b
    exact congrArg Subtype.val this
  choose d hd hlim using fun b => source_slope V hV P b (h0 b)
  refine ⟨WithLp.toLp 2 (fun b => -(⟨d b, hd b⟩ : SuTwo)), tendsto_piLp_suTwo (fun b => ?_)⟩
  have e : ∀ t : ℝ, ((WithLp.ofLp (t⁻¹ • (WithLp.toLp 2 (fun b => -(JSU2Loc 1 P (V t) b)) :
      BondFnL2 L)) b : SuTwo) : M2) = -(t⁻¹ • ((JSU2Loc 1 P (V t) b : SuTwo) : M2)) := by
    intro t
    simp only [PiLp.smul_apply, Submodule.coe_smul, Submodule.coe_neg, smul_neg]
  simp only [e]
  show Tendsto _ _ (𝓝 (-(d b)))
  exact (hlim b).neg

end Source

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## I. The curved dilated family at the flat point: smoothness and the units

`ε ↦ dilU q R ε 1` (curvature `ε` on the round-4 defect line, trivial exterior) has smooth
links and is the trivial background at `ε = 0`.  At the trivial background the Dirichlet
operator, the constraint Gram `Γ` (frozen `MS6.exists_Gami_strat` with `ρ = 0` on the proper
tower of an admissible tower, `MS7.properTower_geomOf`) and `Q*` (frozen `W6F.qs_injective_strat`
with zero drift) are units resp. injective. -/
section DilFamily

open scoped Matrix.Norms.Frobenius
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2 (Ug Xm sig Ug_zero)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilPattern dilU)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

theorem contDiff_Xm : ContDiff ℝ ⊤ (fun t : ℝ => Xm t) := by
  have e : (fun t : ℝ => Xm t) = fun t => t • (Complex.I • sig) := by
    funext t
    ext i j
    simp [Xm, Matrix.smul_apply, Complex.real_smul, mul_assoc]
  rw [e]
  exact contDiff_id.smul contDiff_const

theorem contDiffAt_Ug (t₀ : ℝ) : ContDiffAt ℝ ⊤ (fun t : ℝ => ((Ug t : SU2) : M2)) t₀ :=
  (NormedSpace.exp_analytic (Xm t₀)).contDiffAt.comp t₀ contDiff_Xm.contDiffAt

theorem dilU_link_contDiff (q R : ℕ) (e : Bond (scaleUp 2 1 (dilLu q R))) :
    ContDiff ℝ ⊤ (fun ε : ℝ => ((dilU q R ε 1 e : SU2) : M2)) := by
  classical
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [dilU, if_pos he]
    exact contDiff_const
  · simp only [dilU, if_neg he]
    by_cases hp : dilPattern q R e
    · simp only [if_pos hp]
      exact contDiff_iff_contDiffAt.mpr contDiffAt_Ug
    · simp only [if_neg hp]
      exact contDiff_const

theorem dilU_smooth (q R : ℕ) : SmoothAt0 (fun ε : ℝ => dilU q R ε 1) :=
  fun e => (dilU_link_contDiff q R e).contDiffAt

theorem dilU_contFam (q R : ℕ) : AdalyFormal.D1Literal.ContFam (fun ε : ℝ => dilU q R ε 1) :=
  fun e => (dilU_link_contDiff q R e).continuous

end DilFamily

section DilUnits

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLane2 (Ug Ug_zero)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilPattern dilU)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

theorem dilU_zero (q R : ℕ) : dilU q R 0 1 = fun _ => 1 := by
  classical
  funext e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [dilU, if_pos he]
    rfl
  · simp only [dilU, if_neg he, ite_self, Ug_zero]

theorem dil_G_k (q R : ℕ) : (geomOf 2 1 (dilTower q R)).k = 1 := rfl
theorem dil_G_ell (q R : ℕ) : (geomOf 2 1 (dilTower q R)).ell = 2 := rfl

theorem dil_out_site (q R : ℕ) (hq : 0 < q) :
    ∃ x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)), x ∉ (geomOf 2 1 (dilTower q R)).Om0 := by
  refine ⟨fun _ => 0, ?_⟩
  show ¬ (4 * q ≤ ((0 : Fin _) : ℕ) ∧ _)
  simp only [Fin.val_zero]
  omega

theorem dil_LP_unit (q R : ℕ) (hq : 0 < q) (U : Cfg (scaleUp 2 1 (dilLu q R))) :
    IsUnit (AdalyFormal.M1Site.LP (geomOf 2 1 (dilTower q R)) U 1) :=
  delpA_unit (geomOf 2 1 (dilTower q R)) U one_pos (le_refl 2) (dil_out_site q R hq)

theorem dil_wq_pos (q R : ℕ) (j : ℕ) : 0 < AdalyFormal.M1Site.wq (geomOf 2 1 (dilTower q R)) 1 j :=
  wq_pos (geomOf 2 1 (dilTower q R)) one_pos (le_refl 2) j

theorem bgTower_one {L : PeriodicLatticeExtent} (G : TowerGeom L) (i : ℕ) :
    bgTower G (fun _ => 1) i = fun _ => 1 :=
  AdalyFormal.SliceCoerc.ubarTower_trivial G.ell i

theorem dil_Gam_unit {q R : ℕ} (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    IsUnit (Gam (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1) := by
  obtain ⟨Gi, h1, h2⟩ := AdalyFormal.M1Site.exists_Gami_strat 2 1 (le_refl 2)
    (AdalyFormal.M1Site.hdvd_of_admissible hS) (AdalyFormal.M1Site.properTower_geomOf (by norm_num) hS)
    (fun _ => 1) 1 one_pos 0 le_rfl (by norm_num)
    (fun j _ y _ b _ => by simp)
    (fun j _ y _ i _ z _ _ μ _ => by rw [bgTower_one]; simp)
  refine ⟨⟨Gam (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1, Gi, ?_, ?_⟩, rfl⟩
  · ext1 u; exact h1 u
  · ext1 u; exact h2 u

theorem delW_zero (ell k : ℕ) (hell : 0 < ell) : AdalyFormal.W6.delW ell k (fun _ => 0) = 0 := by
  unfold AdalyFormal.W6.delW AdalyFormal.W6.SS
  simp [AdalyFormal.BondComposite.thetaOf_zero ell hell]

theorem dil_Qs_inj {q R : ℕ} (hq : 0 < q) (hR16 : 16 ≤ R) (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    Function.Injective (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (trivialU (scaleUp 2 1 (dilLu q R))) 1 (dilLam q R)).data.Qs :=
  AdalyFormal.W6.qs_injective_strat (by norm_num) (le_refl 2) hS (by omega) (by omega)
    (trivialU _) 1 (dilLam q R) (fun _ => 0) (AdalyFormal.W6.regTower_triv (by norm_num))
    (AdalyFormal.W6.towerClass_triv (by norm_num)) (fun _ _ => le_rfl)
    (fun _ _ => AdalyFormal.W6.rhoOf_zero_lt 2) (by rw [delW_zero 2 1 (by norm_num)]; norm_num)

end DilUnits

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## J. The flat localized carrier of the dilated tower is positive definite

At the trivial background `⟪x, B x⟫ = ‖χ curl x‖² + ‖T x‖² + Σ a ℓʲ ‖Q x‖²` (`B` the localized
carrier).  If it vanishes, `x` is curl-free on the plaquettes of `Ω₀`, vanishes on every bond not
touching `Ω₁` (level-0 rows of `Q`), and has vanishing level-1 rows.  Integrating `x` along the
longitudinal lines from the left boundary gives a site field `ξ` with `x = D ξ` on the bonds
before the right edge; the level-1 rows telescope along the longitudinal chain of blocks from the
left collar (where `ξ = 0`) to the right collar (where `ξ` is a transverse constant), so the
constant is `0`, `ξ ∈ N(Q')` and `x = D ξ` everywhere; then `T (D ξ) = 0` forces `D ξ = 0`
(the frozen `final_step` argument, copied). -/
section FlatKernel

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dil_fine_size)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_one curlValueCovariant
  gradValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf stepAverage)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open Fin.NatCast

/-! ### Frozen `NsPtD2.final_step` (outside the `DrEquiv` closure), copied verbatim. -/

theorem siteMask_eq_self_of_supp' {L : PeriodicLatticeExtent} (S : Set (PeriodicLatticeSite L))
    (ξ : SiteL2 L) (h : ∀ x, x ∉ S → ξ x = 0) : siteMask S ξ = ξ := by
  classical
  ext x
  rw [siteMask_apply]
  by_cases hx : x ∈ S
  · rw [if_pos hx]
  · rw [if_neg hx, h x hx]

theorem lapDir_eq_mask_lap' {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (ξ : SiteL2 L)
    (h : ∀ x, x ∉ G.Om0 → ξ x = 0) : lapDir G U ξ = siteMask G.Om0 (lapFull U ξ) := by
  unfold lapDir
  simp only [ContinuousLinearMap.comp_apply]
  rw [siteMask_eq_self_of_supp' _ _ h]

theorem final_step' {L : PeriodicLatticeExtent} (G : TowerGeom L) (ξ : SiteL2 L)
    (hξ : ξ ∈ NQp G (flatCfg : Cfg L))
    (hT : Tfull G (flatCfg : Cfg L) (gradL2 (flatCfg : Cfg L) ξ) = 0) :
    gradL2 (flatCfg : Cfg L) ξ = 0 := by
  have hsupp := hξ.1
  have hlap := lapDir_eq_mask_lap' G flatCfg ξ hsupp
  have hmem : lapDir G (flatCfg : Cfg L) ξ ∈ RImage G (flatCfg : Cfg L) :=
    Submodule.mem_map.mpr ⟨ξ, hξ, rfl⟩
  have hR : Rproj G (flatCfg : Cfg L) (lapFull (flatCfg : Cfg L) ξ) = 0 := by
    have : Tfull G (flatCfg : Cfg L) (gradL2 (flatCfg : Cfg L) ξ) =
        Rproj G (flatCfg : Cfg L) (lapFull (flatCfg : Cfg L) ξ) := rfl
    rw [← this]; exact hT
  have horth : lapFull (flatCfg : Cfg L) ξ ∈ (RImage G (flatCfg : Cfg L))ᗮ := by
    have := hR
    unfold Rproj at this
    exact (Submodule.starProjection_apply_eq_zero_iff _).mp this
  have h1 : ⟪lapDir G (flatCfg : Cfg L) ξ, lapFull (flatCfg : Cfg L) ξ⟫ = 0 :=
    (Submodule.mem_orthogonal _ _).mp horth _ hmem
  have h2 : ⟪lapDir G (flatCfg : Cfg L) ξ, lapFull (flatCfg : Cfg L) ξ⟫ =
      ‖lapDir G (flatCfg : Cfg L) ξ‖ ^ 2 := by
    have e : ⟪siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ), lapFull (flatCfg : Cfg L) ξ⟫
        = ⟪siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ),
            siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ)⟫ := by
      calc ⟪siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ), lapFull (flatCfg : Cfg L) ξ⟫
          = ⟪siteMask G.Om0 (siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ)),
              lapFull (flatCfg : Cfg L) ξ⟫ := by rw [siteMask_idem]
        _ = _ := siteMask_symm _ _ _
    rw [hlap, e, real_inner_self_eq_norm_sq]
  have h3 : lapDir G (flatCfg : Cfg L) ξ = 0 := by
    rw [h2] at h1
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)
  have h4 : ⟪ξ, lapFull (flatCfg : Cfg L) ξ⟫ = 0 := by
    have : ⟪ξ, lapFull (flatCfg : Cfg L) ξ⟫ = ⟪siteMask G.Om0 ξ, lapFull (flatCfg : Cfg L) ξ⟫ := by
      rw [siteMask_eq_self_of_supp' _ _ hsupp]
    rw [this, siteMask_symm, ← hlap, h3, inner_zero_right]
  have h5 : ⟪ξ, lapFull (flatCfg : Cfg L) ξ⟫ = ‖gradL2 (flatCfg : Cfg L) ξ‖ ^ 2 := by
    simp only [lapFull, ContinuousLinearMap.comp_apply, gradAdj, ContinuousLinearMap.adjoint_inner_right]
    rw [real_inner_self_eq_norm_sq]
  rw [h5] at h4
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h4)

/-! ### Coordinates of the dilated tower -/

variable {q R : ℕ}

theorem dsize0 (hq : 0 < q) : scaleUp 2 1 (dilLu q R) 0 + 1 = 12 * (R * q) + 16 * q := by
  have h := dil_fine_size hq R 0
  simpa using h

theorem dsizeT (hq : 0 < q) {μ : Fin 3} (hμ : μ ≠ 0) : scaleUp 2 1 (dilLu q R) μ + 1 = 8 * q := by
  rw [dil_fine_size hq R μ, if_neg hμ]

theorem x0_lt (hq : 0 < q) (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    (x 0).val < 12 * (R * q) + 16 * q := by
  have h1 := (x 0).isLt
  have h2 := dsize0 (R := R) hq
  omega

theorem xT_lt (hq : 0 < q) (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0) :
    (x μ).val < 8 * q := by
  have h1 := (x μ).isLt
  have h2 := dsizeT (R := R) hq hμ
  omega

theorem mem_Om0 (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    x ∈ (dilTower q R).Om 0 ↔ 4 * q ≤ (x 0).val ∧ (x 0).val < 12 * (R * q) + 12 * q := Iff.rfl

theorem mem_Om1 (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    x ∈ (dilTower q R).Om 1 ↔
      2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q := Iff.rfl

theorem not_mem_Om2 (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    x ∉ (dilTower q R).Om 2 := by
  simp [dilTower]

theorem shift_coord_ne {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) {μ ν : Fin 3}
    (h : ν ≠ μ) : (periodicLatticeShift x μ) ν = x ν := by
  unfold periodicLatticeShift
  rw [Function.update_of_ne h]

theorem shift_self_coord {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) (μ : Fin 3) :
    (periodicLatticeShift x μ) μ = x μ + 1 := by
  unfold periodicLatticeShift
  rw [Function.update_self]

theorem shift0_val_lt {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L)
    (h : (x 0).val + 1 < L 0 + 1) : ((periodicLatticeShift x 0) 0).val = (x 0).val + 1 := by
  rw [shift_self_coord, Fin.val_add_one, if_neg]
  intro hc
  rw [hc, Fin.val_last] at h
  omega

theorem shift0_val_last {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L)
    (h : (x 0).val + 1 = L 0 + 1) : ((periodicLatticeShift x 0) 0).val = 0 := by
  rw [shift_self_coord, Fin.val_add_one, if_pos]
  ext
  rw [Fin.val_last]
  omega

/-! ### The kernel argument -/

section Kernel
variable (hq : 0 < q) (hR : 1 ≤ R) (A : BondFnL2 (scaleUp 2 1 (dilLu q R)))
  (hsupp : ∀ b, b ∉ bondsOm0 (geomOf 2 1 (dilTower q R)) → A b = 0)
  (hQ : QfullOf (geomOf 2 1 (dilTower q R)) flatCfg A = 0)

theorem OmGe1_mem {x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))}
    (h : OmGe (geomOf 2 1 (dilTower q R)) 1 x) : x ∈ (dilTower q R).Om 1 := by
  obtain ⟨i, hi1, hik, y, hy, hxy⟩ := h
  have hi : i = 1 := by
    have : i ≤ 1 := hik
    omega
  subst hi
  obtain ⟨hdiv, hyOm, -⟩ := hy
  rw [mem_Om1] at hyOm ⊢
  have h0 := hxy 0
  have hd := hdiv 0
  have hell : (geomOf 2 1 (dilTower q R)).ell = 2 := rfl
  simp only [pow_one, hell] at hd h0
  have hb : 2 ∣ 10 * (R * q) + 12 * q := ⟨5 * (R * q) + 6 * q, by ring⟩
  omega

include hsupp hQ in
theorem A_zero_off {b : Bond (scaleUp 2 1 (dilLu q R))} (h1 : b.1 ∉ (dilTower q R).Om 1)
    (h2 : periodicLatticeShift b.1 b.2 ∉ (dilTower q R).Om 1) : A b = 0 := by
  by_cases hb : b ∈ bondsOm0 (geomOf 2 1 (dilTower q R))
  · have hL : b ∈ bondsLam (geomOf 2 1 (dilTower q R)) 0 := by
      refine ⟨?_, ?_⟩
      · rcases hb with hb | hb
        · exact Or.inl ⟨fun μ => by simp, hb, h1⟩
        · exact Or.inr ⟨fun μ => by simp, hb, h2⟩
      · rintro (h | h)
        · exact h1 (OmGe1_mem h)
        · exact h2 (OmGe1_mem h)
    have h := congrArg (fun v : FSp (geomOf 2 1 (dilTower q R)) => WithLp.ofLp v ⟨0, ⟨b, hL⟩⟩) hQ
    have h' : WithLp.ofLp (QfullOf (geomOf 2 1 (dilTower q R)) flatCfg A) ⟨0, ⟨b, hL⟩⟩ = A b := by
      rw [QfullOf_apply]
      show (((geomOf 2 1 (dilTower q R)).ell : ℝ) ^ 0)⁻¹ •
        (WithLp.ofLp (QlinB (geomOf 2 1 (dilTower q R)) flatCfg 0 A)) b = A b
      rw [QlinB_zero, pow_zero, inv_one, one_smul]
    simp only at h
    rw [h'] at h
    exact h
  · exact hsupp b hb

/-- the site with longitudinal coordinate replaced by `u`. -/
def sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) :
    PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) :=
  Function.update z 0 ((u : ℕ) : Fin (scaleUp 2 1 (dilLu q R) 0 + 1))

omit hq A in
theorem sitex_val (hq : 0 < q) (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {u : ℕ}
    (hu : u < 12 * (R * q) + 16 * q) : ((sitex z u) 0).val = u := by
  unfold sitex
  rw [Function.update_self, Fin.val_natCast, dsize0 hq]
  exact Nat.mod_eq_of_lt hu

omit A in
theorem sitex_coord (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) {ν : Fin 3}
    (hν : ν ≠ 0) : (sitex z u) ν = z ν := by
  unfold sitex
  rw [Function.update_of_ne hν]

omit A in
theorem sitex_self (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : sitex z (z 0).val = z := by
  unfold sitex
  rw [Fin.cast_val_eq_self, Function.update_eq_self]

omit A in
theorem sitex_sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u v : ℕ) :
    sitex (sitex z v) u = sitex z u := by
  unfold sitex
  rw [Function.update_idem]

omit A in
theorem shift_sitex0 (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) :
    periodicLatticeShift (sitex z u) 0 = sitex z (u + 1) := by
  unfold periodicLatticeShift sitex
  rw [Function.update_idem, Function.update_self, Nat.cast_succ]

omit A in
theorem shift_sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) {μ : Fin 3}
    (hμ : μ ≠ 0) : periodicLatticeShift (sitex z u) μ = sitex (periodicLatticeShift z μ) u := by
  unfold periodicLatticeShift sitex
  rw [Function.update_of_ne hμ, Function.update_comm (Ne.symm hμ)]

omit A in
theorem sitex_of_shift0 (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) :
    sitex (periodicLatticeShift z 0) u = sitex z u := by
  unfold periodicLatticeShift sitex
  rw [Function.update_idem]

/-- the longitudinal potential. -/
noncomputable def xi (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : SuTwo :=
  ∑ u ∈ Finset.range (z 0).val, A (sitex z u, 0)

include hq in
/-- longitudinal step. -/
theorem xi_shift0 (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (h : (z 0).val + 1 < 12 * (R * q) + 16 * q) :
    xi A (periodicLatticeShift z 0) = xi A z + A (z, 0) := by
  unfold xi
  have hz : ((periodicLatticeShift z 0) 0).val = (z 0).val + 1 :=
    shift0_val_lt z (by have h2 := dsize0 (R := R) hq; omega)
  rw [hz, Finset.sum_range_succ]
  simp only [sitex_of_shift0]
  rw [sitex_self]

include hq hR hsupp hQ in
/-- the plaquette identity in the `(0, μ)` plane, from curl-freeness or vanishing of all bonds. -/
theorem trans_step
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (w : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0)
    (hw : (w 0).val + 1 < 12 * (R * q) + 16 * q) :
    A (periodicLatticeShift w μ, 0) - A (w, 0) = A (periodicLatticeShift w 0, μ) - A (w, μ) := by
  classical
  have h0μ : (0 : Fin 3) < μ := by
    rcases Fin.pos_iff_ne_zero.mpr hμ with h
    exact h
  have hw0 : ((periodicLatticeShift w 0) 0).val = (w 0).val + 1 :=
    shift0_val_lt w (by have h2 := dsize0 (R := R) hq; omega)
  have hwμ : (periodicLatticeShift w μ) 0 = w 0 := shift_coord_ne w (Ne.symm hμ)
  have hw0μ : ((periodicLatticeShift (periodicLatticeShift w 0) μ) 0).val = (w 0).val + 1 := by
    rw [shift_coord_ne _ (Ne.symm hμ), hw0]
  have hwμ0 : ((periodicLatticeShift (periodicLatticeShift w μ) 0) 0).val = (w 0).val + 1 := by
    rw [shift0_val_lt _ (by have h2 := dsize0 (R := R) hq; rw [hwμ]; omega), hwμ]
  by_cases hin : 4 * q ≤ (w 0).val ∧ (w 0).val + 1 < 12 * (R * q) + 12 * q
  · let p : PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)) := (w, ⟨(0, μ), h0μ⟩)
    have hp : p ∈ plaqIn ((dilTower q R).Om 0) := by
      intro e he
      simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton, p] at he
      rcases he with rfl | rfl | rfl | rfl
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
    have hc := hcurl p hp
    simp only [curlValueCovariant, p, flatCfg, RMap_one, LinearMap.id_apply] at hc
    have e : A (periodicLatticeShift w μ, 0) - A (w, 0) - (A (periodicLatticeShift w 0, μ) - A (w, μ)) = 0 := by
      rw [← neg_eq_zero, ← hc]; abel
    exact sub_eq_zero.mp e
  · have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
    have hR1 : ∀ x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)),
        ((x 0).val = (w 0).val ∨ (x 0).val = (w 0).val + 1) → x ∉ (dilTower q R).Om 1 := by
      intro x hx hxm
      rw [mem_Om1] at hxm
      rcases hx with hx | hx <;> rw [hx] at hxm <;>
        (by_cases h4 : 4 * q ≤ (w 0).val
         · have h5 : ¬ ((w 0).val + 1 < 12 * (R * q) + 12 * q) := fun h => hin ⟨h4, h⟩
           omega
         · omega)
    have z1 := A_zero_off A hsupp hQ (b := (w, 0)) (hR1 w (Or.inl rfl)) (hR1 _ (Or.inr hw0))
    have z2 := A_zero_off A hsupp hQ (b := (periodicLatticeShift w 0, μ)) (hR1 _ (Or.inr hw0))
      (hR1 _ (Or.inr hw0μ))
    have z3 := A_zero_off A hsupp hQ (b := (periodicLatticeShift w μ, 0))
      (hR1 (periodicLatticeShift w μ) (Or.inl (by rw [hwμ]))) (hR1 _ (Or.inr hwμ0))
    have z4 := A_zero_off A hsupp hQ (b := (w, μ)) (hR1 w (Or.inl rfl))
      (hR1 (periodicLatticeShift w μ) (Or.inl (by rw [hwμ])))
    rw [z1, z2, z3, z4]

include hq hR hsupp hQ in
/-- transverse step. -/
theorem xi_shiftT
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0) :
    xi A (periodicLatticeShift z μ) = xi A z + (A (z, μ) - A (sitex z 0, μ)) := by
  unfold xi
  rw [shift_coord_ne z (Ne.symm hμ)]
  have hz := x0_lt hq z
  have e : ∀ u ∈ Finset.range (z 0).val, A (sitex (periodicLatticeShift z μ) u, 0)
      = A (sitex z u, 0) + (A (sitex z (u + 1), μ) - A (sitex z u, μ)) := by
    intro u hu
    rw [Finset.mem_range] at hu
    have hval : ((sitex z u) 0).val = u := sitex_val hq z (by omega)
    have ht := trans_step hq hR A hsupp hQ hcurl (sitex z u) hμ (by rw [hval]; omega)
    rw [shift_sitex z u hμ, shift_sitex0] at ht
    rw [← sub_eq_iff_eq_add', ht]
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_range_sub (fun u => A (sitex z u, μ)),
    sitex_self]

include hq hsupp hQ in
theorem xi_left (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (h : (z 0).val < 2 * (R * q) + 4 * q) : xi A z = 0 := by
  unfold xi
  refine Finset.sum_eq_zero (fun u hu => ?_)
  rw [Finset.mem_range] at hu
  have hz := x0_lt hq z
  have hv : ((sitex z u) 0).val = u := sitex_val hq z (by omega)
  refine A_zero_off A hsupp hQ ?_ ?_
  · rw [mem_Om1, hv]; omega
  · rw [mem_Om1, shift_sitex0, sitex_val hq z (by omega)]; omega

include hq hsupp hQ in
/-- beyond the right edge of `Ω₁` the potential equals its value at the right edge. -/
theorem xi_right (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (h : 10 * (R * q) + 12 * q ≤ (z 0).val) :
    xi A z = xi A (sitex z (10 * (R * q) + 12 * q)) := by
  have hz := x0_lt hq z
  have key : ∀ n, 10 * (R * q) + 12 * q + n < 12 * (R * q) + 16 * q →
      xi A (sitex z (10 * (R * q) + 12 * q + n)) = xi A (sitex z (10 * (R * q) + 12 * q)) := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      have hv : ((sitex z (10 * (R * q) + 12 * q + n)) 0).val = 10 * (R * q) + 12 * q + n :=
        sitex_val hq z (by omega)
      rw [← ih (by omega)]
      have e := xi_shift0 hq A (sitex z (10 * (R * q) + 12 * q + n)) (by rw [hv]; omega)
      rw [shift_sitex0] at e
      rw [show 10 * (R * q) + 12 * q + (n + 1) = 10 * (R * q) + 12 * q + n + 1 by ring, e]
      have h0 : A (sitex z (10 * (R * q) + 12 * q + n), 0) = 0 := by
        refine A_zero_off A hsupp hQ ?_ ?_
        · show sitex z _ ∉ _
          rw [mem_Om1, hv]; omega
        · show periodicLatticeShift (sitex z _) 0 ∉ _
          rw [mem_Om1, shift_sitex0, sitex_val hq z (by omega)]; omega
      rw [h0, add_zero]
  have hk := key ((z 0).val - (10 * (R * q) + 12 * q)) (by omega)
  rw [Nat.add_sub_cancel' h, sitex_self] at hk
  exact hk

/-- the right-edge value of the potential, a function of the transverse coordinates. -/
noncomputable def Iv (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : SuTwo :=
  xi A (sitex z (10 * (R * q) + 12 * q))

include hq hR hsupp hQ in
theorem Iv_shiftT
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0) :
    Iv A (periodicLatticeShift z μ) = Iv A z := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  unfold Iv
  rw [← shift_sitex z _ hμ, xi_shiftT hq hR A hsupp hQ hcurl _ hμ]
  have hv : ((sitex z (10 * (R * q) + 12 * q)) 0).val = 10 * (R * q) + 12 * q :=
    sitex_val hq z (by omega)
  have e1 : A (sitex z (10 * (R * q) + 12 * q), μ) = 0 := by
    refine A_zero_off A hsupp hQ ?_ ?_
    · show sitex z _ ∉ _
      rw [mem_Om1, hv]; omega
    · show periodicLatticeShift (sitex z _) μ ∉ _
      rw [mem_Om1, shift_coord_ne _ (Ne.symm hμ), hv]; omega
  have e2 : A (sitex (sitex z (10 * (R * q) + 12 * q)) 0, μ) = 0 := by
    rw [sitex_sitex]
    have hv0 : ((sitex z 0) 0).val = 0 := sitex_val hq z (by omega)
    refine A_zero_off A hsupp hQ ?_ ?_
    · show sitex z 0 ∉ _
      rw [mem_Om1, hv0]; omega
    · show periodicLatticeShift (sitex z 0) μ ∉ _
      rw [mem_Om1, shift_coord_ne _ (Ne.symm hμ), hv0]; omega
  rw [e1, e2, sub_zero, add_zero]

omit hq hR A in
theorem update_shift_succ {L : PeriodicLatticeExtent} (w : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) :
    Function.update w μ (w μ + ((n + 1 : ℕ) : Fin (L μ + 1))) =
      periodicLatticeShift (Function.update w μ (w μ + ((n : ℕ) : Fin (L μ + 1)))) μ := by
  unfold periodicLatticeShift
  rw [Function.update_idem, Function.update_self, Nat.cast_succ, add_assoc]

include hq hR hsupp hQ in
theorem Iv_update
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0)
    (v : Fin (scaleUp 2 1 (dilLu q R) μ + 1)) :
    Iv A (Function.update z μ v) = Iv A z := by
  have hn : ∀ n : ℕ, Iv A (Function.update z μ (z μ + ((n : ℕ) : Fin _))) = Iv A z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [update_shift_succ, Iv_shiftT hq hR A hsupp hQ hcurl _ hμ, ih]
  have h := hn (v - z μ).val
  rw [Fin.cast_val_eq_self, add_sub_cancel] at h
  exact h

omit hq hR A in
theorem Iv_update0 (A : BondFnL2 (scaleUp 2 1 (dilLu q R))) (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (v : Fin (scaleUp 2 1 (dilLu q R) 0 + 1)) : Iv A (Function.update z 0 v) = Iv A z := by
  unfold Iv sitex
  rw [Function.update_idem]

include hq hR hsupp hQ in
theorem Iv_const
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : Iv A z = Iv A (fun _ => 0) := by
  have e : (fun _ => (0 : Fin _) : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) =
      Function.update (Function.update (Function.update z 0 0) 1 0) 2 0 := by
    funext ν
    fin_cases ν <;> simp [Function.update] <;> rfl
  rw [e, Iv_update hq hR A hsupp hQ hcurl _ (by decide), Iv_update hq hR A hsupp hQ hcurl _ (by decide),
    Iv_update0]

omit hq hR A in
theorem coarseShift_sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (t : ℕ) :
    coarseShift (sitex z t) 2 0 = sitex z (t + 2) := by
  show periodicLatticeShift (periodicLatticeShift (sitex z t) 0) 0 = _
  rw [shift_sitex0, shift_sitex0]

include hq hR hQ in
/-- one level-1 row along direction `0`: the block sums of the potential agree. -/
theorem row_step (y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (hy1 : 2 ∣ (y 1).val) (hy2 : 2 ∣ (y 2).val) (hy0 : 2 ∣ (y 0).val)
    (hlo : 2 * (R * q) + 4 * q ≤ (y 0).val + 2) (hhi : (y 0).val + 2 ≤ 10 * (R * q) + 12 * q) :
    ∑ w ∈ stepBlockOf (coarseShift y 2 0) 1 2, xi A w = ∑ w ∈ stepBlockOf y 1 2, xi A w := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  have hy0' : ((periodicLatticeShift y 0) 0).val = (y 0).val + 1 := shift0_val_lt y (by omega)
  have hcs0 : ((coarseShift y 2 0) 0).val = (y 0).val + 2 := by
    show ((periodicLatticeShift (periodicLatticeShift y 0) 0) 0).val = _
    rw [shift0_val_lt _ (by rw [hy0']; omega), hy0']
  have hcsT : ∀ ν : Fin 3, ν ≠ 0 → (coarseShift y 2 0) ν = y ν := by
    intro ν hν
    show (periodicLatticeShift (periodicLatticeShift y 0) 0) ν = y ν
    rw [shift_coord_ne _ hν, shift_coord_ne _ hν]
  have hc : (y, (0 : Fin 3)) ∈ bondsLam (geomOf 2 1 (dilTower q R)) 1 := by
    refine ⟨?_, ?_⟩
    · by_cases hya : 2 * (R * q) + 4 * q ≤ (y 0).val
      · left
        show y ∈ (geomOf 2 1 (dilTower q R)).Lam 1
        refine ⟨fun μ => ?_, (mem_Om1 _).mpr ⟨hya, by omega⟩, not_mem_Om2 _⟩
        show 2 ^ 1 ∣ (y μ).val
        fin_cases μ
        · simpa using hy0
        · simpa using hy1
        · simpa using hy2
      · right
        have e1 : coarseShift (y, (0 : Fin 3)).1 ((geomOf 2 1 (dilTower q R)).ell ^ 1) (y, (0 : Fin 3)).2 =
            coarseShift y 2 0 := rfl
        rw [e1]
        show coarseShift y 2 0 ∈ (geomOf 2 1 (dilTower q R)).Lam 1
        refine ⟨fun μ => ?_, (mem_Om1 _).mpr ⟨by rw [hcs0]; omega, by rw [hcs0]; omega⟩, not_mem_Om2 _⟩
        show 2 ^ 1 ∣ ((coarseShift y 2 0) μ).val
        fin_cases μ
        · show 2 ^ 1 ∣ ((coarseShift y 2 0) 0).val
          rw [hcs0]; simpa using (Nat.dvd_add hy0 (dvd_refl 2))
        · show 2 ^ 1 ∣ ((coarseShift y 2 0) 1).val
          rw [hcsT 1 (by decide)]; simpa using hy1
        · show 2 ^ 1 ∣ ((coarseShift y 2 0) 2).val
          rw [hcsT 2 (by decide)]; simpa using hy2
    · rintro (h | h) <;>
        exact not_OmGe_of_lt (G := geomOf 2 1 (dilTower q R)) (lt_of_eq_of_lt (dil_G_k q R) (by norm_num)) _ h
  let p : BIdx (geomOf 2 1 (dilTower q R)) := ⟨1, ⟨(y, 0), hc⟩⟩
  have hrow : WithLp.ofLp (QfullOf (geomOf 2 1 (dilTower q R)) flatCfg A) p = 0 := by
    rw [hQ]; rfl
  have hQrow := AdalyFormal.W6.Qflat_row (ell := 2) (k := 1) (Lu := dilLu q R) (S := dilTower q R)
    (by norm_num) A p
  have hline : AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictSuTwo (2 ^ (p.1 : ℕ))
      (WithLp.ofLp A) (AdalyFormal.W6.rowCB (by norm_num) p) = 0 := by
    rw [← hQrow]; exact hrow
  have hline' : (1 / ((2 : ℕ) : ℝ) ^ 4) • ∑ x ∈ blockOf y 2, ∑ i ∈ Finset.range 2,
      A (pathSite x 0 i, 0) = 0 := hline
  have hsum : ∑ x ∈ blockOf y 2, ∑ i ∈ Finset.range 2, A (pathSite x 0 i, 0) = 0 := by
    rcases smul_eq_zero.mp hline' with h | h
    · norm_num at h
    · exact h
  have hpt : ∀ x ∈ blockOf y 2, ∑ i ∈ Finset.range 2, A (pathSite x 0 i, 0) =
      xi A (coarseShift x 2 0) - xi A x := by
    intro x hx
    have hxb := (mem_blockOf.mp hx) 0
    have hx0 : (x 0).val + 1 < 12 * (R * q) + 16 * q := by omega
    have hsx : ((periodicLatticeShift x 0) 0).val = (x 0).val + 1 := shift0_val_lt x (by omega)
    have e1 := xi_shift0 hq A x hx0
    have e2 := xi_shift0 hq A (periodicLatticeShift x 0) (by rw [hsx]; omega)
    show _ = xi A (periodicLatticeShift (periodicLatticeShift x 0) 0) - xi A x
    rw [e2, e1, Finset.sum_range_succ, Finset.sum_range_one]
    show A (x, 0) + A (periodicLatticeShift x 0, 0) = _
    abel
  have hfit : ∀ ν : Fin 3, (y ν).val + 1 * 2 ≤ scaleUp 2 1 (dilLu q R) ν + 1 := by
    intro ν
    by_cases hν : ν = 0
    · subst hν; omega
    · have := xT_lt hq y hν
      have h8 := dsizeT (R := R) hq hν
      have hev : 2 ∣ (y ν).val := by
        fin_cases ν
        · exact absurd rfl hν
        · exact hy1
        · exact hy2
      omega
  have hfit' : ∀ ν : Fin 3, ((coarseShift y 2 0) ν).val + 1 * 2 ≤ scaleUp 2 1 (dilLu q R) ν + 1 := by
    intro ν
    by_cases hν : ν = 0
    · subst hν; rw [hcs0]; omega
    · rw [hcsT ν hν]; exact hfit ν
  have hshift := AdalyFormal.CurvBlock.block_sum_shift 1 2 2 0 hfit hfit' (xi A)
  rw [← hshift]
  rw [AdalyFormal.Balaban.QjComposite.stepBlockOf_one] at *
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib] at hsum
  exact sub_eq_zero.mp hsum

include hq hR hsupp hQ in
/-- the block sums vanish along the whole longitudinal chain of blocks. -/
theorem chain_zero (y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (hy1 : 2 ∣ (y 1).val) (hy2 : 2 ∣ (y 2).val) :
    ∀ m : ℕ, 2 * m ≤ 8 * (R * q) + 8 * q + 2 →
      ∑ w ∈ stepBlockOf (sitex y (2 * (R * q) + 4 * q - 2 + 2 * m)) 1 2, xi A w = 0 := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  intro m
  induction m with
  | zero =>
    intro _
    refine Finset.sum_eq_zero (fun w hw => ?_)
    have hb := ((AdalyFormal.Balaban.QjComposite.mem_stepBlockOf).mp hw) 0
    have hv : ((sitex y (2 * (R * q) + 4 * q - 2 + 2 * 0)) 0).val = 2 * (R * q) + 4 * q - 2 + 2 * 0 :=
      sitex_val hq y (by omega)
    rw [hv] at hb
    exact xi_left hq A hsupp hQ w (by omega)
  | succ m ih =>
    intro hm
    have hv : ((sitex y (2 * (R * q) + 4 * q - 2 + 2 * m)) 0).val = 2 * (R * q) + 4 * q - 2 + 2 * m :=
      sitex_val hq y (by omega)
    have e : sitex y (2 * (R * q) + 4 * q - 2 + 2 * (m + 1)) =
        coarseShift (sitex y (2 * (R * q) + 4 * q - 2 + 2 * m)) 2 0 := by
      rw [coarseShift_sitex]
      congr 1
    rw [e, row_step hq hR A hQ _ (by rw [sitex_coord _ _ (by decide)]; exact hy1)
      (by rw [sitex_coord _ _ (by decide)]; exact hy2) (by rw [hv]; omega) (by rw [hv]; omega)
      (by rw [hv]; omega)]
    exact ih (by omega)

include hq hR hsupp hQ in
theorem Iv_zero
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0) :
    Iv A (fun _ => 0) = 0 := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  let y0 : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) := fun _ => 0
  have hb := chain_zero hq hR A hsupp hQ y0 (by simp [y0]) (by simp [y0])
    (4 * (R * q) + 4 * q + 1) (by omega)
  have hv : ((sitex y0 (2 * (R * q) + 4 * q - 2 + 2 * (4 * (R * q) + 4 * q + 1))) 0).val =
      10 * (R * q) + 12 * q := by
    rw [sitex_val hq y0 (by omega)]; omega
  have e : ∀ w ∈ stepBlockOf (sitex y0 (2 * (R * q) + 4 * q - 2 + 2 * (4 * (R * q) + 4 * q + 1))) 1 2,
      xi A w = Iv A (fun _ => 0) := by
    intro w hw
    have hwb := ((AdalyFormal.Balaban.QjComposite.mem_stepBlockOf).mp hw) 0
    rw [hv] at hwb
    rw [xi_right hq A hsupp hQ w (by omega)]
    exact Iv_const hq hR A hsupp hQ hcurl w
  have hfit : ∀ ν : Fin 3, ((sitex y0 (2 * (R * q) + 4 * q - 2 + 2 * (4 * (R * q) + 4 * q + 1))) ν).val
      + 1 * 2 ≤ scaleUp 2 1 (dilLu q R) ν + 1 := by
    intro ν
    by_cases hν : ν = 0
    · subst hν; rw [hv]; omega
    · rw [sitex_coord _ _ hν]
      have h8 := dsizeT (R := R) hq hν
      show ((0 : Fin _) : ℕ) + 1 * 2 ≤ _
      simp only [Fin.val_zero]
      omega
  rw [Finset.sum_congr rfl e, Finset.sum_const,
    AdalyFormal.Balaban.QjComposite.card_stepBlockOf _ 1 2 one_pos hfit] at hb
  have h8 : (8 : ℝ) • Iv A (fun _ => 0) = 0 := by
    rw [show (8 : ℝ) = ((2 ^ 3 : ℕ) : ℝ) by norm_num, Nat.cast_smul_eq_nsmul]
    exact hb
  rcases smul_eq_zero.mp h8 with h | h
  · norm_num at h
  · exact h

include hq hR hsupp hQ in
theorem xi_mem_NQp
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0) :
    (WithLp.toLp 2 (xi A) : SiteL2 (scaleUp 2 1 (dilLu q R))) ∈
      NQp (geomOf 2 1 (dilTower q R)) flatCfg := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  have hzero : ∀ x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)),
      ¬ ((dilTower q R).Om 1 x) → xi A x = 0 := by
    intro x hx
    have hx' : ¬ (2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q) := hx
    by_cases h : (x 0).val < 2 * (R * q) + 4 * q
    · exact xi_left hq A hsupp hQ x h
    · rw [xi_right hq A hsupp hQ x (by omega)]
      show Iv A x = 0
      rw [Iv_const hq hR A hsupp hQ hcurl x, Iv_zero hq hR A hsupp hQ hcurl]
  refine ⟨fun x hx => ?_, fun j hj y hy => ?_⟩
  · show xi A x = 0
    refine hzero x (fun h1 => hx ?_)
    have h1' : 2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q := h1
    show 4 * q ≤ (x 0).val ∧ (x 0).val < 12 * (R * q) + 12 * q
    omega
  · have hj1 : j = 0 ∨ j = 1 := by
      have : j ≤ 1 := hj
      omega
    rcases hj1 with rfl | rfl
    · rw [Qlev_apply, AdalyFormal.Balaban.QjComposite.Qcomposite_zero]
      show xi A y = 0
      exact hzero y hy.2.2
    · rw [Qlev_apply, Qcomposite_one', bgTower_zero']
      show stepAverage (2 ^ 0) (trivialU _) 2 (xi A) y = 0
      rw [AdalyFormal.Balaban.QjComposite.stepAverage_trivialU, pow_zero]
      obtain ⟨hdiv, hy1, -⟩ := hy
      have hy1' : 2 * (R * q) + 4 * q ≤ (y 0).val ∧ (y 0).val < 10 * (R * q) + 12 * q := hy1
      have hd0 : 2 ∣ (y 0).val := by simpa using hdiv 0
      have hd1 : 2 ∣ (y 1).val := by simpa using hdiv 1
      have hd2 : 2 ∣ (y 2).val := by simpa using hdiv 2
      obtain ⟨m, hm⟩ : ∃ m, (y 0).val = 2 * (R * q) + 4 * q - 2 + 2 * m := by
        obtain ⟨t, ht⟩ := hd0
        refine ⟨t - (R * q) - 2 * q + 1, ?_⟩
        omega
      have hc := chain_zero hq hR A hsupp hQ y hd1 hd2 m (by omega)
      rw [← hm, sitex_self] at hc
      rw [hc, smul_zero]

include hq hR hsupp hQ in
theorem A_eq_grad
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0) :
    A = gradL2 flatCfg (WithLp.toLp 2 (xi A)) := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  refine PiLp.ext (fun e => ?_)
  obtain ⟨z, μ⟩ := e
  show A (z, μ) = gradValueCovariant flatCfg (xi A) (z, μ)
  simp only [gradValueCovariant, flatCfg, RMap_one, LinearMap.id_apply]
  have hz := x0_lt hq z
  by_cases hμ : μ = 0
  · subst hμ
    by_cases hz1 : (z 0).val + 1 < 12 * (R * q) + 16 * q
    · rw [xi_shift0 hq A z hz1]; abel
    · have hzl : (z 0).val + 1 = scaleUp 2 1 (dilLu q R) 0 + 1 := by omega
      have h0 : ((periodicLatticeShift z 0) 0).val = 0 := shift0_val_last z hzl
      have e1 : xi A (periodicLatticeShift z 0) = 0 := xi_left hq A hsupp hQ _ (by rw [h0]; omega)
      have e2 : xi A z = 0 := by
        rw [xi_right hq A hsupp hQ z (by omega)]
        show Iv A z = 0
        rw [Iv_const hq hR A hsupp hQ hcurl z, Iv_zero hq hR A hsupp hQ hcurl]
      have e3 : A (z, 0) = 0 := by
        refine A_zero_off A hsupp hQ ?_ ?_
        · show z ∉ _
          rw [mem_Om1]; omega
        · show periodicLatticeShift z 0 ∉ _
          rw [mem_Om1, h0]; omega
      rw [e1, e2, e3, sub_zero]
  · rw [xi_shiftT hq hR A hsupp hQ hcurl z hμ]
    have hv0 : ((sitex z 0) 0).val = 0 := sitex_val hq z (by omega)
    have e3 : A (sitex z 0, μ) = 0 := by
      refine A_zero_off A hsupp hQ ?_ ?_
      · show sitex z 0 ∉ _
        rw [mem_Om1, hv0]; omega
      · show periodicLatticeShift (sitex z 0) μ ∉ _
        rw [mem_Om1, shift_coord_ne _ (Ne.symm hμ), hv0]; omega
    rw [e3]; abel

include hq hR hsupp hQ in
/-- **The flat kernel of the dilated tower is trivial.** -/
theorem dil_flat_kernel
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (hT : Tfull (geomOf 2 1 (dilTower q R)) flatCfg A = 0) : A = 0 := by
  have hg := A_eq_grad hq hR A hsupp hQ hcurl
  have hmem := xi_mem_NQp hq hR A hsupp hQ hcurl
  rw [hg] at hT ⊢
  exact final_step' _ _ hmem hT

end Kernel

end FlatKernel

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## K. Assembly: the soft premise `InteriorSoft` of round 1 holds -/
section FlatCarrier

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilU)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantCLM_L2_toLp)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply)

/-- The flat localized carrier form is a sum of three squares (frozen `NsPtD1.flat_ginv_form`,
outside the `DrEquiv` closure, restated for the pinned localized assembly). -/
theorem flat_ginv_form_in (P : IngrBParams) (hU : P.U = flatCfg) (x : ↥(bondSupp P.G)) :
    ⟪x, (dataS selIn selIn P).Ginv x⟫ =
      ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖ ^ 2
      + ‖Tfull P.G P.U (iE P.G x)‖ ^ 2
      + ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 := by
  rw [BaseDataS.inner_Ginv]
  have hD : ⟪x, (dataS selIn selIn P).Dpi x⟫ =
      ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖ ^ 2 := by
    have : ⟪x, (dataS selIn selIn P).Dpi x⟫ = ⟪iE P.G x, DpiFull P.G P.U P.a (iE P.G x)⟫ := by
      show ⟪x, (pE P.G) (DpiFull P.G P.U P.a (iE P.G x))⟫ = _
      rw [pE_inner_right]
    rw [this, hU]
    exact AdalyFormal.StatementLaneG.inner_DpiFull_flat P.G P.a (iE P.G x)
  have hM : ⟪x, (dataS selIn selIn P).Mass x⟫ =
      ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 := by
    have : ⟪x, (dataS selIn selIn P).Mass x⟫ = ⟪iE P.G x, MassFull P.G P.a P.sector (iE P.G x)⟫ := by
      show ⟪x, (pE P.G) (MassFull P.G P.a P.sector (iE P.G x))⟫ = _
      rw [pE_inner_right]
    rw [this, inner_MassFull]
    rfl
  rw [hD, hM]
  rfl

/-- The flat localized carrier of the dilated tower is positive definite. -/
theorem dil_flat_pos {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (x : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) (hx : x ≠ 0) :
    0 < ⟪x, (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R))).Ginv x⟫ := by
  set P := gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (fun _ => 1) 1 (dilLam q R) with hP
  have hform := flat_ginv_form_in P rfl x
  have t1 := sq_nonneg ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖
  have t2 := sq_nonneg ‖Tfull P.G P.U (iE P.G x)‖
  have hell : (0 : ℝ) < P.ell := by show (0 : ℝ) < (2 : ℕ); norm_num
  have t3 : 0 ≤ ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 :=
    Finset.sum_nonneg (fun p _ => by
      have : (0 : ℝ) < P.a := by show (0 : ℝ) < 1; norm_num
      positivity)
  rcases (add_nonneg (add_nonneg t1 t2) t3).lt_or_eq with h | h
  · rw [hform]; exact h
  · exfalso
    apply hx
    have h1 : ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖ ^ 2 = 0 := by
      linarith
    have h2 : ‖Tfull P.G P.U (iE P.G x)‖ ^ 2 = 0 := by linarith
    have h3 : ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 = 0 := by
      linarith
    have hm : plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x)) = 0 :=
      norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)
    have hT : Tfull P.G P.U (iE P.G x) = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
    have hQ : QfullOf (geomOf 2 1 (dilTower q R)) flatCfg (iE P.G x) = 0 := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => by
        have : (0 : ℝ) < P.a := by show (0 : ℝ) < 1; norm_num
        positivity)).mp h3
      refine PiLp.ext (fun p => ?_)
      have h1 := hz p (Finset.mem_univ p)
      have hp : 0 < P.a * (P.ell : ℝ) ^ (p.1 : ℕ) := by
        have : (0 : ℝ) < P.a := by show (0 : ℝ) < 1; norm_num
        positivity
      have h2 : ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact absurd h hp.ne'
        · exact h
      have := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
      exact this
    have hsupp : ∀ b, b ∉ bondsOm0 (geomOf 2 1 (dilTower q R)) → (iE P.G x) b = 0 :=
      fun b hb => x.2 b hb
    have hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0),
        curlValueCovariant flatCfg (WithLp.ofLp (iE P.G x)) p = 0 := by
      intro p hp
      have h := congrArg (fun v : AdalyFormal.Balaban.CovariantHjMinimizer.PlaqFnL2 P.Lf => WithLp.ofLp v p) hm
      simp only [plaqMask_apply, PiLp.zero_apply] at h
      rw [if_pos (show p ∈ plaqIn P.G.Om0 from hp)] at h
      have e : curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x) =
          WithLp.toLp 2 (curlValueCovariant flatCfg (WithLp.ofLp (iE P.G x))) :=
        curlCovariantCLM_L2_toLp _ _
      rw [e] at h
      exact h
    have hA := dil_flat_kernel hq hR (iE P.G x) hsupp hQ hcurl hT
    exact Subtype.ext hA

theorem dil_flat_unit {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) :
    IsUnit (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R))).Ginv := by
  set M : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
    (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R))).Ginv with hMdef
  have hinj : Function.Injective M := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hne
    have := dil_flat_pos hq hR x hne
    rw [hx, inner_zero_right] at this
    exact lt_irrefl _ this
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (M : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →ₗ[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))))).mp hinj⟩

end FlatCarrier

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

section Final

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilU)
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace extP extA extD InteriorRegularity InteriorSoft)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

/-- the curved dilated family. -/
noncomputable abbrev dilV (q R : ℕ) : ℝ → Cfg (scaleUp 2 1 (dilLu q R)) := fun ε => dilU q R ε 1

theorem dataFam_dil_zero (sD sJ : PlaqSel) (q R : ℕ) :
    dataFam sD sJ (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0 =
      dataS sD sJ (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (fun _ => 1) 1 (dilLam q R)) := by
  show dataS sD sJ (gparams 2 1 (dilLu q R) _ (dilTower q R) (dilU q R 0 1) 1 (dilLam q R)) = _
  rw [dilU_zero]

theorem dil_B0_unit {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) :
    IsUnit (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).Ginv := by
  rw [dataFam_dil_zero]
  exact dil_flat_unit hq hR

theorem dil_B0_psd {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) :
    AdalyFormal.D1Literal.PSD
      (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).Ginv := by
  rw [dataFam_dil_zero]
  intro v
  by_cases hv : v = 0
  · rw [hv, inner_zero_left]
  · exact (dil_flat_pos hq hR v hv).le

theorem dil_Qs0_inj {q R : ℕ} (hq : 0 < q) (hR16 : 16 ≤ R)
    (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    Function.Injective
      (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).Qs := by
  rw [dataFam_dil_zero]
  exact dil_Qs_inj hq hR16 hS

theorem dil_N0_unit {q R : ℕ} (hq : 0 < q) (hR16 : 16 ≤ R)
    (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    IsUnit (((dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).Q.comp
      (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).G).comp
      (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).Qs) := by
  set D0 := dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0
  have hL : D0.Laws := dataS_laws selIn selIn _
  obtain ⟨m, hm, hmc⟩ := AdalyFormal.D1Literal.psd_coercive D0.Ginv (D0.Ginv_symm hL)
    (dil_B0_psd hq (by omega)) (dil_B0_unit hq (by omega))
  exact isUnit_Q_inv_Qs (D0.Ginv_symm hL) hm hmc D0.Q_adj (dil_Qs0_inj hq hR16 hS)

theorem extA_eq_dataFam (q R : ℕ) (ε : ℝ) :
    extA q R ε 1 = (dataFam selAll selAll (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).Ginv := rfl

theorem extD_eq_dataFam (q R : ℕ) (ε : ℝ) :
    extD q R ε 1 = (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).Delta2 (dataS_laws selIn selIn _) := rfl

theorem C2_dataFam (q R : ℕ) (ε : ℝ) (A : TwistSpace q R) :
    (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) ε).C2 A =
      C2fullOf (geomOf 2 1 (dilTower q R)) (dilV q R ε)
        (Wop (geomOf 2 1 (dilTower q R)) (dilV q R ε) 1 (iE (geomOf 2 1 (dilTower q R)) A)) := rfl

theorem J_dataFam (q R : ℕ) (ε : ℝ) :
    (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) ε).J =
      pE (geomOf 2 1 (dilTower q R)) (WithLp.toLp 2 (fun b => -(AdalyFormal.IngredientFamily.JSU2Loc 1
        (plaqIn (geomOf 2 1 (dilTower q R)).Om0) (dilV q R ε) b))) := rfl

theorem Q_dataFam (q R : ℕ) (ε : ℝ) :
    (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) ε).Q =
      (QfullOf (geomOf 2 1 (dilTower q R)) (dilV q R ε)).comp (iE (geomOf 2 1 (dilTower q R))) := rfl

theorem Qs_dataFam (q R : ℕ) (ε : ℝ) :
    (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) ε).Qs =
      ContinuousLinearMap.adjoint
        ((QfullOf (geomOf 2 1 (dilTower q R)) (dilV q R ε)).comp (iE (geomOf 2 1 (dilTower q R)))) := rfl

section DilCont
variable {q R : ℕ} (hq : 0 < q) (hS : Admissible 2 (2 * q) R 1 (dilTower q R))

omit hq hS in
theorem dil_reg0 (q R : ℕ) :
    RegBg ((geomOf 2 1 (dilTower q R)).ell ^ 0) (geomOf 2 1 (dilTower q R)).ell (dilV q R 0) := by
  rw [show dilV q R 0 = fun _ => 1 from dilU_zero q R]; exact RegBg_flat _ _

omit hq hS in
theorem dil_LP0 (hq : 0 < q) : IsUnit (AdalyFormal.M1Site.LP (geomOf 2 1 (dilTower q R)) (dilV q R 0) 1) :=
  dil_LP_unit q R hq _

omit hq hS in
theorem dil_Gam0 (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    IsUnit (Gam (geomOf 2 1 (dilTower q R)) (dilV q R 0) 1) := by
  rw [show dilV q R 0 = fun _ => 1 from dilU_zero q R]; exact dil_Gam_unit hS

include hq hS in
theorem dil_W_cont : ContinuousAt (fun ε => Wop (geomOf 2 1 (dilTower q R)) (dilV q R ε) 1) 0 :=
  continuousAt_Wop (dilU_contFam q R) (geomOf 2 1 (dilTower q R)) rfl 1 (dil_LP0 hq) (dil_wq_pos q R)
    (dil_Gam0 hS)

include hq hS in
theorem dil_T_cont : ContinuousAt (fun ε => Tfull (geomOf 2 1 (dilTower q R)) (dilV q R ε)) 0 :=
  continuousAt_Tfull (dilU_contFam q R) (geomOf 2 1 (dilTower q R)) rfl 1 (dil_LP0 hq) (dil_wq_pos q R)
    (dil_Gam0 hS)

omit hq hS in
theorem dil_Q_cont (q R : ℕ) : ContinuousAt (fun ε => QfullOf (geomOf 2 1 (dilTower q R)) (dilV q R ε)) 0 :=
  continuousAt_QfullOf (dilV q R) (dilU_smooth q R) (geomOf 2 1 (dilTower q R)) rfl (dil_reg0 q R)

include hq hS in
theorem dil_carrier_cont (sD sJ : PlaqSel) :
    ContinuousAt (fun ε => (dataFam sD sJ (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).Ginv) 0 :=
  continuousAt_Ginv_dataS sD sJ (by norm_num) (dilTower q R) (dilV q R) 1 (dilLam q R)
    (dilU_contFam q R) (dil_W_cont hq hS) (dil_T_cont hq hS) (dil_Q_cont q R)

include hq hS in
theorem dil_tendsto_extA :
    Tendsto (fun ε : ℝ => extA q R ε 1) (𝓝[>] 0) (𝓝 (extA q R 0 1)) := by
  simp only [extA_eq_dataFam]
  exact (dil_carrier_cont hq hS selAll selAll).tendsto.mono_left nhdsWithin_le_nhds

include hq hS in
theorem dil_tendsto_W :
    Tendsto (fun ε : ℝ => Wop (geomOf 2 1 (dilTower q R)) (dilU q R ε 1) 1) (𝓝[>] 0)
      (𝓝 (Wop (geomOf 2 1 (dilTower q R)) (dilU q R 0 1) 1)) :=
  (dil_W_cont hq hS).tendsto.mono_left nhdsWithin_le_nhds

include hq hS in
theorem dil_H_cont (hR : 16 ≤ R) :
    ContinuousAt (fun ε => (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).H) 0 := by
  have hQc : ContinuousAt (fun ε => (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).Q) 0 := by
    simp only [Q_dataFam]
    exact continuousAt_clm_comp (dil_Q_cont q R) continuousAt_const
  have hQsc : ContinuousAt (fun ε => (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).Qs) 0 := by
    simp only [Qs_dataFam]
    exact cont_adjoint.continuousAt.comp (continuousAt_clm_comp (dil_Q_cont q R) continuousAt_const)
  exact continuousAt_H _ (dil_carrier_cont hq hS selIn selIn) hQc hQsc (dil_B0_unit hq (by omega))
    (dil_N0_unit hq hR hS)

include hq hS in
theorem dil_C2_tendsto (A : TwistSpace q R) :
    Tendsto (fun ε => (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).C2 A) (𝓝 0) (𝓝 ((dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
        (dilV q R) 1 (dilLam q R) 0).C2 A)) := by
  simp only [C2_dataFam]
  exact tendsto_C2fullOf (dilV q R) (dilU_smooth q R) (geomOf 2 1 (dilTower q R)) rfl (dil_reg0 q R)
    (tendsto_clm_apply₂ (dil_W_cont hq hS) tendsto_const_nhds)

omit hq hS in
theorem dil_J_tendsto (q R : ℕ) : ∃ J' : TwistSpace q R,
    Tendsto (fun ε => ε⁻¹ • (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).J) (𝓝[≠] 0) (𝓝 J') := by
  obtain ⟨J', hJ'⟩ := exists_source_derivative (dilV q R) (dilU_smooth q R) (dilU_zero q R)
    (plaqIn (geomOf 2 1 (dilTower q R)).Om0)
  refine ⟨pE (geomOf 2 1 (dilTower q R)) J', ?_⟩
  simp only [J_dataFam, ← map_smul]
  exact ((pE (geomOf 2 1 (dilTower q R))).continuous.tendsto _).comp hJ'

include hq hS in
theorem dil_exists_D1 (hR : 16 ≤ R) : ∃ D₁ : TwistSpace q R →L[ℝ] TwistSpace q R,
    Tendsto (fun ε : ℝ => ε⁻¹ • extD q R ε 1) (𝓝[>] 0) (𝓝 D₁) := by
  obtain ⟨J', hJ⟩ := dil_J_tendsto q R
  have hH := dil_H_cont hq hS hR
  have hC2 := dil_C2_tendsto hq hS
  obtain ⟨D₁, hD₁⟩ := tendsto_Delta2_div
    (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R))
    (fun ε => dataS_laws selIn selIn
      (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (dilV q R ε) 1 (dilLam q R))) hH hC2 J' hJ
  refine ⟨D₁, ?_⟩
  simp only [extD_eq_dataFam]
  exact hD₁.mono_left (nhdsWithin_mono _ (fun x hx => ne_of_gt hx))

include hq hS in
/-- **The first-order coefficient, explicitly.**  Any limit `D₁` of `extD(ε)/ε` has the quadratic form
`A ↦ 2⟪H₀ C²₀(W₀ A), J'⟫`: `H₀`, `C²₀`, `W₀` are the flat (vacuum) constrained inverse, second
jet and dressing of the localized data, and `J'` the curvature derivative of the source. -/
theorem dil_D1_form (hR : 16 ≤ R) (D₁ : TwistSpace q R →L[ℝ] TwistSpace q R)
    (hD₁ : Tendsto (fun ε : ℝ => ε⁻¹ • extD q R ε 1) (𝓝[>] 0) (𝓝 D₁)) (J' : TwistSpace q R)
    (hJ : Tendsto (fun ε => ε⁻¹ • (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).J) (𝓝[≠] 0) (𝓝 J')) (A : TwistSpace q R) :
    ⟪A, D₁ A⟫ = 2 * ⟪(dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
        (fun _ => 1) 1 (dilLam q R))).H
      (C2fullOf (geomOf 2 1 (dilTower q R)) (fun _ => 1)
        (Wop (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1 (iE (geomOf 2 1 (dilTower q R)) A))), J'⟫ := by
  have hD₁' : Tendsto (fun ε => ε⁻¹ • (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).Delta2 (dataS_laws selIn selIn
        (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (dilV q R ε) 1 (dilLam q R))))
      (𝓝[>] 0) (𝓝 D₁) := by
    simp only [← extD_eq_dataFam]
    exact hD₁
  have h := limit_Delta2_div_form
    (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R))
    (fun ε => dataS_laws selIn selIn
      (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (dilV q R ε) 1 (dilLam q R)))
    (dil_H_cont hq hS hR) (dil_C2_tendsto hq hS) J' hJ D₁ hD₁' A
  rw [h, dataFam_dil_zero]
  rfl

end DilCont

/-- **Soft regularity of the curved dilated family at zero curvature**, for every scale and every
even radius `≥ 18`, given admissibility of the tower: the carrier and `W` are continuous at `ε = 0`
and `Δ⁽²⁾(ε)/ε` converges. -/
theorem interiorRegularity_of_admissible {q R : ℕ} (hq : 0 < q) (hR : 18 ≤ R)
    (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    ∃ D₁ : TwistSpace q R →L[ℝ] TwistSpace q R, InteriorRegularity q R D₁ := by
  obtain ⟨D₁, hD₁⟩ := dil_exists_D1 hq hS (by omega)
  exact ⟨D₁, dil_tendsto_extA hq hS, dil_tendsto_W hq hS, hD₁⟩

/-- `InteriorSoft` (round 1), given admissibility of the dilated towers. -/
theorem interiorSoft_of_admissible
    (hS : ∀ q R : ℕ, 0 < q → 2 ∣ R → Admissible 2 (2 * q) R 1 (dilTower q R)) : InteriorSoft :=
  fun q R hq hR hR18 => interiorRegularity_of_admissible hq hR18 (hS q R hq hR)

end Final

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## L. The soft premise closed; the reductions of this round -/
section Close

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilU dil_admissible)
open AdalyFormal.Round5.Guarded.IVTR1 (twistU twistP twistA twistD)
open AdalyFormal.Round8.Guarded.SignFree (CofinalTwistSeparation goalNeg2_of_cofinalTwistSeparation
  not_cofinalTwistSeparation_of_goalPos1)
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

/-- **Round 1's soft premise `InteriorSoft` holds**, for every scale and every even radius `≥ 18`. -/
theorem interiorSoft_proved : InteriorSoft :=
  interiorSoft_of_admissible (fun _ _ hq hR => dil_admissible hq hR)

/-- **Main reduction of this round**: the zero-curvature crossing data of the left twist refute
the guarded all-plaquette reading; no soft premise remains. -/
theorem goalNeg2_of_vacuumLeftSpectral (hc : VacuumLeftSpectral) : GoalNeg2 :=
  goalNeg2_of_interiorSoft_vacuumLeftSpectral interiorSoft_proved hc

/-- The positive reading forbids it. -/
theorem not_vacuumLeftSpectral_of_goalPos1 (h : GoalPos1) : ¬ VacuumLeftSpectral :=
  fun hc => goalNeg2_of_vacuumLeftSpectral hc (goalPos2_iff_goalPos1.mpr h)

/-- **Zero-curvature regularity of the round-8 twist family** (round 1's
`ZeroCurvatureRegularity`), for every scale and every even radius `≥ 18`. -/
theorem zeroCurvatureRegularity_proved {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    ∃ D₁ : TwistSpace q R →L[ℝ] TwistSpace q R, ZeroCurvatureRegularity q R D₁ := by
  obtain ⟨D₁, hA, hW, hD⟩ := interiorSoft_proved q R hq hR hR18
  have hV0 : AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0) 0 = 1 :=
    AdalyFormal.D1Literal.Uth_zero _
  refine ⟨D₁, fun t => ?_, ?_⟩
  · exact extA_joint_tendsto hq hR (by nlinarith) (AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0))
      (AdalyFormal.D1Literal.contFam_Uth _) (by rw [hV0]; exact hA) (by rw [hV0]; exact hW) t
  · show Tendsto (fun ε : ℝ => ε⁻¹ • extD q R ε (AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0) 0))
      (𝓝[>] 0) (𝓝 D₁)
    rw [hV0]
    exact hD

/-- The zero-curvature, spectral part of round 8's premise: for cofinal dyadic scales and,
for each, cofinal even radii `≥ 18`, the vacuum crossing data of the round-8 twist for the
first-order coefficient of its correction.  NOT proved here. -/
def CofinalTwistVacuumCrossing : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∀ D₁ : TwistSpace (2 ^ j) R →L[ℝ] TwistSpace (2 ^ j) R,
      Tendsto (fun ε : ℝ => ε⁻¹ • twistD (2 ^ j) R ε 1 0) (𝓝[>] 0) (𝓝 D₁) →
        VacuumCrossing (2 ^ j) R D₁

/-- **`X → CofinalTwistSeparation`** (round 8's target), with `X` purely spectral at zero
curvature. -/
theorem cofinalTwistSeparation_of_twistVacuumCrossing (h : CofinalTwistVacuumCrossing) :
    CofinalTwistSeparation := by
  apply cofinalTwistSeparation_of_cofinalVacuum
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
  obtain ⟨D₁, hreg⟩ := zeroCurvatureRegularity_proved (q := 2 ^ j) (by positivity) hR hR18
  exact ⟨R, hRR, hR, hR18, D₁, hreg, hc D₁ hreg.2⟩

theorem goalNeg2_of_twistVacuumCrossing (h : CofinalTwistVacuumCrossing) : GoalNeg2 :=
  goalNeg2_of_cofinalTwistSeparation (cofinalTwistSeparation_of_twistVacuumCrossing h)

theorem not_twistVacuumCrossing_of_goalPos1 (h : GoalPos1) : ¬ CofinalTwistVacuumCrossing :=
  fun h' => not_cofinalTwistSeparation_of_goalPos1 h (cofinalTwistSeparation_of_twistVacuumCrossing h')

/-! ### The remaining premises with the first-order coefficient written out

`vacCoupling q R J' v = 2⟪H₀ C²₀(W₀ v), J'⟫`: the flat (vacuum) constrained inverse `H₀`, the flat
second jet `C²₀` of the flat dressing `W₀ v`, and the curvature derivative `J'` of the localized
source (`IsSourceDerivative`, which exists: `dil_J_tendsto`).  By `dil_D1_form` this is the
quadratic form of the first-order coefficient `D₁`. -/

/-- The flat localized data of the dilated tower. -/
noncomputable abbrev flatData (q R : ℕ) :=
  dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (fun _ => 1) 1 (dilLam q R))

/-- The explicit vacuum coupling form `2⟪H₀ C²₀(W₀ v), J'⟫`. -/
noncomputable def vacCoupling (q R : ℕ) (J' : TwistSpace q R) (v : TwistSpace q R) : ℝ :=
  2 * ⟪(flatData q R).H (C2fullOf (geomOf 2 1 (dilTower q R)) (fun _ => 1)
    (Wop (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1 (iE (geomOf 2 1 (dilTower q R)) v))), J'⟫

/-- `J'` is the curvature derivative of the localized source of the curved dilated family. -/
def IsSourceDerivative (q R : ℕ) (J' : TwistSpace q R) : Prop :=
  Tendsto (fun ε => ε⁻¹ • (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
    (dilLam q R) ε).J) (𝓝[≠] 0) (𝓝 J')

/-- Crossing data of a vacuum carrier path, with the explicit coupling form.  NOT proved here. -/
def CouplingCrossing (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (J' : TwistSpace q R) :
    Prop :=
  ∃ (t₀ : ℝ) (X' : TwistSpace q R →L[ℝ] TwistSpace q R),
    HasDerivAt (fun t => extA q R 0 (V t)) X' t₀ ∧
    (∃ v, extA q R 0 (V t₀) v = 0 ∧ v ≠ 0) ∧
    (∀ v, extA q R 0 (V t₀) v = 0 → v ≠ 0 → ⟪v, X' v⟫ < 0) ∧
    ((∀ v, extA q R 0 (V t₀) v = 0 → v ≠ 0 → vacCoupling q R J' v < 0) ∨
      (∀ v, extA q R 0 (V t₀) v = 0 → v ≠ 0 → 0 < vacCoupling q R J' v))

/-- The left-twist premise with the explicit coupling form.  NOT proved here. -/
def VacuumLeftCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∀ J' : TwistSpace (2 ^ j) R, IsSourceDerivative (2 ^ j) R J' →
      CouplingCrossing (2 ^ j) R (leftTwist (2 ^ j) R) J'

theorem pathCrossing_of_couplingCrossing {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (J' : TwistSpace q R) (hJ : IsSourceDerivative q R J')
    (D₁ : TwistSpace q R →L[ℝ] TwistSpace q R)
    (hD₁ : Tendsto (fun ε : ℝ => ε⁻¹ • extD q R ε 1) (𝓝[>] 0) (𝓝 D₁))
    (h : CouplingCrossing q R V J') : PathCrossing q R V D₁ := by
  obtain ⟨t₀, X', hder, hne, hslope, hsign⟩ := h
  have hform : ∀ v, ⟪v, D₁ v⟫ = vacCoupling q R J' v := fun v =>
    dil_D1_form hq (dil_admissible hq hR) hR16 D₁ hD₁ J' hJ v
  refine ⟨t₀, X', hder, hne, hslope, ?_⟩
  rcases hsign with h | h
  · exact Or.inl (fun v hv hv0 => by rw [hform]; exact h v hv hv0)
  · exact Or.inr (fun v hv hv0 => by rw [hform]; exact h v hv hv0)

theorem vacuumLeftSpectral_of_coupling (h : VacuumLeftCoupling) : VacuumLeftSpectral := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
  refine ⟨R, hRR, hR, hR18, fun D₁ hD₁ => ?_⟩
  obtain ⟨J', hJ'⟩ := dil_J_tendsto (2 ^ j) R
  exact pathCrossing_of_couplingCrossing (by positivity) hR (by omega) _ J' hJ' D₁ hD₁ (hc J' hJ')

/-- **The reduction with every ingredient explicit**: the zero-curvature left-twist crossing
data, with the explicit coupling form, refute the guarded all-plaquette reading. -/
theorem goalNeg2_of_vacuumLeftCoupling (h : VacuumLeftCoupling) : GoalNeg2 :=
  goalNeg2_of_vacuumLeftSpectral (vacuumLeftSpectral_of_coupling h)

/-- The round-8 twist premise with the explicit coupling form.  NOT proved here. -/
def CofinalTwistVacuumCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∀ J' : TwistSpace (2 ^ j) R, IsSourceDerivative (2 ^ j) R J' →
      CouplingCrossing (2 ^ j) R (AdalyFormal.D1Literal.Uth ((dilTower (2 ^ j) R).Om 0)) J'

/-- **`X → CofinalTwistSeparation`** with `X` the explicit zero-curvature coupling data of the
round-8 twist. -/
theorem cofinalTwistSeparation_of_twistVacuumCoupling (h : CofinalTwistVacuumCoupling) :
    CofinalTwistSeparation := by
  apply cofinalTwistSeparation_of_twistVacuumCrossing
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
  refine ⟨R, hRR, hR, hR18, fun D₁ hD₁ => ?_⟩
  obtain ⟨J', hJ'⟩ := dil_J_tendsto (2 ^ j) R
  have hV0 : AdalyFormal.D1Literal.Uth ((dilTower (2 ^ j) R).Om 0) 0 = 1 :=
    AdalyFormal.D1Literal.Uth_zero _
  have hD₁' : Tendsto (fun ε : ℝ => ε⁻¹ • extD (2 ^ j) R ε 1) (𝓝[>] 0) (𝓝 D₁) := by
    have e : (fun ε : ℝ => ε⁻¹ • twistD (2 ^ j) R ε 1 0) =
        fun ε : ℝ => ε⁻¹ • extD (2 ^ j) R ε (AdalyFormal.D1Literal.Uth ((dilTower (2 ^ j) R).Om 0) 0) :=
      rfl
    rw [e, hV0] at hD₁
    exact hD₁
  exact pathCrossing_of_couplingCrossing (by positivity) hR (by omega) _ J' hJ' D₁ hD₁' (hc J' hJ')

theorem goalNeg2_of_twistVacuumCoupling (h : CofinalTwistVacuumCoupling) : GoalNeg2 :=
  goalNeg2_of_cofinalTwistSeparation (cofinalTwistSeparation_of_twistVacuumCoupling h)

end Close

end AdalyFormal.Round9.Guarded.AnalyticR2


#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_of_inner
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_clm_of_apply
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_clm_of_inner
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.inner_suTwo
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_suTwo_of_coe
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuous_suTwo_of_coe
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_piLp_suTwo
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuous_piLp_suTwo
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuous_coe_suTwo
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cont_coarsePathHolonomy
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cont_RMap_coe
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cont_gradL2
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cont_adjoint
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cont_gradAdj
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cont_lapFull
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Qcomposite_one'
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.bgTower_zero'
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cont_Qlev
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cont_Qpa
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cont_DelpA
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cont_LP
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cont_QpP
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Gam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Rproj_formula
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_inverse_comp
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_clm_comp
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_LinvP
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_Xop
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_Gam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_Rproj
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_Tfull
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_Wop
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.ajSeq_pos
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Qpa_nonneg
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.delpA_inner_ge
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.covConst_norm
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.delpA_unit
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.wq_pos
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_clm_of_apply'
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.SmoothAt0
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.SG_V0
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.SG_V1
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.SG_prod
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.SG_loopVar_fam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.SG_sbg_fam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.SG_rProd_fam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.SG_su2Exp_sBlock_fam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.SG_su2Exp_neg_sBlock_fam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.SG_rawStep_fam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.contDiffAt_qStep_fam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_fderiv_qStep
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_fderiv2_qStep
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_clm_apply₂
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.suCoordL
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.QfullOf_apply
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.C2fullOf_apply
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.QlinB_one_coe
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.C2rawB_zero'
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.C2rawB_one_coe
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_QlinB1_coe
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_QfullOf
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_C2fullOf
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Ginv_dataS_eq
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dataFam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Ginv_dataFam_eq
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_Ginv_dataS
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_H
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.inner_polarization
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_Delta2_div_form
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_Delta2_div
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.limit_Delta2_div_form
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.SG_holonomyElem
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cd_imHolonomy
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cd_piProj
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cd_FnuMuLoc
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cd_DstarDir
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cd_JfieldLoc
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cd_JSU2Loc
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.source_slope
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.exists_source_derivative
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.contDiff_Xm
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.contDiffAt_Ug
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dilU_link_contDiff
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dilU_smooth
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dilU_contFam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dilU_zero
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_G_k
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_G_ell
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_out_site
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_LP_unit
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_wq_pos
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.bgTower_one
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_Gam_unit
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.delW_zero
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_Qs_inj
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.siteMask_eq_self_of_supp'
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.lapDir_eq_mask_lap'
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.final_step'
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dsize0
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dsizeT
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.x0_lt
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.xT_lt
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.mem_Om0
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.mem_Om1
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.not_mem_Om2
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.shift_coord_ne
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.shift_self_coord
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.shift0_val_lt
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.shift0_val_last
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.OmGe1_mem
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.A_zero_off
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.sitex
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.sitex_val
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.sitex_coord
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.sitex_self
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.sitex_sitex
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.shift_sitex0
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.shift_sitex
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.sitex_of_shift0
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.xi
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.xi_shift0
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.trans_step
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.xi_shiftT
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.xi_left
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.xi_right
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Iv
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Iv_shiftT
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.update_shift_succ
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Iv_update
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Iv_update0
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Iv_const
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.coarseShift_sitex
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.row_step
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.chain_zero
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Iv_zero
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.xi_mem_NQp
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.A_eq_grad
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_flat_kernel
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.flat_ginv_form_in
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_flat_pos
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_flat_unit
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dilV
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dataFam_dil_zero
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_B0_unit
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_B0_psd
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_Qs0_inj
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_N0_unit
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.extA_eq_dataFam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.extD_eq_dataFam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.C2_dataFam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.J_dataFam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Q_dataFam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Qs_dataFam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_reg0
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_LP0
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_Gam0
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_W_cont
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_T_cont
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_Q_cont
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_carrier_cont
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_tendsto_extA
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_tendsto_W
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_H_cont
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_C2_tendsto
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_J_tendsto
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_exists_D1
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_D1_form
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.interiorRegularity_of_admissible
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.interiorSoft_of_admissible
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.interiorSoft_proved
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_vacuumLeftSpectral
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.not_vacuumLeftSpectral_of_goalPos1
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.zeroCurvatureRegularity_proved
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.CofinalTwistVacuumCrossing
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cofinalTwistSeparation_of_twistVacuumCrossing
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_twistVacuumCrossing
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.not_twistVacuumCrossing_of_goalPos1
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.flatData
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.vacCoupling
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.IsSourceDerivative
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.CouplingCrossing
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.VacuumLeftCoupling
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.pathCrossing_of_couplingCrossing
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.vacuumLeftSpectral_of_coupling
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_vacuumLeftCoupling
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.CofinalTwistVacuumCoupling
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cofinalTwistSeparation_of_twistVacuumCoupling
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_twistVacuumCoupling
