
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
