
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
