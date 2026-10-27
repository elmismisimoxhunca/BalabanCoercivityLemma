import GCg2
import GCg3

/-!
# GCg4 -- G5 (`tauExt` and its adjoint) and G6 (conditional invariance of `GenP.genForm`).

`u y = γ (embY ell k Lu hell y)` is the unit gauge induced by a fine gauge `γ`.
G6 hypotheses are bundled in `GenFormHyps` with SEPARATE named fields (`base` = the six bond-level
hypotheses of G2 incl. `J`; `D2` = the `D2in` equivariance of G4); `τ` is PROVED here (G5).
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace AdalyFormal.GaugeCov
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA gaugeActA_apply)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.StatementLane (scaleUp Tower)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneG

/-- the unit gauge induced by a fine gauge. -/
def uOf (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (γ : GaugeFn (scaleUp ell k Lu)) : GaugeFn Lu :=
  fun y => γ (embY ell k Lu hell y)

/-- **G5.** `τ ∘ Ad_γ = Ad_u ∘ τ`. -/
theorem tauExt_gauge (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (γ : GaugeFn (scaleUp ell k Lu)) (f : FSp (geomOf ell k S)) :
    tauExt ell k Lu hell S (adFL γ (geomOf ell k S) f) =
      adBL (uOf ell k Lu hell γ) (tauExt ell k Lu hell S f) := by
  refine PiLp.ext (fun e => ?_)
  simp only [tauExt, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    WithLp.ofLp_toLp, PiLp.toLp_apply, adGen_apply, uOf]
  split_ifs with hb
  · rfl
  · simp

/-- **G5 (adjoint).** `τ* ∘ Ad_u = Ad_γ ∘ τ*`. -/
theorem tauExt_adjoint_gauge (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (γ : GaugeFn (scaleUp ell k Lu)) (y : BondFnL2 Lu) :
    ContinuousLinearMap.adjoint (tauExt ell k Lu hell S) (adBL (uOf ell k Lu hell γ) y) =
      adFL γ (geomOf ell k S) (ContinuousLinearMap.adjoint (tauExt ell k Lu hell S) y) :=
  adjoint_intertwine (adFL γ (geomOf ell k S)) (adBL (uOf ell k Lu hell γ))
    (fun f => tauExt_gauge ell k Lu hell S γ f) y

/-- the bundled hypotheses of G6 (each field supplied by another lane / by G2, G4). -/
structure GenFormHyps (P : IngrBParams) (U' : PeriodicLinkConfiguration SU2g P.Lf)
    (γ : GaugeFn P.Lf) : Prop where
  base : BondEqv γ P.G P.U U' P.a P.sector ({ P with U := U' } : IngrBParams).sector P.Jf
    ({ P with U := U' } : IngrBParams).Jf
  D2 : ∀ B : BondFnL2 P.Lu, ({ P with U := U' } : IngrBParams).D2in (adBL (uOf P.ell P.k P.Lu P.hell γ) B) =
    adBL (uOf P.ell P.k P.Lu P.hell γ) (P.D2in B)

namespace GenFormHyps
variable {P : IngrBParams} {U' : PeriodicLinkConfiguration SU2g P.Lf} {γ : GaugeFn P.Lf}

theorem data (h : GenFormHyps P U' γ) :
    BaseEqv (adEL γ P.G) (adSL γ) (adFL γ P.G) P.data ({ P with U := U' } : IngrBParams).data :=
  h.base.baseEqv

theorem Nmat (h : GenFormHyps P U' γ) (f : FSp P.G) :
    GenP.Nmat ({ P with U := U' } : IngrBParams) (adFL γ P.G f) = adFL γ P.G (GenP.Nmat P f) :=
  h.data.QG1Qs P.G1inv_spec ({ P with U := U' } : IngrBParams).G1inv_spec f

theorem firstTerm (h : GenFormHyps P U' γ) (B : BondFnL2 P.Lu) :
    GenP.firstTerm ({ P with U := U' } : IngrBParams) (adBL (uOf P.ell P.k P.Lu P.hell γ) B) =
      GenP.firstTerm P B := by
  have hτ := tauExt_adjoint_gauge P.ell P.k P.Lu P.hell P.S γ B
  have hN := ringInverse_intertwine (adFL γ P.G).toContinuousLinearEquiv (fun f => h.Nmat f)
    (ContinuousLinearMap.adjoint P.tau B)
  unfold GenP.firstTerm
  show P.eta * ⟪ContinuousLinearMap.adjoint P.tau (adBL (uOf P.ell P.k P.Lu P.hell γ) B),
      Ring.inverse (GenP.Nmat ({ P with U := U' } : IngrBParams))
        (ContinuousLinearMap.adjoint P.tau (adBL (uOf P.ell P.k P.Lu P.hell γ) B))⟫ = _
  have hτ' : ContinuousLinearMap.adjoint P.tau (adBL (uOf P.ell P.k P.Lu P.hell γ) B) =
      (adFL γ P.G).toContinuousLinearEquiv (ContinuousLinearMap.adjoint P.tau B) := hτ
  rw [hτ', hN]
  exact congrArg (fun r => P.eta * r) ((adFL γ P.G).inner_map_map _ _)

theorem H1in (h : GenFormHyps P U' γ) (y : BondFnL2 P.Lu) :
    ({ P with U := U' } : IngrBParams).H1in (adBL (uOf P.ell P.k P.Lu P.hell γ) y) =
      adBL γ (P.H1in y) := by
  have hτ := tauExt_adjoint_gauge P.ell P.k P.Lu P.hell P.S γ y
  show iE P.G (({ P with U := U' } : IngrBParams).data.H1 ({ P with U := U' } : IngrBParams).G1inv
      (ContinuousLinearMap.adjoint P.tau (adBL (uOf P.ell P.k P.Lu P.hell γ) y))) =
    adBL γ (iE P.G (P.data.H1 P.G1inv (ContinuousLinearMap.adjoint P.tau y)))
  have hτ' : ContinuousLinearMap.adjoint P.tau (adBL (uOf P.ell P.k P.Lu P.hell γ) y) =
      adFL γ P.G (ContinuousLinearMap.adjoint P.tau y) := hτ
  rw [hτ', h.data.H1 P.G1inv_spec ({ P with U := U' } : IngrBParams).G1inv_spec, iE_adEL]

/-- **G6.** Conditional invariance of the genuine form (3.156). -/
theorem genForm (h : GenFormHyps P U' γ) (B : BondFnL2 P.Lu) :
    GenP.genForm ({ P with U := U' } : IngrBParams) (adBL (uOf P.ell P.k P.Lu P.hell γ) B) =
      GenP.genForm P B := by
  unfold GenP.genForm
  rw [h.firstTerm, h.D2, h.H1in, h.base.J]
  show GenP.firstTerm P B - P.a * ⟪adBL (uOf P.ell P.k P.Lu P.hell γ) B,
      adBL (uOf P.ell P.k P.Lu P.hell γ) B⟫ - 2 * ⟪adBL γ (P.H1in (P.D2in B)), adBL γ P.Jf⟫ = _
  rw [LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]

end GenFormHyps

/-- **G6, gauge form**: `U' = U^γ`, `P' = {P with U := U^γ}`, `D2in` supplied by G4 from the
pointwise `Q₁`/`C̃⁽²⁾` hypotheses. -/
theorem genForm_gauge (P : IngrBParams) (γ : GaugeFn P.Lf)
    (hbase : BondEqv γ P.G P.U (periodicGaugeTransform γ P.U) P.a P.sector
      ({ P with U := periodicGaugeTransform γ P.U } : IngrBParams).sector P.Jf
      ({ P with U := periodicGaugeTransform γ P.U } : IngrBParams).Jf)
    (hQ1 : ∀ B c, ({ P with U := periodicGaugeTransform γ P.U } : IngrBParams).Q1
      (gaugeActA (uOf P.ell P.k P.Lu P.hell γ) B) c =
        RMap (uOf P.ell P.k P.Lu P.hell γ c.1.1) (P.Q1 B c))
    (hC2 : ∀ B c, C2tilde P.ell ({ P with U := periodicGaugeTransform γ P.U } : IngrBParams).unitBgU
      (gaugeActA (uOf P.ell P.k P.Lu P.hell γ) B) c =
        RMap (uOf P.ell P.k P.Lu P.hell γ c.1.1) (C2tilde P.ell P.unitBgU B c))
    (B : BondFnL2 P.Lu) :
    GenP.genForm ({ P with U := periodicGaugeTransform γ P.U } : IngrBParams)
      (adBL (uOf P.ell P.k P.Lu P.hell γ) B) = GenP.genForm P B :=
  GenFormHyps.genForm ⟨hbase, fun B' => D2in_gauge P _ _ hQ1 hC2 B'⟩ B

#print axioms tauExt_gauge
#print axioms tauExt_adjoint_gauge
#print axioms GenFormHyps.Nmat
#print axioms GenFormHyps.firstTerm
#print axioms GenFormHyps.H1in
#print axioms GenFormHyps.genForm
#print axioms genForm_gauge

end AdalyFormal.GaugeCov
