import GC3
import GCg1

/-!
# GCg2 -- the r7 `baseData` satisfies the six `BaseEqv` hypotheses, from BOND-LEVEL hypotheses
(`Wop`, `Delta`, `Tfull`, `Qfull`, `C2full`, `Jf`) with `AB = adBL γ`, `AS = adSL γ`, `AF = adFL γ G`,
`AE = adEL γ G`.  `DpiFull` is derived (adjoint-conjugation of `W`), `MassFull` is derived
(`diagW` has gauge-independent weights), `pE = iE*` is derived.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace AdalyFormal.GaugeCov
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.IngredientFamilyR2

/-- adjoints of intertwined operators are intertwined. -/
theorem adjoint_intertwine {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (AX : X ≃ₗᵢ[ℝ] X) (AY : Y ≃ₗᵢ[ℝ] Y) {M M' : X →L[ℝ] Y}
    (h : ∀ x, M' (AX x) = AY (M x)) (y : Y) :
    ContinuousLinearMap.adjoint M' (AY y) = AX (ContinuousLinearMap.adjoint M y) := by
  apply ext_inner_left ℝ
  intro v
  obtain ⟨x, rfl⟩ := AX.surjective v
  rw [ContinuousLinearMap.adjoint_inner_right, h, AY.inner_map_map, AX.inner_map_map,
    ContinuousLinearMap.adjoint_inner_right]

variable {L : PeriodicLatticeExtent}

/-- bond-level hypotheses of task G2. -/
structure BondEqv (γ : GaugeFn L) (G : TowerGeom L) (U U' : Cfg L) (a : ℝ)
    (S S' : BondSector G) (Jf Jf' : BondFnL2 L) : Prop where
  W : ∀ x, Wop G U' a (adBL γ x) = adBL γ (Wop G U a x)
  D : ∀ x, Delta G U' (adBL γ x) = adBL γ (Delta G U x)
  T : ∀ x, Tfull G U' (adBL γ x) = adSL γ (Tfull G U x)
  Q : ∀ x, S'.Qfull (adBL γ x) = adFL γ G (S.Qfull x)
  C : ∀ x, S'.C2full (adBL γ x) = adFL γ G (S.C2full x)
  J : Jf' = adBL γ Jf

theorem iE_adEL (γ : GaugeFn L) (G : TowerGeom L) (A : ↥(bondSupp G)) :
    iE G (adEL γ G A) = adBL γ (iE G A) := rfl

theorem pE_adBL (γ : GaugeFn L) (G : TowerGeom L) (y : BondFnL2 L) :
    pE G (adBL γ y) = adEL γ G (pE G y) :=
  adjoint_intertwine (adEL γ G) (adBL γ) (M := iE G) (M' := iE G) (fun x => iE_adEL γ G x) y

theorem diagW_adFL (γ : GaugeFn L) (G : TowerGeom L) (w : BIdx G → ℝ) (f : FSp G) :
    diagW G w (adFL γ G f) = adFL γ G (diagW G w f) := by
  refine PiLp.ext (fun p => ?_)
  simp only [diagW, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    WithLp.ofLp_toLp, PiLp.toLp_apply, adFL_apply]
  rw [map_smul]

namespace BondEqv
variable {γ : GaugeFn L} {G : TowerGeom L} {U U' : Cfg L} {a : ℝ} {S S' : BondSector G}
  {Jf Jf' : BondFnL2 L}

theorem Dpi (h : BondEqv γ G U U' a S S' Jf Jf') (x : BondFnL2 L) :
    DpiFull G U' a (adBL γ x) = adBL γ (DpiFull G U a x) := by
  simp only [DpiFull, ContinuousLinearMap.comp_apply, h.W, h.D]
  exact adjoint_intertwine (adBL γ) (adBL γ) (fun y => h.W y) _

theorem Mass (h : BondEqv γ G U U' a S S' Jf Jf') (x : BondFnL2 L) :
    MassFull G a S' (adBL γ x) = adBL γ (MassFull G a S x) := by
  simp only [MassFull, ContinuousLinearMap.comp_apply, h.Q, diagW_adFL]
  exact adjoint_intertwine (adBL γ) (adFL γ G) (fun y => h.Q y) _

/-- **G2**: the six `BaseEqv` hypotheses for the r7 `baseData`. -/
theorem baseEqv (h : BondEqv γ G U U' a S S' Jf Jf') :
    BaseEqv (adEL γ G) (adSL γ) (adFL γ G) (baseData G U a S Jf) (baseData G U' a S' Jf') where
  Dpi x := by
    show pE G (DpiFull G U' a (iE G (adEL γ G x))) = adEL γ G (pE G (DpiFull G U a (iE G x)))
    rw [iE_adEL, h.Dpi, pE_adBL]
  T x := by
    show Tfull G U' (iE G (adEL γ G x)) = adSL γ (Tfull G U (iE G x))
    rw [iE_adEL, h.T]
  Q x := by
    show S'.Qfull (iE G (adEL γ G x)) = adFL γ G (S.Qfull (iE G x))
    rw [iE_adEL, h.Q]
  Mass x := by
    show pE G (MassFull G a S' (iE G (adEL γ G x))) = adEL γ G (pE G (MassFull G a S (iE G x)))
    rw [iE_adEL, h.Mass, pE_adBL]
  C2 x := by
    show S'.C2full (Wop G U' a (iE G (adEL γ G x))) = adFL γ G (S.C2full (Wop G U a (iE G x)))
    rw [iE_adEL, h.W, h.C]
  J := by
    show pE G Jf' = adEL γ G (pE G Jf)
    rw [h.J, pE_adBL]

end BondEqv

#print axioms adjoint_intertwine
#print axioms pE_adBL
#print axioms diagW_adFL
#print axioms BondEqv.Dpi
#print axioms BondEqv.Mass
#print axioms BondEqv.baseEqv

end AdalyFormal.GaugeCov
