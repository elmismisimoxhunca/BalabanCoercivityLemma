import TL18b

/-!
# TL15c -- `G₁`, `H₁`, and `Q G₁ Q*` descend
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.IngredientFamilyR2

section g1
variable {Dd : Type} [Fintype Dd]
variable {E Et S St F Ft : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup Et] [InnerProductSpace ℝ Et] [FiniteDimensional ℝ Et]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup St] [InnerProductSpace ℝ St] [FiniteDimensional ℝ St]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup Ft] [InnerProductSpace ℝ Ft] [FiniteDimensional ℝ Ft]
variable {D : BaseDataS E S F} {Dt : BaseDataS Et St Ft} {cE : HCov Dd E Et} {cS : HCov Dd S St} {cF : HCov Dd F Ft}

theorem BDLink.G1 [Nonempty Dd] (_hl : BDLink (Dd := Dd) D Dt cE cS cF) {X : E →L[ℝ] E} {Xt : Et →L[ℝ] Et} (hX : HDesc cE cE X Xt) (hu : IsUnit Xt) :
    IsUnit X ∧ HDesc cE cE (D.G1 X) (Dt.G1 Xt) := hX.inverse hu

theorem BDLink.Nmat [Nonempty Dd] (hl : BDLink (Dd := Dd) D Dt cE cS cF) {X : E →L[ℝ] E} {Xt : Et →L[ℝ] Et}
    (hX : HDesc cE cE X Xt) (hu : IsUnit Xt) :
    HDesc cF cF ((D.Q.comp (D.G1 X)).comp D.Qs) ((Dt.Q.comp (Dt.G1 Xt)).comp Dt.Qs) :=
  (hl.qs.comp (hl.G1 hX hu).2).comp hl.q

theorem BDLink.H1 [Nonempty Dd] (hl : BDLink (Dd := Dd) D Dt cE cS cF) {X : E →L[ℝ] E} {Xt : Et →L[ℝ] Et}
    (hX : HDesc cE cE X Xt) (hu : IsUnit Xt) (hM : IsUnit ((Dt.Q.comp (Dt.G1 Xt)).comp Dt.Qs)) :
    HDesc cF cE (D.H1 X) (Dt.H1 Xt) := by
  unfold BaseDataS.H1
  exact (((hl.Nmat hX hu).inverse hM).2.comp hl.qs).comp (hl.G1 hX hu).2

end g1

end AdalyFormal.Thin
