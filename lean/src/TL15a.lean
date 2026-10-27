import TL14b

/-!
# TL15a -- abstract descent of `BaseDataS`: `G⁻¹`, `G`, `H`, the form `K`
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.IngredientFamilyR2

section bd
variable {Dd : Type} [Fintype Dd]
variable {E Et S St F Ft : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup Et] [InnerProductSpace ℝ Et] [FiniteDimensional ℝ Et]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup St] [InnerProductSpace ℝ St] [FiniteDimensional ℝ St]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup Ft] [InnerProductSpace ℝ Ft] [FiniteDimensional ℝ Ft]

/-- the descent data linking two base data sets -/
structure BDLink (D : BaseDataS E S F) (Dt : BaseDataS Et St Ft) (cE : HCov Dd E Et) (cS : HCov Dd S St) (cF : HCov Dd F Ft) : Prop where
  dpi : HDesc cE cE D.Dpi Dt.Dpi
  t : HDesc cE cS D.T Dt.T
  q : HDesc cE cF D.Q Dt.Q
  mass : HDesc cE cE D.Mass Dt.Mass
  j : Dt.J = cE.ell D.J
  c2_ell : ∀ A, Dt.C2 (cE.ell A) = cF.ell (D.C2 A)
  c2_rho : ∀ d A, Dt.C2 (cE.rho d A) = cF.rho d (Dt.C2 A)

variable {D : BaseDataS E S F} {Dt : BaseDataS Et St Ft} {cE : HCov Dd E Et} {cS : HCov Dd S St} {cF : HCov Dd F Ft}

theorem BaseDataS.Ts_eq (D : BaseDataS E S F) : D.Ts = ContinuousLinearMap.adjoint D.T := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro s x
  rw [real_inner_comm, ← D.T_adj, real_inner_comm]

theorem BaseDataS.Qs_eq (D : BaseDataS E S F) : D.Qs = ContinuousLinearMap.adjoint D.Q := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro s x
  rw [real_inner_comm, ← D.Q_adj, real_inner_comm]

theorem BDLink.ts (hl : BDLink (Dd := Dd) D Dt cE cS cF) : HDesc cS cE D.Ts Dt.Ts := by
  rw [BaseDataS.Ts_eq, BaseDataS.Ts_eq]; exact hl.t.adjoint

theorem BDLink.qs (hl : BDLink (Dd := Dd) D Dt cE cS cF) : HDesc cF cE D.Qs Dt.Qs := by
  rw [BaseDataS.Qs_eq, BaseDataS.Qs_eq]; exact hl.q.adjoint

theorem BDLink.ginv (hl : BDLink (Dd := Dd) D Dt cE cS cF) : HDesc cE cE D.Ginv Dt.Ginv := by
  unfold BaseDataS.Ginv
  exact (hl.dpi.add ((hl.t.comp hl.ts))).add hl.mass

end bd

end AdalyFormal.Thin
