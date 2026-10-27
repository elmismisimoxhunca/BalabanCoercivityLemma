import ZR8DataA

/-!
# ZR8Data -- r8 LOCALITY THEOREM for the repaired statement: every ingredient of `genForm`/`genC`/`WellDef` reads `U` only on the
bonds with both endpoints in `Ω₀`

Hypotheses (`LocHyp`): `S` admissible (`Admissible ell M R k S`), `1 ≤ k`, `2 ≤ ell`, room `17 ell ≤ R M`, `Λ` with `LambdaOK2`.
Two configurations `U, U'` that agree on every `BothIn Ω₀` bond.  Conclusions (each a kernel theorem below):
 * `QfullOf_congr`, `C2fullOf_congr_U`, `C2fullOf_congr_in`, `sector_congr` (bond sector, rows `j ≥ 1` read `U` within `2 rhoT j`);
 * `data_congr` : the whole base data `(Δ_π, T, T*, Q, Q*, Q*aQ, C^{(2)}_π, J)` of (3.122)-(3.128) is THE SAME;
 * `G1inv_congr`, `Qin_congr`, `G1in_congr`, `H1in_congr`, `Nmat_congr`, `firstTerm_congr`;
 * unit level: `unitBgU_agree` (on the unit sites within `5 ell` of `Λ`), `Q1_rows_congr`, `C2tilde_rows_congr` (rows `c ∈ Dset`),
   `H0_congr`, `Cop_congr`, `D2in_congr`;
 * `genForm_congr_outside` : `genForm_U(C_U B̃) = genForm_{U'}(C_{U'} B̃)`, `genC_congr`, `WellDef_congr`, `GuardsUnit_congr`,
   `WellDefG_congr`, `InstIneq_congr`, `InstAtWD_congr`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.StatementLaneR8

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp M2 SU2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_blockOf)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

variable {L : PeriodicLatticeExtent}

/-! ## 2. the base data and everything built on it -/

/-- the locality hypotheses (all on the tower/`Λ`, none on `U`). -/
structure LocHyp (ell M R k : ℕ) {Lu : PeriodicLatticeExtent} (S : Tower (scaleUp ell k Lu))
    (Lam : Set (PeriodicLatticeSite Lu)) : Prop where
  adm : Admissible ell M R k S
  hk : 1 ≤ k
  hell : 2 ≤ ell
  room : 17 * ell ≤ R * M
  lam : LambdaOK2 ell M R k S Lam

theorem BaseDataS_ext' {E S F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup S] [InnerProductSpace ℝ S] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (D D' : BaseDataS E S F) (h1 : D.Dpi = D'.Dpi) (h2 : D.T = D'.T) (h3 : D.Ts = D'.Ts) (h4 : D.Q = D'.Q)
    (h5 : D.Qs = D'.Qs) (h6 : D.Mass = D'.Mass) (h7 : D.C2 = D'.C2) (h8 : D.J = D'.J) : D = D' := by
  cases D; cases D'
  simp only at h1 h2 h3 h4 h5 h6 h7 h8
  subst h1 h2 h3 h4 h5 h6 h7 h8
  rfl

theorem data_congr (P : IngrBParams) {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (hell : 2 ≤ P.ell)
    (hroom : 17 * P.ell ≤ R * M) (U' : Cfg (scaleUp P.ell P.k P.Lu))
    (hUU : ∀ e : Bond (scaleUp P.ell P.k P.Lu), BothIn (P.S.Om 0) e → P.U e = U' e) :
    ({ P with U := U' } : IngrBParams).data = P.data := by
  have hJ := Jf_congr_outside P U' hUU
  have hsec := sector_congr hS hell hroom hUU
  have hD := DpiFull_congr hS hell hroom hUU P.a
  have hT := Tfull_congr hS hell hroom hUU
  have hC : ∀ A : ↥(bondSupp P.G), (bondSectorOf P.G U').C2full (Wop P.G U' P.a (iE P.G A))
      = (bondSectorOf P.G P.U).C2full (Wop P.G P.U P.a (iE P.G A)) := fun A => by
    rw [← hsec]
    exact C2fullOf_congr_in hS hell hroom P.U (fun e he => (Wop_congr_both hS hell hroom hUU P.a _ e he).symm)
  refine BaseDataS_ext' _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · show (pE P.G).comp ((DpiFull P.G U' P.a).comp (iE P.G)) = (pE P.G).comp ((DpiFull P.G P.U P.a).comp (iE P.G))
    rw [← hD]
  · show (Tfull P.G U').comp (iE P.G) = (Tfull P.G P.U).comp (iE P.G)
    rw [← hT]
  · show ContinuousLinearMap.adjoint ((Tfull P.G U').comp (iE P.G)) = ContinuousLinearMap.adjoint ((Tfull P.G P.U).comp (iE P.G))
    rw [← hT]
  · show (bondSectorOf P.G U').Qfull.comp (iE P.G) = (bondSectorOf P.G P.U).Qfull.comp (iE P.G)
    rw [← hsec]
  · show ContinuousLinearMap.adjoint ((bondSectorOf P.G U').Qfull.comp (iE P.G))
      = ContinuousLinearMap.adjoint ((bondSectorOf P.G P.U).Qfull.comp (iE P.G))
    rw [← hsec]
  · show (pE P.G).comp ((MassFull P.G P.a (bondSectorOf P.G U')).comp (iE P.G))
      = (pE P.G).comp ((MassFull P.G P.a (bondSectorOf P.G P.U)).comp (iE P.G))
    rw [← hsec]
  · show (fun A => (bondSectorOf P.G U').C2full (Wop P.G U' P.a (iE P.G A)))
      = (fun A => (bondSectorOf P.G P.U).C2full (Wop P.G P.U P.a (iE P.G A)))
    funext A; exact hC A
  · show pE P.G ({ P with U := U' } : IngrBParams).Jf = pE P.G P.Jf
    rw [hJ]

theorem G1inv_congr (P : IngrBParams) {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (hell : 2 ≤ P.ell)
    (hroom : 17 * P.ell ≤ R * M) (U' : Cfg (scaleUp P.ell P.k P.Lu))
    (hUU : ∀ e : Bond (scaleUp P.ell P.k P.Lu), BothIn (P.S.Om 0) e → P.U e = U' e) :
    ({ P with U := U' } : IngrBParams).G1inv = P.G1inv := by
  have hd := data_congr P hS hell hroom U' hUU
  have h1 := ({ P with U := U' } : IngrBParams).G1inv_spec
  rw [hd] at h1
  exact P.data.G1inv_unique h1 P.G1inv_spec

#print axioms data_congr
#print axioms G1inv_congr

end AdalyFormal.StatementLaneR8
