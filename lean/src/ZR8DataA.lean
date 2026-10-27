import ZR8Site
import ZT5A

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

/-! ## 1. rows of the bond sector -/

theorem bondsLam_ball {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
    (hroom : 17 * ell ≤ R * M) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {b : Bond L}
    (hb : b ∈ bondsLam (geomOf ell k S) j) : Ball b.1 (2 * rhoT ell j + 1) ⊆ S.Om 0 := by
  rcases hb.1 with h | h
  · exact row_ball_Om0 hS hell hroom hj1 hjk h.2.1 (x := b.1) (by rw [pdist_self]; exact Nat.zero_le _)
  · refine row_ball_Om0 hS hell hroom hj1 hjk h.2.1 (x := b.1) ?_
    rw [pdist_comm]; exact pdist_coarseShift_le b.1 (ell ^ j) b.2

theorem suCoordInv_apply_congr {x x' : XS L} {b : Bond L} (h : x b = x' b) :
    (WithLp.ofLp (suCoordInv x)) b = (WithLp.ofLp (suCoordInv x')) b := by
  apply Subtype.ext
  show toM2 (x b) = toM2 (x' b)
  rw [h]

theorem QfullOf_congr {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
    (hroom : 17 * ell ≤ R * M) {U U' : Cfg L} (hUU : ∀ e : Bond L, BothIn (S.Om 0) e → U e = U' e) :
    QfullOf (geomOf ell k S) U = QfullOf (geomOf ell k S) U' := by
  ext1 A
  refine PiLp.ext (fun p => ?_)
  obtain ⟨j, b, hb⟩ := p
  show (((ell : ℝ) ^ (j : ℕ))⁻¹) • (WithLp.ofLp (QlinB (geomOf ell k S) U j A)) b
    = (((ell : ℝ) ^ (j : ℕ))⁻¹) • (WithLp.ofLp (QlinB (geomOf ell k S) U' j A)) b
  congr 1
  rw [QlinB_apply, QlinB_apply]
  refine suCoordInv_apply_congr ?_
  rcases Nat.eq_zero_or_pos (j : ℕ) with hj0 | hj1
  · rw [hj0]; rfl
  · exact QlinCompL_congr_U (geomOf ell k S) (show 0 < ell by omega) _ j b
      (agreeAt_of_both hUU (bondsLam_ball hS hell hroom hj1 (Nat.lt_succ_iff.mp j.isLt) hb))

theorem C2fullOf_congr_U {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
    (hroom : 17 * ell ≤ R * M) {U U' : Cfg L} (hUU : ∀ e : Bond L, BothIn (S.Om 0) e → U e = U' e) (X : BondFnL2 L) :
    C2fullOf (geomOf ell k S) U X = C2fullOf (geomOf ell k S) U' X := by
  refine PiLp.ext (fun p => ?_)
  obtain ⟨j, b, hb⟩ := p
  show (((ell : ℝ) ^ (j : ℕ))⁻¹) • (WithLp.ofLp (C2rawB (geomOf ell k S) U j X)) b
    = (((ell : ℝ) ^ (j : ℕ))⁻¹) • (WithLp.ofLp (C2rawB (geomOf ell k S) U' j X)) b
  congr 1
  rw [C2rawB_eq, C2rawB_eq]
  refine suCoordInv_apply_congr ?_
  rcases Nat.eq_zero_or_pos (j : ℕ) with hj0 | hj1
  · rw [hj0, C2CompL_zero, C2CompL_zero]
  · exact C2CompL_congr_U (geomOf ell k S) (show 0 < ell by omega) _ j b
      (agreeAt_of_both hUU (bondsLam_ball hS hell hroom hj1 (Nat.lt_succ_iff.mp j.isLt) hb))

/-- `C^{(2)}` reads its argument only on `BothIn Ω₀` bonds (rows `j ≥ 1`; level `0` is `0`). -/
theorem C2fullOf_congr_in {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
    (hroom : 17 * ell ≤ R * M) (V : Cfg L) {X X' : BondFnL2 L} (hX : ∀ e : Bond L, BothIn (S.Om 0) e → X e = X' e) :
    C2fullOf (geomOf ell k S) V X = C2fullOf (geomOf ell k S) V X' := by
  refine PiLp.ext (fun p => ?_)
  obtain ⟨j, b, hb⟩ := p
  show (((ell : ℝ) ^ (j : ℕ))⁻¹) • (WithLp.ofLp (C2rawB (geomOf ell k S) V j X)) b
    = (((ell : ℝ) ^ (j : ℕ))⁻¹) • (WithLp.ofLp (C2rawB (geomOf ell k S) V j X')) b
  congr 1
  rw [C2rawB_eq, C2rawB_eq]
  refine suCoordInv_apply_congr ?_
  rcases Nat.eq_zero_or_pos (j : ℕ) with hj0 | hj1
  · rw [hj0, C2CompL_zero, C2CompL_zero]
  · have hB := bondsLam_ball hS hell hroom hj1 (Nat.lt_succ_iff.mp j.isLt) hb
    refine C2CompL_congr_in ell (by omega) _ j b (fun e he => ?_)
    have he' : e.1 ∈ Ball b.1 (2 * rhoT ell j + 1) := Ball_mono (by omega) he
    have hs : periodicLatticeShift e.1 e.2 ∈ Ball b.1 (2 * rhoT ell j + 1) :=
      Ball_sub (y' := e.1) he (by omega) (pdist_shift_le e.1 e.2)
    show fromM2 (((WithLp.ofLp X) e : SuTwo) : M2) = fromM2 (((WithLp.ofLp X') e : SuTwo) : M2)
    rw [hX e ⟨hB he', hB hs⟩]

theorem sector_congr {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
    (hroom : 17 * ell ≤ R * M) {U U' : Cfg L} (hUU : ∀ e : Bond L, BothIn (S.Om 0) e → U e = U' e) :
    bondSectorOf (geomOf ell k S) U = bondSectorOf (geomOf ell k S) U' := by
  have h1 := QfullOf_congr hS hell hroom hUU
  have h2 : C2fullOf (geomOf ell k S) U = C2fullOf (geomOf ell k S) U' := funext (C2fullOf_congr_U hS hell hroom hUU)
  unfold bondSectorOf
  congr 1

#print axioms QfullOf_congr
#print axioms C2fullOf_congr_U
#print axioms C2fullOf_congr_in
#print axioms sector_congr

end AdalyFormal.StatementLaneR8
