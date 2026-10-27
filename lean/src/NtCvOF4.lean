import NtCvOF3
import NtCvOH5

/-!
# CvOF4 -- the nested family `Pn`, and `G1inv x = Qs v` for the chain saddle (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG (gparams)

/-- the genuine parameters of the nested staggered family. -/
noncomputable abbrev Pn (ell M R : ℕ) (hell : 0 < ell) (a t : ℝ) : IngrBParams :=
  gparams ell 2 (neLu M R) hell (neS ell M R) (stagU ell M R t) a (neLam M R)

theorem zfield_congr {L : PeriodicLatticeExtent} {g1 g2 : ℕ → ℝ} (h : ∀ v, v ≤ L 0 → g1 v = g2 v) :
    (zfield g1 : BondFnL2 L) = zfield g2 := by
  refine PiLp.ext (fun b => ?_)
  show zfun g1 b = zfun g2 b
  unfold zfun
  split_ifs
  · rw [h _ (by have := (b.1 0).isLt; omega)]
  · rfl

variable {ell M R : ℕ}

theorem Wt_outside (hg : NGeo ell M R) {v : ℕ} (hv : ¬ (neP0 ell M R ≤ v ∧ v < neQ0 ell M R)) (ρ : ℕ → ℕ → ℝ) :
    Wt ell (isRowN ell M R) ρ v = 0 := by
  classical
  unfold Wt
  refine Finset.sum_eq_zero (fun j hj => ?_)
  have hj2 : j ≤ 2 := by have := Finset.mem_range.mp hj; omega
  rw [if_neg (fun h => hv (hrowJ_nested hg hj2 v h))]; ring

end AdalyFormal.CoverOmega

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (scaleUp)

variable {ell M R : ℕ}

theorem fe_supp {n : ℕ} (P0 : ℕ) (e : Fin n → ℝ) {v : ℕ} (hv : ¬ (P0 ≤ v ∧ v < P0 + n)) : fe P0 e v = 0 := by
  by_cases h1 : v < P0
  · exact fe_lt _ e h1
  · exact fe_ge _ e (by omega)

theorem zfield_fe_mem (hg : NGeo ell M R) (hell3 : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (e : Fin (nN ell M R) → ℝ) :
    (zfield (fe (neP0 ell M R) e) : BondFnL2 (scaleUp ell 2 (neLu M R))) ∈ bondSupp (geomOf ell 2 (neS ell M R)) := by
  refine zfield_mem_bondSupp _ (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) ?_ _ ?_
  · ext x; simp only [geomOf, Set.mem_setOf_eq]; exact neS_om0 x
  · intro v _ hv
    apply fe_supp
    unfold nN; intro h; apply hv; omega

theorem nested_G1inv_eq (hell3 : 3 ≤ ell) (hE : StagOK ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ) (htπ : |t| < tcap ell)
    (e : Fin (nN ell M R) → ℝ)
    (hrad : ∀ d : Fin (nN ell M R) → ℝ, d ∈ Vsub (rowOfN ell M R) → BF (neC ell M R - neP0 ell M R) (Real.cos t) e d = 0)
    (hf : (zfield (fe (neP0 ell M R) e) : BondFnL2 (scaleUp ell 2 (neLu M R))) ∈ bondSupp (geomOf ell 2 (neS ell M R)))
    (hv : (zfield (Wt ell (isRowN ell M R) (rhoV ell M R (neC ell M R - neP0 ell M R) (Real.cos t) a e)) : BondFnL2 (scaleUp ell 2 (neLu M R))) ∈
      bondSupp (geomOf ell 2 (neS ell M R))) :
    (((Pn ell M R (by omega) a t).G1inv ⟨zfield (fe (neP0 ell M R) e), hf⟩ : ↥(bondSupp (Pn ell M R (by omega) a t).G)) : BondFnL2 (scaleUp ell 2 (neLu M R))) =
      zfield (Wt ell (isRowN ell M R) (rhoV ell M R (neC ell M R - neP0 ell M R) (Real.cos t) a e)) := by
  have hg := nGeo hell3 hdvd hM hR
  have hell : 0 < ell := by omega
  have S := nested_stagSetup hell3 hE hdvd hM hR
  set P := Pn ell M R hell a t with hP
  have hcart : CartanCfg P.U := stagU_cartan ell M R t
  have hC : ∀ A : BondFnL2 P.Lf, SigB (WithLp.ofLp A) → P.sector.C2full A = 0 := fun A hA =>
    C2fullOf_sig S.hN S.hE S.hell (neC ell M R) t htπ S.hc1 S.hc2 P.G S.hG S.hk A hA
  set x : ↥(bondSupp P.G) := ⟨zfield (fe (neP0 ell M R) e), hf⟩ with hx
  have hxs : SigB (WithLp.ofLp (x : BondFnL2 P.Lf)) := fun b => zfun_diag _ b
  have hD2 := Delta2_sig P hcart hC x hxs
  have hG1 : P.G1inv = P.data.Ginv - P.data.Delta2 P.data_laws :=
    P.data.G1inv_unique P.G1inv_spec (P.data.isG1inv_sub P.data_laws)
  have h1 : P.G1inv x = P.data.Ginv x := by
    rw [hG1]; simp [hD2]
  rw [h1]
  have h2 := Ginv_zfield (ell := ell) (c := neC ell M R) t P.U rfl (G := P.G) (isRow := isRowN ell M R) S
    (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) (by ext y; simp only [IngrBParams.G, geomOf, Set.mem_setOf_eq]; exact neS_om0 y)
    (fun j hj v h => hrowJ_nested hg hj v h) htπ a P.Jf (fe (neP0 ell M R) e) hf
  refine h2.trans (zfield_congr (fun v hv => ?_))
  exact ginv_eq_Wt hell3 hdvd hM hR t a e hrad v hv

#print axioms nested_G1inv_eq

end AdalyFormal.CoverOmega
