import R7Fork.ZGU1K

/-!
# GU1L -- CONTROLS that exercise the `η`-power at `U = 1` (k ≥ 1) and a proved BLINDNESS statement for the J-sign.
(a) the constant mode `B_c = (e ↦ c_{e.2})` is a ZERO of the genuine form at every `k`;
(b) the mutated first term `η' ⟨τ*B,N⁻¹τ*B⟩ - a‖B‖²` equals `(η' ell^k - 1) a ‖B_c‖²` there, so every
    `η'` with `η' ell^k ≠ 1` (e.g. `η²`, `1`, `η⁻¹` at `k = 1`) is refuted;
(c) at `U = 1` the source `J` vanishes (`Jf_flat`) so replacing `J ↦ -J` changes nothing: no flat theorem
    can exercise the J-sign.
Standard axioms only (see the #print axioms lines).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.GenuineU1

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.GenuineU1H (constBond hodge_converse)

/-- the first term of (3.156) with a mutated `η`-power `η'` -/
noncomputable def firstTermMut (P : IngrBParams) (η' : ℝ) (B : BondFnL2 P.Lu) : ℝ :=
  η' * ⟪ContinuousLinearMap.adjoint P.tau B, Ring.inverse (GenP.Nmat P) (ContinuousLinearMap.adjoint P.tau B)⟫

/-- `genForm` with mutated `η`-power and a signed source term -/
noncomputable def genFormMut (P : IngrBParams) (η' s : ℝ) (B : BondFnL2 P.Lu) : ℝ :=
  firstTermMut P η' B - P.a * ⟪B, B⟫ - 2 * s * ⟪P.H1in (P.D2in B), P.Jf⟫

theorem genFormMut_eq (P : IngrBParams) (B : BondFnL2 P.Lu) :
    genFormMut P P.eta 1 B = GenP.genForm P B := by
  unfold genFormMut firstTermMut GenP.genForm GenP.firstTerm; ring

/-- (c) the J-sign is invisible at flat `U` -/
theorem genForm_Jsign_blind_flat (P : IngrBParams) (hU : P.U = flatCfg) (η' : ℝ) (B : BondFnL2 P.Lu) :
    genFormMut P η' 1 B = genFormMut P η' (-1) B := by
  have hJ : P.Jf = 0 := Jf_flat P hU
  unfold genFormMut
  rw [hJ]; simp

/-- the constant-per-direction unit bond field -/
def Bconst (Lu : PeriodicLatticeExtent) (c : Fin 3 → SuTwo) : BondFnL2 Lu :=
  WithLp.toLp 2 (fun e : Bond Lu => c e.2)

namespace Gen
variable (P : IngrBParams)

/-- the form of `G₁⁻¹` is nonnegative (flat, full tower, `0 < a`) -/
theorem G1inv_nonneg (hFS : P.FullSupp) (hOm : P.G.Om0 = Set.univ) (hU : P.U = flatCfg) (ha : 0 < P.a) (x : ↥(bondSupp P.G)) :
    0 ≤ ⟪x, P.G1inv x⟫ := by
  have hpos : 0 < P.a * (P.ell : ℝ) ^ P.k := by
    have : (0 : ℝ) < P.ell := by exact_mod_cast P.hell
    positivity
  rw [G1inv_form P hFS hOm hU]
  have h3 := mul_nonneg hpos.le (sq_nonneg ‖P.data.Q x‖)
  have h1 := sq_nonneg ‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp P.ell P.k P.Lu)) (iE P.G x)‖
  have h2 := sq_nonneg ‖Tfull P.G P.U (iE P.G x)‖
  linarith

/-- **VARIATIONAL CHARACTERISATION** (flat, full tower, any `k`, `G₁⁻¹`/`N` units): for every fibre element
`A` with `Q_k A = τ*B`,  `genForm B ≤ η (‖curl A‖² + ‖R D* A‖²)`.  Together with `genForm_reduction`
(equality attained) this says `genForm B = η · min{ ‖curl A‖² + ‖R D* A‖² : Q_k A = τ*B }`. -/
theorem genForm_le_fibre (hFS : P.FullSupp) (hOm : P.G.Om0 = Set.univ) (hU : P.U = flatCfg) (hG : IsUnit P.G1inv)
    (hN : IsUnit (GenP.Nmat P)) (ha : 0 < P.a) (B : BondFnL2 P.Lu) (A : ↥(bondSupp P.G))
    (hA : P.data.Q A = ContinuousLinearMap.adjoint P.tau B) :
    GenP.genForm P B ≤ P.eta * (‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp P.ell P.k P.Lu)) (iE P.G A)‖ ^ 2 +
      ‖Tfull P.G P.U (iE P.G A)‖ ^ 2) := by
  set y := ContinuousLinearMap.adjoint P.tau B with hy
  set z := Ring.inverse (GenP.Nmat P) y with hz
  have hNz : GenP.Nmat P z = y := by
    have := Ring.mul_inverse_cancel _ hN
    exact ContinuousLinearMap.ext_iff.mp this y
  set A1 : ↥(bondSupp P.G) := P.data.G1 P.G1inv (P.data.Qs z) with hA1
  have hG1 : P.G1inv A1 = P.data.Qs z := by
    have := Ring.mul_inverse_cancel _ hG
    exact ContinuousLinearMap.ext_iff.mp this (P.data.Qs z)
  have hQA1 : P.data.Q A1 = y := by rw [← hNz]; rfl
  have hin1 : ⟪y, z⟫ = ⟪A1, P.G1inv A1⟫ := by rw [hG1, ← P.data.Q_adj, hQA1]
  set d : ↥(bondSupp P.G) := A - A1 with hd
  have hQd : P.data.Q d = 0 := by rw [hd, map_sub, hA, hQA1, sub_self]
  have horth : ⟪d, P.G1inv A1⟫ = 0 := by
    rw [hG1, ← P.data.Q_adj, hQd, inner_zero_left]
  have hsymm := P.G1inv_spec.symm
  have hexp : ⟪A, P.G1inv A⟫ = ⟪A1, P.G1inv A1⟫ + 2 * ⟪d, P.G1inv A1⟫ + ⟪d, P.G1inv d⟫ := by
    have hAd : A = A1 + d := by rw [hd]; abel
    rw [hAd, map_add, inner_add_left, inner_add_right, inner_add_right]
    have h5 : ⟪A1, P.G1inv d⟫ = ⟪d, P.G1inv A1⟫ := by
      rw [← hsymm A1 d, real_inner_comm]
    rw [h5]; ring
  have hle : ⟪A1, P.G1inv A1⟫ ≤ ⟪A, P.G1inv A⟫ := by
    have := G1inv_nonneg P hFS hOm hU ha d
    rw [horth] at hexp
    linarith
  have hJ : P.Jf = 0 := Jf_flat P hU
  have hη : P.eta * (P.ell : ℝ) ^ P.k = 1 := by
    unfold IngrBParams.eta
    have : (0 : ℝ) < P.ell := by exact_mod_cast P.hell
    field_simp
  have hnormy : ‖y‖ = ‖B‖ := tau_adj_norm P hFS B
  have hKA : ⟪A, P.G1inv A⟫ = ‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp P.ell P.k P.Lu)) (iE P.G A)‖ ^ 2 +
      ‖Tfull P.G P.U (iE P.G A)‖ ^ 2 + P.a * (P.ell : ℝ) ^ P.k * ‖B‖ ^ 2 := by
    rw [G1inv_form P hFS hOm hU, hA, hnormy]
  have hBB : ⟪B, B⟫ = ‖B‖ ^ 2 := real_inner_self_eq_norm_sq B
  unfold GenP.genForm GenP.firstTerm
  rw [hJ, inner_zero_right, mul_zero, sub_zero, hBB, ← hy, ← hz, hin1]
  have hpe : 0 ≤ P.eta := P.eta_pos.le
  have h4 := mul_le_mul_of_nonneg_left (hle.trans_eq hKA) hpe
  have e2 : P.eta * (P.a * (P.ell : ℝ) ^ P.k * ‖B‖ ^ 2) = P.a * ‖B‖ ^ 2 := by
    calc P.eta * (P.a * (P.ell : ℝ) ^ P.k * ‖B‖ ^ 2) = (P.eta * (P.ell : ℝ) ^ P.k) * (P.a * ‖B‖ ^ 2) := by ring
      _ = P.a * ‖B‖ ^ 2 := by rw [hη, one_mul]
  rw [mul_add, mul_add, e2] at h4
  linarith

/-- **THE EXACT STATEMENT** (flat `U`, full tower, any `k`, feasible): the genuine (3.156) is the attained
constrained minimum of the pulled-back quadratic form `η(‖curl A‖² + ‖R D* A‖²)` over the fibre `Q_k A = τ*B`. -/
theorem genForm_eq_min (hFS : P.FullSupp) (hOm : P.G.Om0 = Set.univ) (hU : P.U = flatCfg) (hG : IsUnit P.G1inv)
    (hN : IsUnit (GenP.Nmat P)) (ha : 0 < P.a) (B : BondFnL2 P.Lu) :
    ∃ A : ↥(bondSupp P.G), P.data.Q A = ContinuousLinearMap.adjoint P.tau B ∧
      GenP.genForm P B = P.eta * (‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
          (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp P.ell P.k P.Lu)) (iE P.G A)‖ ^ 2 +
        ‖Tfull P.G P.U (iE P.G A)‖ ^ 2) ∧
      ∀ A' : ↥(bondSupp P.G), P.data.Q A' = ContinuousLinearMap.adjoint P.tau B →
        GenP.genForm P B ≤ P.eta * (‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
          (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp P.ell P.k P.Lu)) (iE P.G A')‖ ^ 2 +
        ‖Tfull P.G P.U (iE P.G A')‖ ^ 2) := by
  obtain ⟨A, hQ, hform⟩ := genForm_reduction P hFS hOm hU hG hN B
  refine ⟨A, ?_, hform, fun A' hA' => genForm_le_fibre P hFS hOm hU hG hN ha B A' hA'⟩
  refine PiLp.ext (fun p => ?_)
  obtain ⟨e, rfl⟩ := (P.eqv hFS).surjective p
  rw [tau_adj_apply P hFS]
  exact hQ e

end Gen

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
  (Lam : Set (PeriodicLatticeSite Lu))
local notation "PP" => PK ell k Lu hell a Lam

/-- `τ* B_c = Q (const fine field)` -/
theorem constMode_Q (hN : ∀ μ, 1 ≤ Lu μ) (c : Fin 3 → SuTwo) :
    (PP).data.Q ⟨constBond (scaleUp ell k Lu) c, bondSupp_G ell k Lu _⟩
      = ContinuousLinearMap.adjoint (PP).tau (Bconst Lu c) := by
  have hFS : (PP).FullSupp := PK_fullSupp ell k Lu hell a Lam
  have hpos : 0 < ell ^ k := pow_pos hell k
  refine PiLp.ext (fun p => ?_)
  obtain ⟨e, rfl⟩ := ((PP).eqv hFS).surjective p
  rw [Gen.tau_adj_apply (PP) hFS]
  show ((PP).sector.Qfull (constBond (scaleUp ell k Lu) c)) ((PP).eqv hFS e) = _
  rw [Qfull_top ell k Lu hell a Lam]
  exact LCR_const (ell ^ k) hpos (scaleUp_tiling ell k Lu hell) c _ (embY_mem_CL ell k Lu hell e.1) e.2

/-- (a) the minimal value of the form on the constant fibre: `⟨τ*B_c, N⁻¹ τ*B_c⟩ = a ell^k ‖B_c‖²` -/
theorem constMode_firstTerm (hN : ∀ μ, 1 ≤ Lu μ) (ha : 0 < a) (c : Fin 3 → SuTwo) :
    ⟪ContinuousLinearMap.adjoint (PP).tau (Bconst Lu c),
        Ring.inverse (GenP.Nmat (PP)) (ContinuousLinearMap.adjoint (PP).tau (Bconst Lu c))⟫
      = a * (ell : ℝ) ^ k * ‖Bconst Lu c‖ ^ 2 := by
  have hFS : (PP).FullSupp := PK_fullSupp ell k Lu hell a Lam
  have hG := PK_isUnit_G1inv ell k Lu hell a Lam hN ha
  have hNu := PK_isUnit_Nmat ell k Lu hell a Lam hN ha
  set y := ContinuousLinearMap.adjoint (PP).tau (Bconst Lu c) with hy
  set z := Ring.inverse (GenP.Nmat (PP)) y with hz
  have hNz : GenP.Nmat (PP) z = y := by
    have := Ring.mul_inverse_cancel _ hNu
    exact ContinuousLinearMap.ext_iff.mp this y
  set Ast : ↥(bondSupp (PP).G) := (PP).data.G1 (PP).G1inv ((PP).data.Qs z) with hAst
  have hG1 : (PP).G1inv Ast = (PP).data.Qs z := by
    have := Ring.mul_inverse_cancel _ hG
    exact ContinuousLinearMap.ext_iff.mp this ((PP).data.Qs z)
  have hQA : (PP).data.Q Ast = y := by rw [← hNz]; rfl
  have hin : ⟪y, z⟫ = ⟪Ast, (PP).G1inv Ast⟫ := by
    rw [hG1, ← (PP).data.Q_adj, hQA]
  -- the constant competitor
  set A0 : ↥(bondSupp (PP).G) := ⟨constBond (scaleUp ell k Lu) c, bondSupp_G ell k Lu _⟩ with hA0
  have hQ0 : (PP).data.Q A0 = y := constMode_Q ell k Lu hell a Lam hN c
  have hnormy : ‖y‖ = ‖Bconst Lu c‖ := Gen.tau_adj_norm (PP) hFS _
  have hpos : 0 < a * (ell : ℝ) ^ k := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell
    positivity
  -- form of the competitor
  have hform0 : ⟪A0, (PP).G1inv A0⟫ = a * (ell : ℝ) ^ k * ‖Bconst Lu c‖ ^ 2 := by
    rw [Gen.G1inv_form (PP) hFS (PK_Om0_univ ell k Lu hell a Lam) rfl]
    obtain ⟨hc1, hc2, -⟩ := hodge_converse (L := scaleUp ell k Lu) c 0
    have e1 : curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) (iE (PP).G A0) = 0 := hc1
    have e2 : Tfull (PP).G (PP).U (iE (PP).G A0) = 0 := by
      show (Rproj (PP).G flatCfg) (gradAdj flatCfg (iE (PP).G A0)) = 0
      rw [show gradAdj flatCfg (iE (PP).G A0) = 0 from hc2, map_zero]
    show ‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) (iE (PP).G A0)‖ ^ 2 +
      ‖Tfull (PP).G (PP).U (iE (PP).G A0)‖ ^ 2 + a * (ell : ℝ) ^ k * ‖(PP).data.Q A0‖ ^ 2 = _
    rw [e1, e2, hQ0, hnormy]; simp
  -- lower bound: every form value on the fibre is ≥ a ell^k ‖y‖²
  have hlow : ∀ x : ↥(bondSupp (PP).G), 0 ≤ ⟪x, (PP).G1inv x⟫ := by
    intro x
    rw [Gen.G1inv_form (PP) hFS (PK_Om0_univ ell k Lu hell a Lam) rfl]
    have : (PP).a * ((PP).ell : ℝ) ^ (PP).k = a * (ell : ℝ) ^ k := rfl
    have h3 := mul_nonneg hpos.le (sq_nonneg ‖(PP).data.Q x‖)
    have h1 := sq_nonneg ‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) (iE (PP).G x)‖
    have h2 := sq_nonneg ‖Tfull (PP).G (PP).U (iE (PP).G x)‖
    show 0 ≤ ‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) (iE (PP).G x)‖ ^ 2 +
      ‖Tfull (PP).G (PP).U (iE (PP).G x)‖ ^ 2 + a * (ell : ℝ) ^ k * ‖(PP).data.Q x‖ ^ 2
    linarith
  have hlowA : a * (ell : ℝ) ^ k * ‖y‖ ^ 2 ≤ ⟪Ast, (PP).G1inv Ast⟫ := by
    rw [Gen.G1inv_form (PP) hFS (PK_Om0_univ ell k Lu hell a Lam) rfl]
    have h1 := sq_nonneg ‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) (iE (PP).G Ast)‖
    have h2 := sq_nonneg ‖Tfull (PP).G (PP).U (iE (PP).G Ast)‖
    show _ ≤ ‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) (iE (PP).G Ast)‖ ^ 2 +
      ‖Tfull (PP).G (PP).U (iE (PP).G Ast)‖ ^ 2 + a * (ell : ℝ) ^ k * ‖(PP).data.Q Ast‖ ^ 2
    rw [hQA]; linarith
  -- upper bound by orthogonality
  set d : ↥(bondSupp (PP).G) := A0 - Ast with hd
  have hQd : (PP).data.Q d = 0 := by rw [hd, map_sub, hQ0, hQA, sub_self]
  have horth : ⟪d, (PP).G1inv Ast⟫ = 0 := by
    rw [hG1, ← (PP).data.Q_adj, hQd, inner_zero_left]
  have hsymm := (PP).G1inv_spec.symm
  have hexp : ⟪A0, (PP).G1inv A0⟫ = ⟪Ast, (PP).G1inv Ast⟫ + 2 * ⟪d, (PP).G1inv Ast⟫ + ⟪d, (PP).G1inv d⟫ := by
    have hA0d : A0 = Ast + d := by rw [hd]; abel
    rw [hA0d, map_add, inner_add_left, inner_add_right, inner_add_right]
    have := hsymm d Ast
    rw [real_inner_comm] at this
    have h5 : ⟪Ast, (PP).G1inv d⟫ = ⟪d, (PP).G1inv Ast⟫ := by
      rw [← hsymm Ast d, real_inner_comm]
    rw [h5]; ring
  have hup : ⟪Ast, (PP).G1inv Ast⟫ ≤ a * (ell : ℝ) ^ k * ‖Bconst Lu c‖ ^ 2 := by
    have := hlow d
    rw [horth] at hexp
    linarith [hform0]
  have hlowA' : a * (ell : ℝ) ^ k * ‖Bconst Lu c‖ ^ 2 ≤ ⟪Ast, (PP).G1inv Ast⟫ := by
    rw [hnormy] at hlowA; exact hlowA
  linarith [hin]

end

#print axioms genFormMut_eq
#print axioms genForm_Jsign_blind_flat
#print axioms constMode_Q
#print axioms constMode_firstTerm
#print axioms Gen.G1inv_nonneg
#print axioms Gen.genForm_le_fibre
#print axioms Gen.genForm_eq_min

end AdalyFormal.GenuineU1
