import R7Fork.DM1b
import R7Fork.ZGU1N
import R7Fork.ZXG3H

/-!
# DM2a -- the genuine form (3.156) at flat `U`, ARBITRARY tower (`E_0` touching, `frakB` multi-stratum):
 (R) `genForm B = eta ( ||chi_{plaqIn Om0} curl A||^2 + ||T A||^2 + <A, Mass A> ) - a ||B||^2`   for the explicit candidate `A`, `Q A = tau* B`
     (generic `firstTerm_core`; needs only `IsUnit G1inv`, `IsUnit N`);
 (M) `a ell^k ||B||^2 <= <A, Mass A>` when `B` is supported on embedded `frakB`-bonds (only the level-`k` terms are used).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.DirichletMono

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GenuineU1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)

/-- (R): the reduction at flat `U` for an arbitrary tower -/
theorem genForm_reduction_gen (P : IngrBParams) (hU : P.U = flatCfg) (hG : IsUnit P.G1inv)
    (hN : IsUnit (GenP.Nmat P)) (B : BondFnL2 P.Lu) :
    ∃ A : ↥(bondSupp P.G), P.data.Q A = ContinuousLinearMap.adjoint P.tau B ∧
      GenP.genForm P B = P.eta * (‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn P.G.Om0)
          (curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
            (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp P.ell P.k P.Lu)) (iE P.G A))‖ ^ 2 +
          ‖Tfull P.G P.U (iE P.G A)‖ ^ 2 + ⟪A, P.data.Mass A⟫) - P.a * ‖B‖ ^ 2 := by
  obtain ⟨A, hQ, hin⟩ := Gen.firstTerm_core P hG hN (ContinuousLinearMap.adjoint P.tau B)
  refine ⟨A, hQ, ?_⟩
  have hJ : P.Jf = 0 := Jf_flat P hU
  have hJd : P.data.J = 0 := by
    show (pE P.G) P.Jf = 0
    rw [hJ]; exact map_zero _
  have hK := P.G1inv_spec.form A
  have hD : ⟪A, P.data.Dpi A⟫ = ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn P.G.Om0)
          (curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
            (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp P.ell P.k P.Lu)) (iE P.G A))‖ ^ 2 := by
    have : ⟪A, P.data.Dpi A⟫ = ⟪iE P.G A, DpiFull P.G P.U P.a (iE P.G A)⟫ := by
      show ⟪A, (pE P.G) (DpiFull P.G P.U P.a (iE P.G A))⟫ = _
      rw [pE_inner_right]
    rw [this, hU]
    exact inner_DpiFull_flat P.G P.a (iE P.G A)
  unfold GenP.genForm GenP.firstTerm
  rw [hJ, inner_zero_right, mul_zero, sub_zero, hin, hK]
  unfold BaseDataS.K
  rw [hJd, inner_zero_right, mul_zero, sub_zero, hD]
  have hBB : ⟪B, B⟫ = ‖B‖ ^ 2 := real_inner_self_eq_norm_sq B
  rw [hBB]
  have hT : P.data.T A = Tfull P.G P.U (iE P.G A) := rfl
  rw [hT]

#print axioms genForm_reduction_gen

/-- the mass form on `E_0` is the level-weighted sum over `frakB` -/
theorem mass_inner_gen (P : IngrBParams) (A : ↥(bondSupp P.G)) :
    ⟪A, P.data.Mass A⟫ = ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.data.Q A p‖ ^ 2 := by
  have h1 : ⟪A, P.data.Mass A⟫ = ⟪iE P.G A, MassFull P.G P.a P.sector (iE P.G A)⟫ := by
    show ⟪A, (pE P.G) ((MassFull P.G P.a P.sector) ((iE P.G) A))⟫ = _
    rw [pE_inner_right]
  rw [h1, inner_MassFull]
  rfl

/-- (M): if `Q A = tau* B` and `B` is supported on embedded `frakB`-bonds, `<A, Mass A> >= a ell^k ||B||^2` (`a >= 0`) -/
theorem mass_ge_gen (P : IngrBParams) (ha : 0 ≤ P.a) (A : ↥(bondSupp P.G)) (B : BondFnL2 P.Lu)
    (hQ : P.data.Q A = ContinuousLinearMap.adjoint P.tau B)
    (hB : ∀ e : Bond P.Lu, unitBondEmb P.ell P.k P.Lu P.hell e ∉ bondsLam P.G P.k → (WithLp.ofLp B) e = 0) :
    P.a * (P.ell : ℝ) ^ P.k * ‖B‖ ^ 2 ≤ ⟪A, P.data.Mass A⟫ := by
  classical
  rw [mass_inner_gen, hQ]
  set Es : Finset (Bond P.Lu) := Finset.univ.filter
    (fun e => unitBondEmb P.ell P.k P.Lu P.hell e ∈ bondsLam P.G P.k) with hEs
  have hmem : ∀ e : Es, unitBondEmb P.ell P.k P.Lu P.hell e.1 ∈ bondsLam P.G P.k :=
    fun e => (Finset.mem_filter.mp e.2).2
  set g : BIdx P.G → ℝ := fun p => P.a * (P.ell : ℝ) ^ (p.1 : ℕ) *
    ‖(ContinuousLinearMap.adjoint P.tau B) p‖ ^ 2 with hg
  have hnn : ∀ p, 0 ≤ g p := fun p => by
    have : 0 ≤ P.a * (P.ell : ℝ) ^ (p.1 : ℕ) := mul_nonneg ha (by positivity)
    exact mul_nonneg this (sq_nonneg _)
  set f : Es → BIdx P.G := fun e => pe P e.1 (hmem e) with hf
  have hfinj : Function.Injective f := fun e e' h =>
    Subtype.ext (pe_injective P e.1 e'.1 (hmem e) (hmem e') h)
  have h1 : (∑ e : Es, g (f e)) ≤ ∑ p : BIdx P.G, g p := by
    have himg : (∑ p ∈ (Finset.univ : Finset Es).image f, g p) = ∑ e : Es, g (f e) :=
      Finset.sum_image (fun a _ b _ h => hfinj h)
    rw [← himg]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun p _ _ => hnn p)
  have h2 : ∀ e : Es, g (f e) = P.a * (P.ell : ℝ) ^ P.k * ‖(WithLp.ofLp B) e.1‖ ^ 2 := by
    intro e
    have h0 : g (f e) = P.a * (P.ell : ℝ) ^ P.k *
        ‖(WithLp.ofLp (ContinuousLinearMap.adjoint P.tau B)) (pe P e.1 (hmem e))‖ ^ 2 := rfl
    rw [h0, tauAdj_apply P B e.1 (hmem e)]
  have h3 : (∑ e : Es, g (f e)) = P.a * (P.ell : ℝ) ^ P.k * ‖B‖ ^ 2 := by
    simp only [h2]
    rw [← Finset.mul_sum, PiLp.norm_sq_eq_of_L2]
    congr 1
    rw [Finset.sum_coe_sort Es (fun e => ‖(WithLp.ofLp B) e‖ ^ 2)]
    refine Finset.sum_subset (Finset.subset_univ _) (fun e _ he => ?_)
    have : (WithLp.ofLp B) e = 0 := hB e (fun h => he (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    simp [this]
  linarith [h1, h3]

#print axioms mass_ge_gen

end AdalyFormal.DirichletMono
