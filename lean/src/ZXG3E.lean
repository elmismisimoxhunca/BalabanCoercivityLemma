import ZXG3D3
import ZR2E
import ZMut

/-!
# G3E -- (a) the per-cube class excludes configurations on the closed-point tower;
(b) the ingredient lane's `toIngr` cannot be instantiated on a tower whose `𝔅` misses a unit bond
    (this is why `WellDef` uses the multi-level `Nmat` on `L²(𝔅)`);
(c) re-exports of the verifier's mutation controls (`Mut.lean`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace AdalyFormal.StatementLaneG

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

/-- (a) the fixed-factor (`c = 12`) per-cube class is RESTRICTIVE at the closed-point tower of every height `k` (r5; was `k = 0`, Mix class):
some `U` is excluded (holonomy `-1` plaquette) -/
theorem genuine_class_excludes_some_U (k : ℕ) {α₀ : ℝ} (hα : 0 < α₀)
    (hsmall : (12 : ℝ) * ((1 : ℕ) : ℝ) * α₀ ≤ 1 / 2) :
    ∃ U : LinkCfg (scaleUp 2 k L10),
      ¬ PerCubeRegular2 2 1 12 k (fullTower 2 k L10) α₀ (((2 : ℕ) : ℝ) ^ k)⁻¹ U := by
  have hN : ∀ μ, 1 ≤ scaleUp 2 k L10 μ := by
    intro μ
    have : 0 < (L10 μ + 1) * 2 ^ k := Nat.mul_pos (Nat.succ_pos _) (pow_pos (by norm_num) k)
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    simp only [scaleUp, L10]
    omega
  have hne : ((fullTower 2 k L10).Om 0).Nonempty :=
    ⟨fun _ => ⟨0, by simp [scaleUp, L10]⟩, by simp [fullTower]⟩
  exact coveredc_class_excludes_some_U hN (by norm_num) (by norm_num) (by norm_num) (fullTower 2 k L10)
    (Sk_coversc_scaleUp k 12 (by norm_num)) hne (by positivity) hα hsmall

/-- (b) if some unit bond is not (the embedding of) a bond of `𝔅` at level `k`, the ingredient lane's
top-level `Q G₁ Q*` (the `Ingr.QGQ_unit` carrier) is NOT a unit, whatever `G₁`: `toIngr`'s `hunit`
hypothesis is false.  [`Qin = τ ∘ Qfull`, `τ* y = 0` for `y` supported off the image.] -/
theorem toIngr_hunit_false (P : IngrBParams)
    (e : Bond P.Lu) (he : unitBondEmb P.ell P.k P.Lu P.hell e ∉ bondsLam P.G P.k) :
    ¬ IsUnit ((P.Qin.comp P.G1in).comp (ContinuousLinearMap.adjoint P.Qin)) := by
  classical
  intro hU
  let y : BondFnL2 P.Lu := WithLp.toLp 2 (Pi.single e suTwoWitness)
  have hy : y ≠ 0 := by
    intro h
    have := congrArg (fun z : BondFnL2 P.Lu => z.ofLp e) h
    simp [y] at this
    exact suTwoWitness_ne_zero this
  have htau : ContinuousLinearMap.adjoint P.tau y = 0 := by
    refine ext_inner_right ℝ (fun f => ?_)
    rw [inner_zero_left, ContinuousLinearMap.adjoint_inner_left]
    -- ⟨y, τ f⟩ = ⟨suTwoWitness, (τ f) e⟩ = 0
    have hτ : (WithLp.ofLp (P.tau f)) e = 0 := by
      show (if hb : unitBondEmb P.ell P.k P.Lu P.hell e ∈ bondsLam (geomOf P.ell P.k P.S) P.k
        then WithLp.ofLp f ⟨Fin.last P.k, ⟨unitBondEmb P.ell P.k P.Lu P.hell e, hb⟩⟩ else 0) = 0
      rw [dif_neg he]
    rw [PiLp.inner_apply, Finset.sum_eq_single e]
    · simp [y, hτ]
    · intro b _ hb
      simp [y, Pi.single_apply, hb]
    · intro h; exact absurd (Finset.mem_univ e) h
  have hQs : ContinuousLinearMap.adjoint P.Qin y = 0 := by
    have : P.Qin = P.tau.comp P.sector.Qfull := rfl
    rw [this, ContinuousLinearMap.adjoint_comp]
    show ContinuousLinearMap.adjoint P.sector.Qfull (ContinuousLinearMap.adjoint P.tau y) = 0
    rw [htau, map_zero]
  have hzero : ((P.Qin.comp P.G1in).comp (ContinuousLinearMap.adjoint P.Qin)) y = 0 := by
    show P.Qin (P.G1in (ContinuousLinearMap.adjoint P.Qin y)) = 0
    rw [hQs, map_zero, map_zero]
  exact hy ((ContinuousLinearMap.isUnit_iff_bijective.mp hU).1 (by rw [hzero, map_zero]))

#print axioms genuine_class_excludes_some_U
#print axioms toIngr_hunit_false
#check @Mut.q1_bad_power
#check @Mut.q1_bad_range
#check @Mut.J_signflip_fails
#check @Mut.J_etapower_fails
#check @Mut.toy2_ignoreC2_fails
#check @Mut.toy2_signflip_fails
#check @Mut.D2_linear_variant_violates_law
#print axioms Mut.q1_bad_power
#print axioms Mut.J_signflip_fails
#print axioms Mut.J_etapower_fails
#print axioms Mut.toy2_signflip_fails

end AdalyFormal.StatementLaneG
