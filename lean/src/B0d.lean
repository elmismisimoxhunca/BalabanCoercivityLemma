import B0c

/-!
# B0d -- jet of the coarse gauge `nextG` (one level)

* `sBlock_mem`: `sBlock s ell V V1 y ∈ su(2)` (a ℚ-weighted sum of principal logs).
* `sBlock_zero`: `sBlock s ell V (pgV s V γ) y = 0` when `γ = 1` at `y` and on the block.
* `hasDerivAt_sBlock`: `d/dt sBlock s ell V (pgV s V (γ t)) y |₀ = Σ_{x∈B} ℓ⁻³ (ν y - H_x ν x H_xᴴ)`.
* `hasDerivAt_nextG`: `d/dt (nextG s ell V (γ t) y : M2) |₀ = (Σ_{x∈B} ℓ⁻³ (ν y - H_x ν x H_xᴴ))ᴴ + ν y`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.SliceCoerc

open scoped Matrix Matrix.Norms.Frobenius
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp M2 SU2 su2Log_one su2Exp_zero
  su2Log_antiHermitian su2Log_traceless mul_star_self star_mul_self)
open AdalyFormal.Balaban.CovariantOperators (suTwo mem_suTwo_iff)
open AdalyFormal.Balaban.SmoothLog (exp_hasFDerivAt_zero su2Exp_coe_of_mem_suTwo)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)

variable {L : PeriodicLatticeExtent}

theorem sBlock_mem (s ell : ℕ) (V V1 : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L) :
    sBlock s ell V V1 y ∈ suTwo := by
  unfold sBlock
  refine Submodule.sum_mem _ (fun x _ => ?_)
  rw [← Rat.cast_smul_eq_qsmul ℝ]
  exact Submodule.smul_mem _ _ ((mem_suTwo_iff _).mpr ⟨su2Log_antiHermitian _, su2Log_traceless _⟩)

theorem sBlock_zero (s ell : ℕ) (V : PeriodicLinkConfiguration SU2 L) (γ : PeriodicLatticeSite L → SU2)
    (y : PeriodicLatticeSite L) (hy : γ y = 1) (hB : ∀ x ∈ stepBlockOf y s ell, γ x = 1) :
    sBlock s ell V (pgV s V γ) y = 0 := by
  unfold sBlock
  refine Finset.sum_eq_zero (fun x hx => ?_)
  rw [rProd_pgV s ell V γ y x hx, hy, hB x hx]
  simp

theorem hasDerivAt_sBlock (s ell : ℕ) (V : PeriodicLinkConfiguration SU2 L)
    (γ : ℝ → PeriodicLatticeSite L → SU2) (ν : PeriodicLatticeSite L → M2) (y : PeriodicLatticeSite L)
    (h0y : γ 0 y = 1) (h0B : ∀ x ∈ stepBlockOf y s ell, γ 0 x = 1)
    (hdy : HasDerivAt (fun t => (γ t y : M2)) (ν y) 0)
    (hdB : ∀ x ∈ stepBlockOf y s ell, HasDerivAt (fun t => (γ t x : M2)) (ν x) 0)
    (hah : ∀ x ∈ stepBlockOf y s ell, (ν x)ᴴ = -ν x) :
    HasDerivAt (fun t => sBlock s ell V (pgV s V (γ t)) y)
      (∑ x ∈ stepBlockOf y s ell, ((ell : ℝ) ^ 3)⁻¹ •
        (ν y - ((coarsePathHolonomy s V y (coarseGammaPath s y x) : SU2) : M2) * ν x
          * ((coarsePathHolonomy s V y (coarseGammaPath s y x) : SU2) : M2)ᴴ)) 0 := by
  have hfun : (fun t => sBlock s ell V (pgV s V (γ t)) y) = fun t =>
      ∑ x ∈ stepBlockOf y s ell, ((ell : ℝ) ^ 3)⁻¹ •
        su2Log (rProd s V (pgV s V (γ t)) y (coarseGammaPath s y x)) := by
    funext t
    unfold sBlock
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Rat.cast_smul_eq_qsmul ℝ]
    push_cast
    rfl
  rw [hfun]
  refine HasDerivAt.fun_sum (fun x hx => ?_)
  exact (hasDerivAt_logLoop s ell V γ ν y x hx h0y (h0B x hx) hdy (hdB x hx) (hah x hx)).const_smul
    ((ell : ℝ) ^ 3)⁻¹

theorem hasDerivAt_nextG (s ell : ℕ) (V : PeriodicLinkConfiguration SU2 L)
    (γ : ℝ → PeriodicLatticeSite L → SU2) (ν : PeriodicLatticeSite L → M2) (y : PeriodicLatticeSite L)
    (h0y : γ 0 y = 1) (h0B : ∀ x ∈ stepBlockOf y s ell, γ 0 x = 1)
    (hdy : HasDerivAt (fun t => (γ t y : M2)) (ν y) 0)
    (hdB : ∀ x ∈ stepBlockOf y s ell, HasDerivAt (fun t => (γ t x : M2)) (ν x) 0)
    (hah : ∀ x ∈ stepBlockOf y s ell, (ν x)ᴴ = -ν x) :
    HasDerivAt (fun t => (nextG s ell V (γ t) y : M2))
      ((∑ x ∈ stepBlockOf y s ell, ((ell : ℝ) ^ 3)⁻¹ •
        (ν y - ((coarsePathHolonomy s V y (coarseGammaPath s y x) : SU2) : M2) * ν x
          * ((coarsePathHolonomy s V y (coarseGammaPath s y x) : SU2) : M2)ᴴ))ᴴ + ν y) 0 := by
  set S : ℝ → M2 := fun t => sBlock s ell V (pgV s V (γ t)) y with hSdef
  have hS := hasDerivAt_sBlock s ell V γ ν y h0y h0B hdy hdB hah
  have hS0 : S 0 = 0 := sBlock_zero s ell V (γ 0) y h0y h0B
  have hexp : HasDerivAt (fun t => NormedSpace.exp (S t)) _ 0 :=
    exp_hasFDerivAt_zero.comp_hasDerivAt_of_eq (0 : ℝ) hS hS0.symm
  have hstar := hexp.star
  have hprod := hstar.fun_mul hdy
  have hfun : (fun t => (nextG s ell V (γ t) y : M2))
      = fun t => star (NormedSpace.exp (S t)) * (γ t y : M2) := by
    funext t
    have hm := (mem_suTwo_iff _).mp (sBlock_mem s ell V (pgV s V (γ t)) y)
    show (((su2Exp (S t))⁻¹ * γ t y : SU2) : M2) = _
    rw [Submonoid.coe_mul, AdalyFormal.Balaban.SuTwoLogExp.coe_inv,
      su2Exp_coe_of_mem_suTwo hm.1 hm.2, Matrix.star_eq_conjTranspose]
  rw [hfun]
  refine hprod.congr_deriv ?_
  rw [hS0, h0y, NormedSpace.exp_zero]
  simp only [ContinuousLinearEquiv.coe_refl, OneMemClass.coe_one, star_one,
    mul_one, one_mul, Matrix.star_eq_conjTranspose]
  rfl

#print axioms sBlock_mem
#print axioms sBlock_zero
#print axioms hasDerivAt_sBlock
#print axioms hasDerivAt_nextG

end AdalyFormal.SliceCoerc
