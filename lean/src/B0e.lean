import B0d

/-!
# B0e -- jets of the level gauges along the gauge curve `gLam t x = exp(t λ(x))`

`dG ell bg λ j y` (recursive): `dG 0 = λ`, `dG (j+1) y = (Σ_{x∈B_j(y)} ℓ⁻³ (dG j y - H dG j x Hᴴ))ᴴ + dG j y`,
`B_j(y) = stepBlockOf y (ell^j) ell`, `H = (bg j)(Γ_{y,x})` at stride `ell^j`.
`gT_jets`: for every level `j` and EVERY site `y`: `gT ell bg (gLam 0) j y = 1` and
`d/dt (gT ell bg (gLam t) j y : M2)|₀ = dG ell bg λ j y`.  No lattice, divisibility or smallness hypothesis.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.SliceCoerc

open scoped Matrix Matrix.Norms.Frobenius
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp M2 SU2 su2Exp_zero)
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwo mem_suTwo_iff)
open AdalyFormal.Balaban.SmoothLog (exp_hasFDerivAt_zero su2Exp_coe_of_mem_suTwo)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)

variable {L : PeriodicLatticeExtent}

/-- the gauge curve `t ↦ exp(t λ)`. -/
noncomputable def gLam (lam : PeriodicLatticeSite L → SuTwo) (t : ℝ) : PeriodicLatticeSite L → SU2 :=
  fun x => su2Exp (t • ((lam x : SuTwo) : M2))

/-- recursive jets of the level gauges. -/
noncomputable def dG (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L)
    (lam : PeriodicLatticeSite L → SuTwo) : ℕ → PeriodicLatticeSite L → M2
  | 0 => fun x => ((lam x : SuTwo) : M2)
  | j + 1 => fun y =>
      (∑ x ∈ stepBlockOf y (ell ^ j) ell, ((ell : ℝ) ^ 3)⁻¹ •
        (dG ell bg lam j y - ((coarsePathHolonomy (ell ^ j) (bg j) y (coarseGammaPath (ell ^ j) y x) : SU2) : M2)
          * dG ell bg lam j x
          * ((coarsePathHolonomy (ell ^ j) (bg j) y (coarseGammaPath (ell ^ j) y x) : SU2) : M2)ᴴ))ᴴ
      + dG ell bg lam j y

theorem gT_jets (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L)
    (lam : PeriodicLatticeSite L → SuTwo) (j : ℕ) :
    (∀ y, gT ell bg (gLam lam 0) j y = 1) ∧
      ∀ y, HasDerivAt (fun t => (gT ell bg (gLam lam t) j y : M2)) (dG ell bg lam j y) 0 := by
  induction j with
  | zero =>
      refine ⟨fun y => ?_, fun y => ?_⟩
      · show su2Exp ((0 : ℝ) • _) = 1
        rw [zero_smul, su2Exp_zero]
      · have hm := (mem_suTwo_iff _).mp (lam y).2
        have hfun : (fun t : ℝ => (gT ell bg (gLam lam t) 0 y : M2))
            = fun t => NormedSpace.exp (t • ((lam y : SuTwo) : M2)) := by
          funext t
          show ((su2Exp (t • ((lam y : SuTwo) : M2)) : SU2) : M2) = _
          rw [su2Exp_coe_of_mem_suTwo]
          · rw [Matrix.conjTranspose_smul, hm.1, smul_neg]; simp
          · rw [Matrix.trace_smul, hm.2, smul_zero]
        rw [hfun]
        have h1 : HasDerivAt (fun t : ℝ => t • ((lam y : SuTwo) : M2)) ((lam y : SuTwo) : M2) 0 := by
          have := (hasDerivAt_id (0 : ℝ)).smul_const ((lam y : SuTwo) : M2)
          simp only [one_smul] at this
          exact this
        exact exp_hasFDerivAt_zero.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
  | succ j ih =>
      obtain ⟨h0, hd⟩ := ih
      have hah : ∀ x, (dG ell bg lam j x)ᴴ = -dG ell bg lam j x := fun x =>
        antiHerm_of_hasDerivAt (fun t => gT ell bg (gLam lam t) j x) _ (hd x) (h0 x)
      refine ⟨fun y => ?_, fun y => ?_⟩
      · show (su2Exp (sBlock (ell ^ j) ell (bg j) (pgV (ell ^ j) (bg j) (gT ell bg (gLam lam 0) j)) y))⁻¹
            * gT ell bg (gLam lam 0) j y = 1
        rw [sBlock_zero _ _ _ _ y (h0 y) (fun x _ => h0 x), su2Exp_zero, inv_one, one_mul, h0 y]
      · exact hasDerivAt_nextG (ell ^ j) ell (bg j) (fun t => gT ell bg (gLam lam t) j) (dG ell bg lam j) y
          (h0 y) (fun x _ => h0 x) (hd y) (fun x _ => hd x) (fun x _ => hah x)

#print axioms gT_jets

end AdalyFormal.SliceCoerc
