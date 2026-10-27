import NB10
/-!
# NB11 -- the corner (axial) gauge: link defects bounded by curvature (piece N2, part 2)

`γ_y(z) = V(Γ(y→z))` (holonomy along the tree's staircase).  In the gauge `γ_y`, the link at `(x, ρ)`
is the closed loop `γ_y(x) V(x,ρ) γ_y(x + s e_ρ)⁻¹`; it is `1` for `ρ = 0` and a conjugated strided
ladder for `ρ = 1, 2`, so (`axial_link`)

  `dv (γ_y(x) · V(x,ρ) · γ_y(x+s e_ρ)⁻¹) ≤ (off_0(x)/s + off_1(x)/s) · P`

whenever all offsets of `x` from `y` are multiples of `s`, `off_ρ(x) + s < N_ρ` (no wrap) and every
stride-`s` plaquette at an `s`-aligned site has defect `≤ P` (`y` aligned, `s ∣ N`).

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_mem_coarseLattice)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath coarsePathEndpoint coarsePathHolonomy)
open AdalyFormal.Balaban.QjComposite (coarsePathEndpoint_append coarsePathHolonomy_append)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)

variable {L : PeriodicLatticeExtent}

theorem finK_off (y x : PeriodicLatticeSite L) (σ : Fin 3) : finK (L σ) (off y x σ) = x σ - y σ := by
  apply Fin.ext
  show off y x σ % (L σ + 1) = _
  exact Nat.mod_eq_of_lt (off_lt y x σ)

theorem gamma_end (s : ℕ) (y x : PeriodicLatticeSite L) (h : ∀ σ, s ∣ off y x σ) :
    coarsePathEndpoint s y (coarseGammaPath s y x) = x := by
  rw [gamma_eq, coarsePathEndpoint_append, coarsePathEndpoint_append, endpoint_rep, endpoint_rep,
    endpoint_rep, Nat.mul_div_cancel' (h 2), Nat.mul_div_cancel' (h 1), Nat.mul_div_cancel' (h 0)]
  funext σ
  fin_cases σ
  · show (coarseShift _ (off y x 0) 0) 0 = x 0
    rw [shift_self, shift_ne _ _ (by decide : (0 : Fin 3) ≠ 1),
      shift_ne _ _ (by decide : (0 : Fin 3) ≠ 2), finK_off, add_sub_cancel]
  · show (coarseShift _ (off y x 0) 0) 1 = x 1
    rw [shift_ne _ _ (by decide : (1 : Fin 3) ≠ 0), shift_self,
      shift_ne _ _ (by decide : (1 : Fin 3) ≠ 2), finK_off, add_sub_cancel]
  · show (coarseShift _ (off y x 0) 0) 2 = x 2
    rw [shift_ne _ _ (by decide : (2 : Fin 3) ≠ 0), shift_ne _ _ (by decide : (2 : Fin 3) ≠ 1),
      shift_self, finK_off, add_sub_cancel]

/-- The corner gauge. -/
def cornerGauge (s : ℕ) (V : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L) :
    PeriodicLatticeSite L → SU2 := fun z => coarsePathHolonomy s V y (coarseGammaPath s y z)

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.gamma_end
