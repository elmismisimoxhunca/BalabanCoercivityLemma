import TL15b
import ZXR2Wire1

/-!
# TL16a -- unit-lattice covers (reindexed to the fine deck group), `embY` compatibility, `tauExt` descends
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.IngredientFamilyR2

section reidx
variable {D D' Xt X : Type} [Fintype D] [Fintype D'] [Fintype Xt] [Fintype X]

/-- change the deck index type along an equivalence -/
def Cov.reindex (c : Cov D Xt X) (e : D' ≃ D) : Cov D' Xt X where
  π := c.π
  τ := fun d' => c.τ (e d')
  surj := c.surj
  π_τ := fun d' x => c.π_τ (e d') x
  free := fun x y hxy => by
    obtain ⟨d, hd, hu⟩ := c.free x y hxy
    refine ⟨e.symm d, by simpa using hd, fun d' hd' => ?_⟩
    have := hu (e d') hd'
    simpa using congrArg e.symm this

end reidx

section unit
variable {Lut Lu : PeriodicLatticeExtent} (hu : Covers Lut Lu) (ell k : ℕ)

theorem nn_scaleUp (hell : 0 < ell) (μ : Fin 3) :
    nn (scaleUp ell k Lut) (scaleUp ell k Lu) μ = nn Lut Lu μ := by
  unfold nn
  rw [scaleUp_add_one ell k hell, scaleUp_add_one ell k hell]
  exact Nat.mul_div_mul_right _ _ (pow_pos hell k)

/-- fine deck group ≃ unit deck group -/
def eUnit (hell : 0 < ell) : DeckIdx (scaleUp ell k Lut) (scaleUp ell k Lu) ≃ DeckIdx Lut Lu :=
  Equiv.piCongrRight (fun μ => finCongr (nn_scaleUp ell k hell μ))

theorem eUnit_val (hell : 0 < ell) (d : DeckIdx (scaleUp ell k Lut) (scaleUp ell k Lu)) (μ : Fin 3) :
    ((eUnit (Lut := Lut) (Lu := Lu) ell k hell d) μ).val = (d μ).val := rfl

theorem phiS_emb (hell : 0 < ell) (o : Fin 3 → ℕ) (y : PeriodicLatticeSite Lut) :
    phiS (covers_scaleUp ell k hell hu) (fun μ => ell ^ k * o μ) (embY ell k Lut hell y) =
      embY ell k Lu hell (phiS hu o y) := by
  funext μ
  apply Fin.ext
  show (ell ^ k * (y μ).val + ell ^ k * o μ) % (scaleUp ell k Lu μ + 1) = ell ^ k * (((y μ).val + o μ) % (Lu μ + 1))
  rw [scaleUp_add_one ell k hell, mul_comm (Lu μ + 1), ← Nat.mul_add, Nat.mul_mod_mul_left]

end unit

end AdalyFormal.Thin
