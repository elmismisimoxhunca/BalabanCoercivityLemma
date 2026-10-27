import TL16a

/-!
# TL16b -- the unit-level background, `Q₁` and `C̃⁽²⁾` are natural
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp SU2)
open AdalyFormal.IngredientFamilyR2

section ubg
variable {Lut Lu : PeriodicLatticeExtent} (hu : Covers Lut Lu) (ell k : ℕ) (hell : 0 < ell)

/-- the unit background of the pulled-back blocked fine background is the pull-back of the unit background -/
theorem unitBg_nat (o : Fin 3 → ℕ) (hp : PhiOK (covers_scaleUp ell k hell hu) (fun μ => ell ^ k * o μ) (ell ^ k))
    {Vt : PeriodicLinkConfiguration SU2 (scaleUp ell k Lut)} {V : PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)}
    (hV : AgreeAligned (covers_scaleUp ell k hell hu) (fun μ => ell ^ k * o μ) (ell ^ k) Vt V) :
    unitBg ell k Lut hell Vt = fun e => unitBg ell k Lu hell V (phiE hu o e) := by
  funext e
  show Vt (embY ell k Lut hell e.1, e.2) = V (embY ell k Lu hell (phiS hu o e.1), e.2)
  have hal : Aligned (ell ^ k) (embY ell k Lut hell e.1) := fun μ => by
    show ell ^ k ∣ ell ^ k * (e.1 μ).val
    exact Dvd.intro _ rfl
  rw [hV (embY ell k Lut hell e.1, e.2) hal]
  show V (phiS (covers_scaleUp ell k hell hu) (fun μ => ell ^ k * o μ) (embY ell k Lut hell e.1), e.2) = _
  rw [phiS_emb hu ell k hell o e.1]

end ubg

section q1
variable {Lut Lu : PeriodicLatticeExtent} {hu : Covers Lut Lu} {o : Fin 3 → ℕ} {ell : ℕ}

theorem coarse_aligned (y : PeriodicLatticeSite Lut) (hy : y ∈ CoarseLattice Lut ell) : Aligned ell y :=
  fun μ => Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp hy μ)

/-- coarse bond map induced by `phiS` -/
def cbMap (hp : PhiOK hu o ell) (c : CoarseBond Lut ell) : CoarseBond Lu ell :=
  (⟨phiS hu o c.1.1, mem_CoarseLattice.mpr (fun μ => Nat.mod_eq_zero_of_dvd
    (((aligned_phiS hp c.1.1).mpr (coarse_aligned c.1.1 c.1.2)) μ))⟩, c.2)

theorem Q1jet_nat (hp : PhiOK hu o ell) (hell : 0 < ell)
    {V0t : PeriodicLinkConfiguration SU2 Lut} {V0 : PeriodicLinkConfiguration SU2 Lu} (h0 : AgreeAligned hu o 1 V0t V0)
    (B : Bond Lu → SuTwo) (c : CoarseBond Lut ell)
    (hdiff : DifferentiableAt ℝ (qStepComp 1 ell V0t (c.1.1, c.2)) 0) :
    Q1jet ell V0t (fun e => B (phiE hu o e)) c = Q1jet ell V0 B (cbMap hp c) := by
  have hp1 : PhiOK hu o (1 * ell) := by simpa using hp
  show (ell : ℝ)⁻¹ • (suCoordFInv (QlinStepL 1 ell V0t (suCoordF (fun e => B (phiE hu o e))))) (c.1.1, c.2) =
    (ell : ℝ)⁻¹ • (suCoordFInv (QlinStepL 1 ell V0 (suCoordF B))) ((cbMap hp c).1.1, (cbMap hp c).2)
  congr 1
  have hrow := QlinStepL_row_nat hp1 Nat.one_pos hell h0 (c := (c.1.1, c.2)) (by simpa using coarse_aligned c.1.1 c.1.2)
    hdiff (suCoordF (fun e => B (phiE hu o e))) (suCoordF B) (fun e _ => rfl)
  show (suCoordFInv (QlinStepL 1 ell V0t (suCoordF (fun e => B (phiE hu o e))))) (c.1.1, c.2) = (suCoordFInv (QlinStepL 1 ell V0 (suCoordF B))) (phiE hu o (c.1.1, c.2))
  apply Subtype.ext
  show toM2 _ = toM2 _
  rw [hrow]

end q1

end AdalyFormal.Thin
