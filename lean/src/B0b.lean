import B0a
import R2RawX
import AdalyFormal.Balaban.RegularityGap

/-!
# B0b -- the level-`j` composite raw map on a pure-gauge fluctuation (exact, nonlinear, coordinates)

`gT ell bg γ j`: the gauge at level `j` (`gT 0 = γ`, `gT (j+1) = nextG (ell^j) ell (bg j) (gT j)`).
`aC ell bg γ j e = fromM2 (su2Log (pgV (ell^j) (bg j) (gT j) e))`: coordinates of the level-`j` pure-gauge fluctuation.

* `rawStep_tower`: on the genuine tower `bg = UbarTower su2LogExp ell U`, level `j` pure gauge ↦ level `j+1` pure gauge.
* `expCfgX_aC`: if no level-`j` fluctuation link equals `-1`, `exp(toM2 (aC j)) = pgV ... (gT j)` (exp∘log).
* `qCompX_aC`: if no fluctuation link equals `-1` at levels `< j`, `qCompX ell bg j (aC 0) = aC j`.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace AdalyFormal.SliceCoerc

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp M2 SU2 su2NegOne su2Log_antiHermitian
  su2Log_traceless)
open AdalyFormal.Balaban.CovariantOperators (suTwo mem_suTwo_iff)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower UbarTower_succ)

variable {L : PeriodicLatticeExtent}

/-- the gauge at level `j`. -/
noncomputable def gT (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L)
    (γ : PeriodicLatticeSite L → SU2) : ℕ → PeriodicLatticeSite L → SU2
  | 0 => γ
  | j + 1 => nextG (ell ^ j) ell (bg j) (gT ell bg γ j)

/-- coordinates of the level-`j` pure-gauge fluctuation. -/
noncomputable def aC (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L)
    (γ : PeriodicLatticeSite L → SU2) (j : ℕ) : XS L :=
  fun e => fromM2 (su2Log (pgV (ell ^ j) (bg j) (gT ell bg γ j) e))

theorem rawStep_tower (ell : ℕ) (U : PeriodicLinkConfiguration SU2 L)
    (γ : PeriodicLatticeSite L → SU2) (j : ℕ) (c : PeriodicLatticeEdge L) :
    rawStep (ell ^ j) ell (UbarTower su2LogExp ell U j)
        (pgV (ell ^ j) (UbarTower su2LogExp ell U j) (gT ell (UbarTower su2LogExp ell U) γ j)) c
      = pgV (ell ^ (j + 1)) (UbarTower su2LogExp ell U (j + 1))
          (gT ell (UbarTower su2LogExp ell U) γ (j + 1)) c := by
  rw [rawStep_pgV, UbarTower_succ, pow_succ]
  rfl

theorem expCfgX_aC (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L)
    (γ : PeriodicLatticeSite L → SU2) (j : ℕ)
    (hne : ∀ e, pgV (ell ^ j) (bg j) (gT ell bg γ j) e ≠ su2NegOne) :
    expCfgX (aC ell bg γ j) = pgV (ell ^ j) (bg j) (gT ell bg γ j) := by
  funext e
  have hmem : su2Log (pgV (ell ^ j) (bg j) (gT ell bg γ j) e) ∈ suTwo :=
    (mem_suTwo_iff _).mpr ⟨su2Log_antiHermitian _, su2Log_traceless _⟩
  simp only [expCfgX, aC]
  rw [toM2_fromM2 hmem]
  exact AdalyFormal.Balaban.RegularityGap.su2_exp_log_of_ne_negOne _ (hne e)

theorem qCompX_aC (ell : ℕ) (U : PeriodicLinkConfiguration SU2 L)
    (γ : PeriodicLatticeSite L → SU2) (j : ℕ)
    (hne : ∀ i, i < j → ∀ e, pgV (ell ^ i) (UbarTower su2LogExp ell U i)
      (gT ell (UbarTower su2LogExp ell U) γ i) e ≠ su2NegOne) :
    qCompX ell (UbarTower su2LogExp ell U) j (aC ell (UbarTower su2LogExp ell U) γ 0)
      = aC ell (UbarTower su2LogExp ell U) γ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [qCompX, Function.comp_apply, ih (fun i hi => hne i (by omega))]
      funext c
      simp only [qStepX]
      rw [expCfgX_aC ell _ γ j (hne j (by omega)), rawStep_tower]
      rfl

#print axioms rawStep_tower
#print axioms expCfgX_aC
#print axioms qCompX_aC

end AdalyFormal.SliceCoerc
