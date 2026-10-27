import TL11b

/-!
# TL11c -- the level-`j` first-order jet `QlinCompL` is natural at `ell^j`-aligned bonds
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open scoped Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp SU2 M2)
open AdalyFormal.IngredientFamilyR2

section comp
variable {Lt L : PeriodicLatticeExtent} {h : Covers Lt L} {o : Fin 3 → ℕ} {ell : ℕ}

theorem QlinCompL_nat (hell : 0 < ell) (bgt : ℕ → PeriodicLinkConfiguration SU2 Lt) (bg : ℕ → PeriodicLinkConfiguration SU2 L) :
    ∀ j : ℕ, PhiOK h o (ell ^ j) →
      (∀ l, l < j → AgreeAligned h o (ell ^ l) (bgt l) (bg l)) →
      (∀ l, l < j → ∀ c : PeriodicLatticeEdge Lt, Aligned (ell ^ (l + 1)) c.1 →
        DifferentiableAt ℝ (qStepComp (ell ^ l) ell (bgt l) c) 0) →
      ∀ (a : XS L) (e : PeriodicLatticeEdge Lt), Aligned (ell ^ j) e.1 →
        QlinCompL ell bgt j (ellX h o a) e = QlinCompL ell bg j a (phiE h o e) := by
  intro j
  induction j with
  | zero => intro _ _ _ a e _; rfl
  | succ j ih =>
    intro hp hbg hdiff a e he
    have hpos : 0 < ell ^ j := pow_pos hell j
    have hp' : PhiOK h o (ell ^ j * ell) := by rw [← pow_succ]; exact hp
    have he' : Aligned (ell ^ j * ell) e.1 := by rw [← pow_succ]; exact he
    have hpj : PhiOK h o (ell ^ j) := hp.mono (pow_dvd_pow ell (Nat.le_succ j))
    have ih' := ih hpj (fun l hl => hbg l (Nat.lt_succ_of_lt hl)) (fun l hl => hdiff l (Nat.lt_succ_of_lt hl)) a
    rw [QlinCompL_succ, QlinCompL_succ]
    simp only [ContinuousLinearMap.comp_apply]
    exact QlinStepL_row_nat hp' hpos hell (hbg j (Nat.lt_succ_self j)) he'
      (hdiff j (Nat.lt_succ_self j) e (by rw [pow_succ]; exact he')) _ _ (fun e' he'' => ih' e' he'')

end comp

end AdalyFormal.Thin
