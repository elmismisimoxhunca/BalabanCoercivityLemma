import TL11f

/-!
# TL12a -- index maps of `𝔅`, and `Q = (Q_j(U))_j` descends
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_val_eq coarseShift_apply_ne)
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp SU2)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.ClassJets (ReadRow)

section bidx
variable {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell k : ℕ}

theorem aligned_of_coarseShift {L' : PeriodicLatticeExtent} {s : ℕ} (hs : ∀ μ, s ∣ L' μ + 1) {y : PeriodicLatticeSite L'} {μ : Fin 3}
    (hy : Aligned s (coarseShift y s μ)) : Aligned s y := by
  intro ν
  by_cases hν : ν = μ
  · subst hν
    have h1 := hy ν
    rw [coarseShift_val_eq] at h1
    have h2 : s ∣ (y ν).val + s := (Nat.dvd_mod_iff (hs ν)).mp h1
    exact (Nat.dvd_add_left dvd_rfl).mp h2
  · have := hy ν
    rwa [coarseShift_apply_ne y s μ ν hν] at this

theorem bondsLam_aligned {L' : PeriodicLatticeExtent} {S : Tower L'} {j : ℕ} (hside : ∀ μ, ell ^ j ∣ L' μ + 1) {b : Bond L'}
    (hb : b ∈ bondsLam (geomOf ell k S) j) : Aligned (ell ^ j) b.1 := by
  rcases hb.1 with h1 | h1
  · exact (Set.mem_setOf_eq.mp h1).1
  · exact aligned_of_coarseShift hside (Set.mem_setOf_eq.mp h1).1

/-- READ-RESTRICTED `C²`-regularity of the averaging components of a background tower: only at the rows `ReadRow` read by a
bond-sector row `b ∈ Λ_j` of the tower `S'` (the class supplies exactly this, `ClassJets.classRows_read`; at the UR point an
unread aligned row of a class configuration is NOT differentiable, CJ6). -/
def JetReg {L' : PeriodicLatticeExtent} (ell k : ℕ) (S' : Tower L') (bg : ℕ → PeriodicLinkConfiguration SU2 L') : Prop :=
  ∀ j : ℕ, j ≤ k → ∀ b : PeriodicLatticeEdge L', b ∈ bondsLam (geomOf ell k S') j →
    ∀ l e, ReadRow ell j b l e → ContDiffAt ℝ 2 (qStepComp (ell ^ l) ell (bg l) e) 0

theorem suCoord_ell (o : Fin 3 → ℕ) (A : BondFnL2 L) : suCoord (liftF (phiE h o) A) = ellX h o (suCoord A) := rfl

theorem QlinB_nat {o : Fin 3 → ℕ} (hp : PhiOK h o (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L) {j : ℕ} (hj : j ≤ k)
    (hreg : JetReg ell k (towerPull h o S) (UbarTower su2LogExp ell (pullCfg h o U))) (A : BondFnL2 L) {b : Bond Lt}
    (hb : Aligned (ell ^ j) b.1) (hbL : b ∈ bondsLam (geomOf ell k (towerPull h o S)) j) :
    (QlinB (geomOf ell k (towerPull h o S)) (pullCfg h o U) j (liftF (phiE h o) A)).ofLp b =
      (QlinB (geomOf ell k S) U j A).ofLp (phiE h o b) := by
  rw [QlinB_apply, QlinB_apply, suCoord_ell]
  have hbg : ∀ l, l < j → AgreeAligned h o (ell ^ l) (UbarTower su2LogExp ell (pullCfg h o U) l) (UbarTower su2LogExp ell U l) :=
    fun l hl => UbarTower_nat su2LogExp hell U l (phiOK_le (hp := hp) (le_trans (le_of_lt hl) hj))
  have hdiff : ∀ l e, ReadRow ell j b l e →
      DifferentiableAt ℝ (qStepComp (ell ^ l) ell (UbarTower su2LogExp ell (pullCfg h o U) l) e) 0 :=
    fun l e hr => (hreg j hj b hbL l e hr).differentiableAt (by norm_num)
  have := QlinCompL_natR (h := h) (o := o) hell (UbarTower su2LogExp ell (pullCfg h o U)) (UbarTower su2LogExp ell U) j
    (phiOK_le (hp := hp) hj) hbg b hb hdiff (suCoord A)
  show (suCoordInv (QlinCompL ell (UbarTower su2LogExp ell (pullCfg h o U)) j (ellX h o (suCoord A)))).ofLp b = _
  show _ = (suCoordInv (QlinCompL ell (UbarTower su2LogExp ell U) j (suCoord A))).ofLp (phiE h o b)
  apply Subtype.ext
  show toM2 _ = toM2 _
  rw [this]

end bidx


end AdalyFormal.Thin
