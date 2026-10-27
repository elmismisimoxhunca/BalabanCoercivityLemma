import TL12b

/-!
# TL12c -- `C^{(2)}` (`C2fullOf`) is natural
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp SU2)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.ClassJets (ReadRow)

section c2
variable {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell k : ℕ}

theorem D2B_nat {o : Fin 3 → ℕ} (hp : PhiOK h o (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L) {j : ℕ} (hj : j ≤ k)
    (hreg : JetReg ell k (towerPull h o S) (UbarTower su2LogExp ell (pullCfg h o U))) (A B : BondFnL2 L) {b : Bond Lt}
    (hb : Aligned (ell ^ j) b.1) (hbL : b ∈ bondsLam (geomOf ell k (towerPull h o S)) j) :
    (D2B (geomOf ell k (towerPull h o S)) (pullCfg h o U) j (liftF (phiE h o) A) (liftF (phiE h o) B)).ofLp b =
      (D2B (geomOf ell k S) U j A B).ofLp (phiE h o b) := by
  have hbg : ∀ l, l < j → AgreeAligned h o (ell ^ l) (UbarTower su2LogExp ell (pullCfg h o U) l) (UbarTower su2LogExp ell U l) :=
    fun l hl => UbarTower_nat su2LogExp hell U l (phiOK_le (hp := hp) (le_trans (le_of_lt hl) hj))
  have hC2 : ∀ l e, ReadRow ell j b l e →
      ContDiffAt ℝ 2 (qStepComp (ell ^ l) ell (UbarTower su2LogExp ell (pullCfg h o U) l) e) 0 :=
    fun l e hr => hreg j hj b hbL l e hr
  have := D2CompL_natR (h := h) (o := o) hell (UbarTower su2LogExp ell (pullCfg h o U)) (UbarTower su2LogExp ell U) j
    (phiOK_le (hp := hp) hj) hbg b hb hC2 (suCoord A) (suCoord B)
  show (suCoordInv (D2CompL ell (UbarTower su2LogExp ell (pullCfg h o U)) j (suCoord (liftF (phiE h o) A)) (suCoord (liftF (phiE h o) B)))).ofLp b = _
  show _ = (suCoordInv (D2CompL ell (UbarTower su2LogExp ell U) j (suCoord A) (suCoord B))).ofLp (phiE h o b)
  apply Subtype.ext
  show toM2 _ = toM2 _
  rw [suCoord_ell, suCoord_ell, this]

theorem C2fullOf_apply {L' : PeriodicLatticeExtent} (G : TowerGeom L') (U : Cfg L') (A : BondFnL2 L') (p : BIdx G) :
    C2fullOf G U A p = (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (C2rawB G U p.1 A)) p.2.1 := rfl

theorem C2fullOf_nat {o : Fin 3 → ℕ} (hp : PhiOK h o (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L)
    (St : Tower Lt) (hSt : St = towerPull h o S) (Ut : Cfg Lt) (hUt : Ut = pullCfg h o U)
    (hreg : JetReg ell k St (UbarTower su2LogExp ell Ut)) (hφ : ∀ j : Fin (k + 1), ∀ b, b ∈ bondsLam (geomOf ell k St) j →
      phiE h o b ∈ bondsLam (geomOf ell k S) j)
    (A : BondFnL2 L) (p : BIdx (geomOf ell k St)) :
    C2fullOf (geomOf ell k St) Ut (liftF (phiE h o) A) p =
      C2fullOf (geomOf ell k S) U A (bidxMap ell k St S (phiE h o) hφ p) := by
  subst hSt hUt
  obtain ⟨j, b, hb⟩ := p
  have hj : (j : ℕ) ≤ k := Nat.lt_succ_iff.mp j.2
  have hside : ∀ μ, ell ^ (j : ℕ) ∣ Lt μ + 1 := fun μ => ((phiOK_le (hp := hp) hj).side μ).trans (h μ)
  have hal : Aligned (ell ^ (j : ℕ)) b.1 := bondsLam_aligned hside hb
  rw [C2fullOf_apply, C2fullOf_apply]
  show _ • _ = _ • _
  congr 1
  show (((1 / 2 : ℝ) • D2B _ _ (j : ℕ) (liftF (phiE h o) A) (liftF (phiE h o) A))).ofLp b = ((1 / 2 : ℝ) • D2B _ _ (j : ℕ) A A).ofLp (phiE h o b)
  simp only [PiLp.smul_apply]
  rw [D2B_nat h hp hell S U hj hreg A A hal hb]

end c2


end AdalyFormal.Thin
