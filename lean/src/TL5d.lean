import TL5c
import TL3c

set_option autoImplicit false
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.IngredientFamilyR2

theorem covS_pi {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) : (covS h).π = phiS h (fun _ => 0) := projS_eq_phiS h

theorem covS_tau {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (d : DeckIdx Lt L) :
    ((covS h).τ d : PeriodicLatticeSite Lt → PeriodicLatticeSite Lt) =
      phiS (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) := tauS_eq_phiS h d

/-- invariance of the pulled-back configuration under the deck translations -/
theorem pullCfg_tau {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (d : DeckIdx Lt L) (U : Cfg L) :
    pullCfg (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) (pullCfg h (fun _ => 0) U) = pullCfg h (fun _ => 0) U := by
  funext e
  simp only [pullCfg, phiE]
  have : phiS h (fun _ => 0) (phiS (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) e.1) = phiS h (fun _ => 0) e.1 := by
    funext μ
    apply Fin.ext
    simp only [phiS_val]
    rw [← Nat.mod_add_mod _ (L μ + 1), Nat.mod_mod_of_dvd _ (h μ), Nat.mod_add_mod, Nat.add_zero, Nat.add_mul_mod_self_right]
    simp
  rw [this]

theorem desc_of_nat_phi {D X Xt Y Yt : Type} [Fintype D] [Fintype X] [Fintype Xt] [Fintype Y] [Fintype Yt]
    [DecidableEq X] [DecidableEq Xt] [DecidableEq Y] [DecidableEq Yt] [Nonempty D]
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (cX : Cov D Xt X) (cY : Cov D Yt Y)
    (O : PiLp 2 (fun _ : X => E) →L[ℝ] PiLp 2 (fun _ : Y => E))
    (Ot : PiLp 2 (fun _ : Xt => E) →L[ℝ] PiLp 2 (fun _ : Yt => E))
    (φX : Xt → X) (φY : Yt → Y) (ψX : D → Xt → Xt) (ψY : D → Yt → Yt)
    (hπX : cX.π = φX) (hπY : cY.π = φY) (hτX : ∀ d, ⇑(cX.τ d) = ψX d) (hτY : ∀ d, ⇑(cY.τ d) = ψY d)
    (e1 : ∀ f, Ot (liftF φX f) = liftF φY (O f))
    (eq : ∀ d f, Ot (liftF (ψX d) f) = liftF (ψY d) (Ot f)) : Desc cX cY O Ot := by
  apply desc_of_e1_equi
  · ext1 f
    simp only [ContinuousLinearMap.comp_apply]
    show Ot (liftF cX.π f) = liftF cY.π (O f)
    rw [hπX, hπY]; exact e1 f
  · intro d
    ext1 f
    simp only [ContinuousLinearMap.comp_apply]
    show Ot (liftF (cX.τ d) f) = liftF (cY.τ d) (Ot f)
    have := eq d f
    rw [← hτX d, ← hτY d] at this
    exact this

theorem desc_gradL2 {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (U : Cfg L) :
    Desc (covS h) (covE h) (gradL2 U) (gradL2 (pullCfg h (fun _ => 0) U)) := by
  haveI := deckIdx_nonempty h
  refine desc_of_nat_phi (covS h) (covE h) _ _ (phiS h (fun _ => 0)) (phiE h (fun _ => 0))
    (fun d => phiS (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)))
    (fun d => phiE (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1))) (covS_pi h) (covE_pi h)
    (fun d => covS_tau h d) (fun d => covE_tau h d) (fun f => gradL2_nat h _ U f) (fun d f => ?_)
  have := gradL2_nat (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) (pullCfg h (fun _ => 0) U) f
  rwa [pullCfg_tau] at this

theorem desc_gradAdj {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (U : Cfg L) :
    Desc (covE h) (covS h) (gradAdj U) (gradAdj (pullCfg h (fun _ => 0) U)) := by
  haveI := deckIdx_nonempty h
  refine desc_of_nat_phi (covE h) (covS h) _ _ (phiE h (fun _ => 0)) (phiS h (fun _ => 0))
    (fun d => phiE (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)))
    (fun d => phiS (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1))) (covE_pi h) (covS_pi h)
    (fun d => covE_tau h d) (fun d => covS_tau h d) (fun f => gradAdj_nat h _ U f) (fun d f => ?_)
  have := gradAdj_nat (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) (pullCfg h (fun _ => 0) U) f
  rwa [pullCfg_tau] at this

open Classical in
theorem desc_siteMask {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (S : Set (PeriodicLatticeSite L)) :
    Desc (covS h) (covS h) (siteMask S) (siteMask (phiS h (fun _ => 0) ⁻¹' S)) := by
  haveI := deckIdx_nonempty h
  refine desc_of_nat_phi (covS h) (covS h) _ _ (phiS h (fun _ => 0)) (phiS h (fun _ => 0))
    (fun d => phiS (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)))
    (fun d => phiS (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1))) (covS_pi h) (covS_pi h)
    (fun d => covS_tau h d) (fun d => covS_tau h d) (fun f => siteMask_nat h _ S f) (fun d f => ?_)
  have := siteMask_nat (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) (phiS h (fun _ => 0) ⁻¹' S) f
  have hinv : phiS (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) ⁻¹' (phiS h (fun _ => 0) ⁻¹' S) =
      phiS h (fun _ => 0) ⁻¹' S := by
    ext x
    simp only [Set.mem_preimage]
    have : phiS h (fun _ => 0) (phiS (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) x) = phiS h (fun _ => 0) x := by
      funext μ
      apply Fin.ext
      simp only [phiS_val]
      rw [← Nat.mod_add_mod _ (L μ + 1), Nat.mod_mod_of_dvd _ (h μ), Nat.mod_add_mod, Nat.add_zero, Nat.add_mul_mod_self_right]
      simp
    rw [this]
  rwa [hinv] at this

end AdalyFormal.Thin
