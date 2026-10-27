import TL5a
import R2Ops1

/-!
# TL5b -- the covers of edges, and the first operators: masks, gradient, divergence, Laplacian
-/
set_option autoImplicit false
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.IngredientFamilyR2

theorem projS_eq_phiS {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) : projS h = phiS h (fun _ => 0) := by
  funext x μ; apply Fin.ext; simp [projS_val, phiS_val]

theorem tauS_eq_phiS {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (d : DeckIdx Lt L) :
    (tauS h d : PeriodicLatticeSite Lt → PeriodicLatticeSite Lt) = phiS (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) := by
  funext x μ; apply Fin.ext; rfl

def phiE {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (o : Fin 3 → ℕ) (e : PeriodicLatticeEdge Lt) : PeriodicLatticeEdge L :=
  (phiS h o e.1, e.2)

/-- edge cover -/
def covE {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) :
    Cov (DeckIdx Lt L) (PeriodicLatticeEdge Lt) (PeriodicLatticeEdge L) := (covS h).prodR (Fin 3)

theorem covE_pi {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) : (covE h).π = phiE h (fun _ => 0) := by
  funext e; simp only [covE, Cov.prodR, covS, phiE, projS_eq_phiS]

theorem covE_tau {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (d : DeckIdx Lt L) :
    ((covE h).τ d : PeriodicLatticeEdge Lt → PeriodicLatticeEdge Lt) =
      phiE (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) := by
  funext e; simp only [covE, Cov.prodR, covS, phiE, tauS_eq_phiS]; rfl

/-- pull back a configuration along `phiS` -/
def pullCfg {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (o : Fin 3 → ℕ) (U : Cfg L) : Cfg Lt := fun e => U (phiE h o e)

theorem gradL2_nat {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (o : Fin 3 → ℕ) (U : Cfg L)
    (f : SiteL2 L) :
    gradL2 (pullCfg h o U) (liftF (phiS h o) f) = liftF (phiE h o) (gradL2 U f) := by
  refine PiLp.ext (fun e => ?_)
  have h1 := congrFun (gradL2_apply (pullCfg h o U) (liftF (phiS h o) f)) e
  have h2 := congrFun (gradL2_apply U f) (phiE h o e)
  simp only [liftF_apply]
  show (WithLp.ofLp (gradL2 (pullCfg h o U) (liftF (phiS h o) f)) e) = (WithLp.ofLp (gradL2 U f)) (phiE h o e)
  rw [h1, h2]
  simp only [AdalyFormal.Balaban.CovariantOperators.gradValueCovariant, pullCfg, liftF_apply, phiE]
  rw [phiS_shift]

end AdalyFormal.Thin
