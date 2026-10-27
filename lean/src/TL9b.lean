import TL9a

/-!
# TL9b -- index maps of `L²(Λ_j)`, deck invariance of the pulled-back tower, `Q'` stack
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.IngredientFamilyR2

section lam
variable {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell k : ℕ}

/-- the pulled-back tower is deck invariant -/
theorem towerPull_tau (S : Tower L) (d : DeckIdx Lt L) :
    towerPull (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) (towerPull h (fun _ => 0) S) = towerPull h (fun _ => 0) S := by
  cases S
  simp only [towerPull]
  congr 1
  funext j
  ext x
  simp only [Set.mem_preimage, phiS_tau0]

/-- index map of `⨆ Λ_j` induced by a site map respecting the `Λ_j` -/
def lamMap (ell k : ℕ) {L' L : PeriodicLatticeExtent} (S' : Tower L') (S : Tower L) (φ : PeriodicLatticeSite L' → PeriodicLatticeSite L)
    (hφ : ∀ j : Fin (k + 1), ∀ y, y ∈ (geomOf ell k S').Lam j → φ y ∈ (geomOf ell k S).Lam j) :
    LamIdx (geomOf ell k S') → LamIdx (geomOf ell k S) := fun p => ⟨p.1, ⟨φ p.2.1, hφ p.1 p.2.1 p.2.2⟩⟩

theorem lamHφ_pi (hp : PhiOK h (fun _ => 0) (ell ^ k)) (S : Tower L) :
    ∀ j : Fin (k + 1), ∀ y, y ∈ (geomOf ell k (towerPull h (fun _ => 0) S)).Lam j →
      phiS h (fun _ => 0) y ∈ (geomOf ell k S).Lam j :=
  fun j y hy => (lam_iff hp (Nat.lt_succ_iff.mp j.2) y).mp hy

theorem lamHφ_tau (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hpd : ∀ d : DeckIdx Lt L, PhiOK (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) (ell ^ k))
    (S : Tower L) (d : DeckIdx Lt L) :
    ∀ j : Fin (k + 1), ∀ y, y ∈ (geomOf ell k (towerPull h (fun _ => 0) S)).Lam j →
      phiS (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) y ∈ (geomOf ell k (towerPull h (fun _ => 0) S)).Lam j := by
  intro j y hy
  have := (lam_iff (S := towerPull h (fun _ => 0) S) (hpd d) (Nat.lt_succ_iff.mp j.2) y).mp
  rw [towerPull_tau h S d] at this
  exact this hy

end lam

end AdalyFormal.Thin
