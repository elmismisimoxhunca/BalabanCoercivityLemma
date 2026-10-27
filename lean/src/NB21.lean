import NB20
import CB7
/-!
# NB21 -- level-uniform nonabelian LINK tower at aligned bonds, every `ell ≥ 2`

* `defect_tower_aligned`: CB7's reduction restricted to aligned bonds/plaquettes.
* `link_tower_na`: under `curv_tower_na`'s hypotheses and `dv (U b) ≤ e` for every fine bond, at every
  `ell^l`-aligned bond `c` (`l ≤ n`):
  `dv (ubarTowerSU2 ell U l c) ≤ ell^l e + 3π (ell²)^l q0`.

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.Balaban.UbarTowerCov (coarseBondVar)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2 ubarTowerSU2)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)

variable {L : PeriodicLatticeExtent}

theorem defect_tower_aligned (ell : ℕ) (hell : 2 ≤ ell) (U : PeriodicLinkConfiguration SU2 L)
    (q0 C : ℝ) (hq0 : 0 ≤ q0) (hC : 0 ≤ C) (n : ℕ) (hdvd : ∀ ρ, ell ^ n ∣ L ρ + 1)
    (hP : ∀ l < n, ∀ y ∈ CoarseLattice L (ell ^ l), ∀ ν μ : Fin 3,
      dv (pw (ell ^ l) (ubarTowerSU2 ell U l) y ν μ) ≤ C * ((ell : ℝ) ^ 2) ^ l * q0) :
    ∀ l ≤ n, ∀ c : PeriodicLatticeEdge L, c.1 ∈ CoarseLattice L (ell ^ l) →
      dv (ubarTowerSU2 ell U l c * (strT ell U l c)⁻¹)
        ≤ 3 * Real.pi / 2 * C * ((ell : ℝ) ^ 2) ^ l * q0 := by
  have hell0 : 0 < ell := by omega
  have hpi := Real.pi_pos
  intro l
  induction l with
  | zero =>
      intro _ c _
      show dv (U c * (U c)⁻¹) ≤ _
      rw [mul_inv_cancel, dv_one, pow_zero, mul_one]; positivity
  | succ k ih =>
      intro hk c hc
      have hs : 0 < ell ^ k := pow_pos hell0 k
      have hd1 : ∀ ρ, ell ^ k * ell ∣ L ρ + 1 := fun ρ =>
        Nat.dvd_trans (by rw [← pow_succ]; exact Nat.pow_dvd_pow ell hk) (hdvd ρ)
      have hd0 : ∀ ρ, ell ^ k ∣ L ρ + 1 := fun ρ =>
        Nat.dvd_trans (Nat.pow_dvd_pow ell (by omega)) (hdvd ρ)
      have hc' : c.1 ∈ CoarseLattice L (ell ^ k * ell) := by rw [← pow_succ]; exact hc
      have hck := cl_mono (ell ^ k) ell hc'
      set X : ℝ := ((ell : ℝ) ^ 2) ^ k * q0
      have hX : 0 ≤ X := by positivity
      have hstep := defect_step_curv (ell ^ k) ell hs hell0 (ubarTowerSU2 ell U k) (strT ell U k) c
        (3 * Real.pi / 2 * C * X) (C * X) (by positivity)
        (fun b hb => (ih (by omega) b (pathBonds_aligned _ hd0 _ _ hck b hb)).trans
          (le_of_eq (by simp only [X]; ring)))
        (fun x _ t ht => (hP k (by omega) t.1 (ladPlaqs_aligned _ hd0 _ _ _ _ hck t ht)
          t.2.1 t.2.2).trans (le_of_eq (by simp only [X]; ring)))
      have hsh : ubarTowerSU2 ell U (k + 1) c * (strT ell U (k + 1) c)⁻¹
          = ubarSU2 (ell ^ k) ell (ubarTowerSU2 ell U k) c
            * (coarseBondVar (ell ^ k) ell (strT ell U k) c)⁻¹ := rfl
      rw [hsh]
      refine le_trans hstep ?_
      have hpow : 3 * Real.pi / 2 * C * ((ell : ℝ) ^ 2) ^ (k + 1) * q0
          = 3 * Real.pi / 2 * C * X * (ell : ℝ) ^ 2 := by simp only [X]; ring
      rw [hpow]
      exact le_of_eq (by ring)

theorem link_tower_na (ell : ℕ) (hell : 2 ≤ ell) (U : PeriodicLinkConfiguration SU2 L) (q0 e : ℝ)
    (hq0 : 0 ≤ q0) (h0 : ∀ y ν μ, dv (pw 1 U y ν μ) ≤ q0) (he : ∀ b, dv (U b) ≤ e) (n : ℕ)
    (hdvd : ∀ ρ, ell ^ n ∣ L ρ + 1) (hN : ∀ ρ, 2 * ell ^ n < L ρ + 1)
    (hsmall : 4000000 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ n * q0) ≤ 1)
    (l : ℕ) (hl : l ≤ n) (c : PeriodicLatticeEdge L) (hc : c.1 ∈ CoarseLattice L (ell ^ l)) :
    dv (ubarTowerSU2 ell U l c) ≤ (ell : ℝ) ^ l * e + 3 * Real.pi * (((ell : ℝ) ^ 2) ^ l * q0) := by
  have hcurv := curv_tower_na ell hell U q0 hq0 h0 n hdvd hN hsmall
  have hD := defect_tower_aligned ell hell U q0 2 hq0 (by norm_num) n hdvd
    (fun l hl y hy ν μ => (hcurv l (le_of_lt hl) y hy ν μ).trans (le_of_eq (by ring))) l hl c hc
  have hT := strT_link_le ell U e he l c
  have hid : ubarTowerSU2 ell U l c
      = (ubarTowerSU2 ell U l c * (strT ell U l c)⁻¹) * strT ell U l c := by group
  rw [hid]
  have := dv_mul (ubarTowerSU2 ell U l c * (strT ell U l c)⁻¹) (strT ell U l c)
  have e3 : 3 * Real.pi / 2 * 2 * ((ell : ℝ) ^ 2) ^ l * q0 = 3 * Real.pi * (((ell : ℝ) ^ 2) ^ l * q0) := by
    ring
  linarith

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.defect_tower_aligned
#print axioms AdalyFormal.CurvBlock.link_tower_na
