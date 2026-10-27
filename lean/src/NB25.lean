import NB24
/-!
# NB25 -- LOCAL level-uniform nonabelian link tower (every `ell ≥ 2`)

`GoodBd ell R l c`: the defect cone of the level-`l` bond `c` meets only plaquette cones that are good
(`GoodPl`).  `link_tower_na_loc`: fine plaquette words `≤ q0` on `R`, fine links `≤ e` on `Rl`
(in one gauge), smallness as in `curv_tower_na`  ⟹  at every aligned `c` with good cones:
`dv (ubarTowerSU2 ell U l c) ≤ ell^l e + 3π (ell²)^l q0`.

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath)
open AdalyFormal.Balaban.UbarTowerCov (coarseBondVar)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2 ubarTowerSU2)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)

variable {L : PeriodicLatticeExtent}

def GoodBd (ell : ℕ) (R : PeriodicLatticeSite L → Prop) : ℕ → PeriodicLatticeEdge L → Prop
  | 0, _ => True
  | l + 1, c =>
      (∀ b ∈ pathBonds (ell ^ l) c.1 (List.replicate ell c.2), GoodBd ell R l b) ∧
      (∀ x ∈ stepBlockOf c.1 (ell ^ l) ell,
        ∀ t ∈ ladPlaqs (ell ^ l) c.2 ell c.1 (coarseGammaPath (ell ^ l) c.1 x), GoodPl ell R l t.1)

theorem goodBd_univ (ell : ℕ) : ∀ (l : ℕ) (c : PeriodicLatticeEdge L),
    GoodBd ell (fun _ => True) l c := by
  intro l
  induction l with
  | zero => intro c; trivial
  | succ k ih => intro c; exact ⟨fun b _ => ih b, fun x _ t _ => goodPl_univ ell k t.1⟩

theorem defect_tower_aligned_loc (ell : ℕ) (hell : 2 ≤ ell) (U : PeriodicLinkConfiguration SU2 L)
    (R : PeriodicLatticeSite L → Prop) (q0 C : ℝ) (hq0 : 0 ≤ q0) (hC : 0 ≤ C) (n : ℕ)
    (hdvd : ∀ ρ, ell ^ n ∣ L ρ + 1)
    (hP : ∀ l < n, ∀ y ∈ CoarseLattice L (ell ^ l), GoodPl ell R l y → ∀ ν μ : Fin 3,
      dv (pw (ell ^ l) (ubarTowerSU2 ell U l) y ν μ) ≤ C * ((ell : ℝ) ^ 2) ^ l * q0) :
    ∀ l ≤ n, ∀ c : PeriodicLatticeEdge L, c.1 ∈ CoarseLattice L (ell ^ l) → GoodBd ell R l c →
      dv (ubarTowerSU2 ell U l c * (strT ell U l c)⁻¹)
        ≤ 3 * Real.pi / 2 * C * ((ell : ℝ) ^ 2) ^ l * q0 := by
  have hell0 : 0 < ell := by omega
  have hpi := Real.pi_pos
  intro l
  induction l with
  | zero =>
      intro _ c _ _
      show dv (U c * (U c)⁻¹) ≤ _
      rw [mul_inv_cancel, dv_one, pow_zero, mul_one]; positivity
  | succ k ih =>
      intro hk c hc hg
      obtain ⟨hg1, hg2⟩ := hg
      have hs : 0 < ell ^ k := pow_pos hell0 k
      have hd0 : ∀ ρ, ell ^ k ∣ L ρ + 1 := fun ρ =>
        Nat.dvd_trans (Nat.pow_dvd_pow ell (by omega)) (hdvd ρ)
      have hc' : c.1 ∈ CoarseLattice L (ell ^ k * ell) := by rw [← pow_succ]; exact hc
      have hck := cl_mono (ell ^ k) ell hc'
      set X : ℝ := ((ell : ℝ) ^ 2) ^ k * q0
      have hX : 0 ≤ X := by positivity
      have hstep := defect_step_curv (ell ^ k) ell hs hell0 (ubarTowerSU2 ell U k) (strT ell U k) c
        (3 * Real.pi / 2 * C * X) (C * X) (by positivity)
        (fun b hb => (ih (by omega) b (pathBonds_aligned _ hd0 _ _ hck b hb) (hg1 b hb)).trans
          (le_of_eq (by simp only [X]; ring)))
        (fun x hx t ht => (hP k (by omega) t.1 (ladPlaqs_aligned _ hd0 _ _ _ _ hck t ht)
          (hg2 x hx t ht) t.2.1 t.2.2).trans (le_of_eq (by simp only [X]; ring)))
      have hsh : ubarTowerSU2 ell U (k + 1) c * (strT ell U (k + 1) c)⁻¹
          = ubarSU2 (ell ^ k) ell (ubarTowerSU2 ell U k) c
            * (coarseBondVar (ell ^ k) ell (strT ell U k) c)⁻¹ := rfl
      rw [hsh]
      refine le_trans hstep ?_
      have hpow : 3 * Real.pi / 2 * C * ((ell : ℝ) ^ 2) ^ (k + 1) * q0
          = 3 * Real.pi / 2 * C * X * (ell : ℝ) ^ 2 := by simp only [X]; ring
      rw [hpow]
      exact le_of_eq (by ring)

theorem link_tower_na_loc (ell : ℕ) (hell : 2 ≤ ell) (U : PeriodicLinkConfiguration SU2 L)
    (R : PeriodicLatticeSite L → Prop) (Rl : PeriodicLatticeEdge L → Prop) (q0 e : ℝ)
    (hq0 : 0 ≤ q0) (h0 : ∀ y, R y → ∀ ν μ, dv (pw 1 U y ν μ) ≤ q0)
    (he : ∀ b, Rl b → dv (U b) ≤ e) (n : ℕ)
    (hdvd : ∀ ρ, ell ^ n ∣ L ρ + 1) (hN : ∀ ρ, 2 * ell ^ n < L ρ + 1)
    (hsmall : 4000000 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ n * q0) ≤ 1)
    (l : ℕ) (hl : l ≤ n) (c : PeriodicLatticeEdge L) (hc : c.1 ∈ CoarseLattice L (ell ^ l))
    (hgB : GoodBd ell R l c) (hgL : goodL ell Rl l c) :
    dv (ubarTowerSU2 ell U l c) ≤ (ell : ℝ) ^ l * e + 3 * Real.pi * (((ell : ℝ) ^ 2) ^ l * q0) := by
  have hcurv := curv_tower_na_loc ell hell U q0 R hq0 h0 n hdvd hN hsmall
  have hD := defect_tower_aligned_loc ell hell U R q0 2 hq0 (by norm_num) n hdvd
    (fun l hl y hy hg ν μ => (hcurv l (le_of_lt hl) y hy hg ν μ).trans (le_of_eq (by ring)))
    l hl c hc hgB
  have hT := strT_link_le_loc ell U Rl e he l c hgL
  have hid : ubarTowerSU2 ell U l c
      = (ubarTowerSU2 ell U l c * (strT ell U l c)⁻¹) * strT ell U l c := by group
  rw [hid]
  have := dv_mul (ubarTowerSU2 ell U l c * (strT ell U l c)⁻¹) (strT ell U l c)
  have e3 : 3 * Real.pi / 2 * 2 * ((ell : ℝ) ^ 2) ^ l * q0 = 3 * Real.pi * (((ell : ℝ) ^ 2) ^ l * q0) := by
    ring
  linarith

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.defect_tower_aligned_loc
#print axioms AdalyFormal.CurvBlock.link_tower_na_loc
