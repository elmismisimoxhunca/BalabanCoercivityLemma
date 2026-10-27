import NB23
/-!
# NB24 -- LOCAL level-uniform nonabelian curvature blocking (every `ell ≥ 2`)

`GoodPl ell R l y`: the level-`l` plaquette cone of `y` reaches only fine sites in `R` (defined by the
recursion of `prop1_level_loc`: level `l+1` needs level `l` at every `ell^l`-aligned site of the box
`Box y (ell^l) (2·ell^{l+1} − ell^l)`).  `curv_tower_na_loc`: `curv_tower_na` with the fine plaquette
hypothesis only on `R` and the conclusion at every aligned `y` whose cone is good.
`goodPl_univ`: with `R = everything` every cone is good (so `curv_tower_na` is the special case).

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2 ubarTowerSU2)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice)

variable {L : PeriodicLatticeExtent}

/-- Plaquette cone predicate. -/
def GoodPl (ell : ℕ) (R : PeriodicLatticeSite L → Prop) : ℕ → PeriodicLatticeSite L → Prop
  | 0, y => R y
  | l + 1, y => ∀ z ∈ CoarseLattice L (ell ^ l), Box y (ell ^ l) (2 * (ell ^ l * ell) - ell ^ l) z →
      GoodPl ell R l z

theorem goodPl_univ (ell : ℕ) : ∀ (l : ℕ) (y : PeriodicLatticeSite L), GoodPl ell (fun _ => True) l y := by
  intro l
  induction l with
  | zero => intro y; trivial
  | succ k ih => intro y z _ _; exact ih z

theorem curv_tower_na_loc (ell : ℕ) (hell : 2 ≤ ell) (U : PeriodicLinkConfiguration SU2 L) (q0 : ℝ)
    (R : PeriodicLatticeSite L → Prop)
    (hq0 : 0 ≤ q0) (h0 : ∀ y, R y → ∀ ν μ, dv (pw 1 U y ν μ) ≤ q0) (n : ℕ)
    (hdvd : ∀ ρ, ell ^ n ∣ L ρ + 1) (hN : ∀ ρ, 2 * ell ^ n < L ρ + 1)
    (hsmall : 4000000 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ n * q0) ≤ 1) :
    ∀ l ≤ n, ∀ y ∈ CoarseLattice L (ell ^ l), GoodPl ell R l y → ∀ ν μ : Fin 3,
      dv (pw (ell ^ l) (ubarTowerSU2 ell U l) y ν μ) ≤ 2 * (((ell : ℝ) ^ 2) ^ l * q0) := by
  have hell0 : 0 < ell := by omega
  have hl2 : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  set r : ℝ := (ell : ℝ) ^ 2 with hr
  have hr4 : 4 ≤ r := by rw [hr]; nlinarith
  have hr2 : 2 ≤ r := by linarith
  set K : ℝ := 1000000
  set S : ℕ → ℝ := fun l => ∑ m ∈ Finset.range l, r ^ m
  -- invariant
  have inv : ∀ l ≤ n, ∀ y ∈ CoarseLattice L (ell ^ l), GoodPl ell R l y → ∀ ν μ : Fin 3,
      dv (pw (ell ^ l) (ubarTowerSU2 ell U l) y ν μ) ≤ r ^ l * q0 * (1 + 4 * K * r * q0 * S l) := by
    intro l
    induction l with
    | zero =>
        intro _ y _ hg ν μ
        show dv (pw 1 U y ν μ) ≤ _
        simp only [S, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero, pow_zero, one_mul,
          mul_one]
        exact h0 y hg ν μ
    | succ k ih =>
        intro hk y hy hg ν μ
        have hs : 0 < ell ^ k := pow_pos hell0 k
        have hrk : r ^ k ≤ r ^ n := pow_le_pow_right₀ (by linarith) (by omega)
        have hSk : S k ≤ r ^ k := geom_le r hr2 k
        have hD : 4 * K * r * q0 * S k ≤ 1 := by
          have : 4 * K * r * q0 * S k ≤ 4 * K * r * q0 * r ^ n := by
            have := mul_le_mul_of_nonneg_left (le_trans hSk hrk)
              (by positivity : (0:ℝ) ≤ 4 * K * r * q0)
            linarith
          have e : 4 * K * r * q0 * r ^ n = 4000000 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ n * q0) := by
            simp only [K, hr]; ring
          linarith
        set P : ℝ := r ^ k * q0 * (1 + 4 * K * r * q0 * S k)
        have hP0 : 0 ≤ P := by
          have : 0 ≤ S k := Finset.sum_nonneg (fun m _ => by positivity)
          positivity
        have hP2 : P ≤ 2 * (r ^ k * q0) := by
          have : 0 ≤ r ^ k * q0 := by positivity
          simp only [P]; nlinarith
        have hδ : (ell : ℝ) ^ 4 * P ≤ 1 / 100000 := by
          have e4 : (ell : ℝ) ^ 4 = r ^ 2 := by rw [hr]; ring
          have h1 : (ell : ℝ) ^ 4 * P ≤ 2 * r * (r ^ (k + 1) * q0) := by
            rw [e4, pow_succ]
            have := mul_le_mul_of_nonneg_left hP2 (sq_nonneg r)
            calc r ^ 2 * P ≤ r ^ 2 * (2 * (r ^ k * q0)) := this
              _ = 2 * r * (r ^ k * r * q0) := by ring
          have hrk1 : r ^ (k + 1) ≤ r ^ n := pow_le_pow_right₀ (by linarith) hk
          have h2 : 2 * r * (r ^ (k + 1) * q0) ≤ 2 * r * (r ^ n * q0) := by
            have := mul_le_mul_of_nonneg_right hrk1 hq0
            nlinarith
          have h3 : 2 * r * (r ^ n * q0) ≤ 1 / 2000000 := by
            have e : 4000000 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ n * q0) = 4000000 * r * (r ^ n * q0) := by
              rw [hr]
            rw [e] at hsmall
            linarith
          linarith
        have hd1 : ∀ ρ, ell ^ k * ell ∣ L ρ + 1 := fun ρ =>
          Nat.dvd_trans (by rw [← pow_succ]; exact Nat.pow_dvd_pow ell hk) (hdvd ρ)
        have hN1 : ∀ ρ, 2 * (ell ^ k * ell) < L ρ + 1 := fun ρ => by
          have : ell ^ k * ell ≤ ell ^ n := by rw [← pow_succ]; exact Nat.pow_le_pow_right hell0 hk
          have := hN ρ; omega
        have hy' : y ∈ CoarseLattice L (ell ^ k * ell) := by rw [← pow_succ]; exact hy
        have hstep := prop1_level_loc (ell ^ k) ell hs hell0 (ubarTowerSU2 ell U k) P hP0 hδ hd1 hN1
          y hy' (fun z hz hbox ν' μ' => ih (by omega) z hz (hg z hz hbox) ν' μ') ν μ
        have hpw : pw (ell ^ (k + 1)) (ubarTowerSU2 ell U (k + 1)) y ν μ
            = pw (ell ^ k * ell) (ubarSU2 (ell ^ k) ell (ubarTowerSU2 ell U k)) y ν μ := by
          rw [pow_succ]; rfl
        rw [hpw]
        refine le_trans hstep ?_
        -- ell² P + K ell⁴ P² ≤ r^{k+1} q0 (1 + 4 K r q0 S(k+1))
        have hSk1 : S (k + 1) = S k + r ^ k := by simp only [S, Finset.sum_range_succ]
        rw [hSk1]
        have e2 : (ell : ℝ) ^ 2 * P + 1000000 * ((ell : ℝ) ^ 4 * P ^ 2) = r * P * (1 + K * r * P) := by
          simp only [K, hr]; ring
        rw [e2]
        have hKP : K * r * P ≤ 2 * K * r * (r ^ k * q0) := by
          have := mul_le_mul_of_nonneg_left hP2 (by positivity : (0:ℝ) ≤ K * r)
          linarith
        set D := 4 * K * r * q0 * S k
        set d := 2 * K * r * (r ^ k * q0)
        have hd0 : 0 ≤ d := by positivity
        have hrP : r * P = r ^ (k + 1) * q0 * (1 + D) := by simp only [P, D]; rw [pow_succ]; ring
        rw [hrP]
        have hgoal : (1 + D) * (1 + K * r * P) ≤ 1 + 4 * K * r * q0 * (S k + r ^ k) := by
          have : (1 + D) * (1 + K * r * P) ≤ (1 + D) * (1 + d) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          have e3 : 4 * K * r * q0 * (S k + r ^ k) = D + 2 * d := by simp only [D, d]; ring
          rw [e3]
          nlinarith
        have hq1 : 0 ≤ r ^ (k + 1) * q0 := by positivity
        calc r ^ (k + 1) * q0 * (1 + D) * (1 + K * r * P)
            = r ^ (k + 1) * q0 * ((1 + D) * (1 + K * r * P)) := by ring
          _ ≤ r ^ (k + 1) * q0 * (1 + 4 * K * r * q0 * (S k + r ^ k)) :=
            mul_le_mul_of_nonneg_left hgoal hq1
  intro l hl y hy hg ν μ
  refine le_trans (inv l hl y hy hg ν μ) ?_
  have hrl : r ^ l ≤ r ^ n := pow_le_pow_right₀ (by linarith) hl
  have hSl : S l ≤ r ^ l := geom_le r hr2 l
  have hD : 4 * K * r * q0 * S l ≤ 1 := by
    have : 4 * K * r * q0 * S l ≤ 4 * K * r * q0 * r ^ n := by
      have := mul_le_mul_of_nonneg_left (le_trans hSl hrl) (by positivity : (0:ℝ) ≤ 4 * K * r * q0)
      linarith
    have e : 4 * K * r * q0 * r ^ n = 4000000 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ n * q0) := by
      simp only [K, hr]; ring
    linarith
  have : 0 ≤ r ^ l * q0 := by positivity
  nlinarith

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.curv_tower_na_loc
