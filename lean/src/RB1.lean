import SH13

/-!
# RB1 -- the printed tower conditions (CMP96 (2.1),(2.2); CMP99b p.393, p.394, p.396) in fine-site coordinates,
and their comparison with the frozen `AdalyFormal.StatementLane.Admissible`.

Coordinates (READING.md, section 5): the fine lattice `T_eta` has spacing `eta` = ONE SITE; the lattice
`T^{(j)}_{L^j eta}` is the sub-grid of sites whose coordinates are multiples of `ell^j` (`ell = L`); a big block of
`T^{(j)}_{L^j eta}` is a cube of `M x M x M` of its points, i.e. `M ell^j` fine sites; `B^j(y)` is the `ell^j`-block
of fine sites `y_mu <= x_mu < y_mu + ell^j`.  `dist` is the `l^1` distance on `T_eta` (CMP96 p.223), periodic on the torus.
`T_1 = T_{L^{-0}}` of p.396 is `T_eta` measured in units of `L^0 eta = eta`: blocks of `M` sites, collar `R M` sites.

Nothing is re-defined from the frozen statement: `Tower`, `Admissible`, `pdist`, `BlockClosed`, `bigSide` are imported.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.RBridge

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.P409S

variable {L : PeriodicLatticeExtent}

/-! ## printed vocabulary -/

/-- the cell `{z : z_mu / s = b_mu}` of the partition of `T_eta` into cubes of side `s` cut at multiples of `s`
("elementary cubes (cells) of the lattice `s Z^d`", p.408). -/
def BigBlockCell (s : ℕ) (b : Fin 3 → ℕ) : Set (PeriodicLatticeSite L) :=
  {z | ∀ μ, (z μ).val / s = b μ}

/-- `A` is a big block of side `s` (in fine sites). -/
def IsBigBlock (s : ℕ) (A : Set (PeriodicLatticeSite L)) : Prop := ∃ b, A = BigBlockCell s b

/-- `dist(A,B) <= r` for finite sets of sites: some pair at `l^1` periodic distance `<= r` (the infimum is attained). -/
def SetDistLe (A B : Set (PeriodicLatticeSite L)) (r : ℕ) : Prop := ∃ z ∈ A, ∃ y ∈ B, pdist z y ≤ r

/-- `dist(A,B) < r`. -/
def SetDistLt (A B : Set (PeriodicLatticeSite L)) (r : ℕ) : Prop := ∃ z ∈ A, ∃ y ∈ B, pdist z y < r

/-- every point of `A` is within `r` of `B` (the "all points" reading of "their distances to Omega_1 are <= RM"). -/
def SetAllLe (A B : Set (PeriodicLatticeSite L)) (r : ℕ) : Prop := ∀ z ∈ A, ∃ y ∈ B, pdist z y ≤ r

/-- the sub-grid `T^{(j)}_{L^j eta}` of `T_eta`. -/
def CoarseGrid (ell j : ℕ) : Set (PeriodicLatticeSite L) := {y | ∀ μ, ell ^ j ∣ (y μ).val}

/-- `B^j(W)`: the union of the `ell^j`-blocks `{x : y_mu <= x_mu < y_mu + ell^j}` of the points `y` of `W`. -/
def Bj (ell j : ℕ) (W : Set (PeriodicLatticeSite L)) : Set (PeriodicLatticeSite L) :=
  {x | ∃ y ∈ W, ∀ μ, (y μ).val ≤ (x μ).val ∧ (x μ).val < (y μ).val + ell ^ j}

/-- `W ⊂ T^{(j)}_{L^j eta}` is a sum of big blocks (side `M` in the units of that lattice): closed under "same coarse block". -/
def CoarseBlockSum (ell M j : ℕ) (W : Set (PeriodicLatticeSite L)) : Prop :=
  W ⊆ CoarseGrid ell j ∧
    ∀ y ∈ W, ∀ y' ∈ CoarseGrid ell j, (∀ μ, (y' μ).val / ell ^ j / M = (y μ).val / ell ^ j / M) → y' ∈ W

/-- the printed `Omega_0` of p.396: the union of the big blocks `A` of `T_1` with `dist(A, Omega_1) <= R M`. -/
def Om0Print (M R : ℕ) (Om1 : Set (PeriodicLatticeSite L)) : Set (PeriodicLatticeSite L) :=
  {x | ∃ A, IsBigBlock M A ∧ SetDistLe A Om1 (R * M) ∧ x ∈ A}

/-- the printed tower conditions: (2.1) with `Omega_0` prepended and `Omega_{k+1} = emptyset` (p.393); (2.2) first line
(`Omega_j = B^j(Omega_j^{(j)})`, `Omega_j^{(j)} ⊂ T^{(j)}_{L^j eta}` a sum of big blocks) with the big blocks tiling the torus;
(2.2) second line `(L^j eta)^{-1} dist(Omega_j^c, Omega_{j+1}) > R M` (distance in site units, `eta` = one site);
and the base law of p.396 for `Omega_0`. -/
def PrintedTower (ell M R k : ℕ) (S : Tower L) : Prop :=
  (∀ j, j ≤ k → S.Om (j + 1) ⊆ S.Om j) ∧
  S.Om (k + 1) = ∅ ∧
  (∀ j, j ≤ k → ∀ μ : Fin 3, M * ell ^ j ∣ L μ + 1) ∧
  (∀ j, j ≤ k → ∃ W, CoarseBlockSum ell M j W ∧ S.Om j = Bj ell j W) ∧
  (∀ j, j ≤ k → ∀ x : PeriodicLatticeSite L, x ∉ S.Om j → ∀ y ∈ S.Om (j + 1),
      ((R * M : ℕ) : ℚ) < (pdist x y : ℚ) / ((ell : ℚ) ^ j)) ∧
  S.Om 0 = Om0Print M R (S.Om 1)

/-- the convention of the frozen definition: levels above `k` are padded by the empty set. -/
def PadAbove (k : ℕ) (S : Tower L) : Prop := ∀ j, k < j → S.Om j = ∅

/-! ## block-closure = "sum of big blocks of `T^{(j)}`" -/

theorem div_div_comm' (a e M : ℕ) : a / e / M = a / (M * e) := by
  rw [Nat.div_div_eq_div_mul, mul_comm]

/-- floor of `x` to the grid `e Z`, as a site. -/
def floorSite (e : ℕ) (x : PeriodicLatticeSite L) : PeriodicLatticeSite L :=
  fun μ => ⟨(x μ).val / e * e, lt_of_le_of_lt (Nat.div_mul_le_self _ _) (x μ).isLt⟩

theorem floorSite_val (e : ℕ) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    (floorSite e x μ).val = (x μ).val / e * e := rfl

theorem floorSite_div (e : ℕ) (he : 0 < e) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    (floorSite e x μ).val / e = (x μ).val / e := by
  rw [floorSite_val]; exact Nat.mul_div_cancel _ he

theorem floorSite_mem_grid (e : ℕ) (x : PeriodicLatticeSite L) : floorSite (L := L) e x ∈ CoarseGrid e 1 := by
  intro μ; rw [floorSite_val, pow_one]; exact dvd_mul_left _ _

theorem blockClosed_iff_sum {ell M j : ℕ} (hell : 0 < ell) (hM : 0 < M) (Ω : Set (PeriodicLatticeSite L)) :
    BlockClosed (bigSide M ell j) Ω ↔ ∃ W, CoarseBlockSum ell M j W ∧ Ω = Bj ell j W := by
  have he : 0 < ell ^ j := pow_pos hell j
  have hb : bigSide M ell j = M * ell ^ j := rfl
  rw [hb]
  constructor
  · intro hbc
    refine ⟨{y | y ∈ Ω ∧ ∀ μ, ell ^ j ∣ (y μ).val}, ⟨fun y hy => hy.2, ?_⟩, ?_⟩
    · intro y hy y' hy' hsame
      refine ⟨hbc y hy.1 y' ?_, hy'⟩
      intro μ
      rw [← div_div_comm', ← div_div_comm']; exact hsame μ
    · ext x
      constructor
      · intro hx
        refine ⟨floorSite (ell ^ j) x, ⟨?_, ?_⟩, ?_⟩
        · refine hbc x hx _ ?_
          intro μ
          rw [floorSite_val, ← div_div_comm', ← div_div_comm', Nat.mul_div_cancel _ he]
        · intro μ; rw [floorSite_val]; exact dvd_mul_left _ _
        · intro μ
          refine ⟨?_, ?_⟩
          · rw [floorSite_val]; exact Nat.div_mul_le_self _ _
          · rw [floorSite_val]; exact Nat.lt_div_mul_add he
      · rintro ⟨y, ⟨hyΩ, hyg⟩, hyx⟩
        refine hbc y hyΩ x ?_
        intro μ
        obtain ⟨c, hc⟩ := hyg μ
        have h1 : (x μ).val / ell ^ j = c := by
          have := hyx μ
          rw [hc] at this
          exact Nat.div_eq_of_lt_le (by nlinarith [this.1]) (by nlinarith [this.2])
        have h2 : (y μ).val / ell ^ j = c := by rw [hc]; exact Nat.mul_div_cancel_left _ he
        rw [← div_div_comm', ← div_div_comm', h1, h2]
  · rintro ⟨W, ⟨hWg, hWb⟩, rfl⟩ x ⟨y, hy, hyx⟩ x' hx'
    have hyg := hWg hy
    have hxe : ∀ μ, (x μ).val / ell ^ j = (y μ).val / ell ^ j := by
      intro μ
      obtain ⟨c, hc⟩ := hyg μ
      have h2 : (y μ).val / ell ^ j = c := by rw [hc]; exact Nat.mul_div_cancel_left _ he
      have := hyx μ
      rw [h2]
      rw [hc] at this
      exact Nat.div_eq_of_lt_le (by nlinarith [this.1]) (by nlinarith [this.2])
    refine ⟨floorSite (ell ^ j) x', ?_, ?_⟩
    · refine hWb y hy _ (fun μ => by
        rw [floorSite_val]; exact dvd_mul_left _ _) ?_
      intro μ
      rw [floorSite_val, Nat.mul_div_cancel _ he, div_div_comm', ← hxe μ, div_div_comm']
      exact hx' μ
    · intro μ
      rw [floorSite_val]
      exact ⟨Nat.div_mul_le_self _ _, Nat.lt_div_mul_add he⟩

/-! ## the Omega_0 clause of the frozen definition = the printed set -/

theorem om0clause_iff_print {M R : ℕ} (hM : 0 < M) (Om0 Om1 : Set (PeriodicLatticeSite L)) :
    (∀ x : PeriodicLatticeSite L, x ∈ Om0 ↔
      ∃ y ∈ Om1, ∃ z : PeriodicLatticeSite L,
        (∀ μ : Fin 3, (z μ).val / M = (x μ).val / M) ∧ pdist z y ≤ R * M) ↔
    Om0 = Om0Print M R Om1 := by
  constructor
  · intro h
    ext x
    rw [h x]
    constructor
    · rintro ⟨y, hy, z, hz, hd⟩
      refine ⟨BigBlockCell M (fun μ => (x μ).val / M), ⟨_, rfl⟩, ⟨z, fun μ => hz μ, y, hy, hd⟩, fun μ => rfl⟩
    · rintro ⟨A, ⟨b, rfl⟩, ⟨z, hz, y, hy, hd⟩, hx⟩
      exact ⟨y, hy, z, fun μ => by rw [hz μ, hx μ], hd⟩
  · intro h x
    rw [h]
    constructor
    · rintro ⟨A, ⟨b, rfl⟩, ⟨z, hz, y, hy, hd⟩, hx⟩
      exact ⟨y, hy, z, fun μ => by rw [hz μ, hx μ], hd⟩
    · rintro ⟨y, hy, z, hz, hd⟩
      exact ⟨BigBlockCell M (fun μ => (x μ).val / M), ⟨_, rfl⟩, ⟨z, fun μ => hz μ, y, hy, hd⟩, fun μ => rfl⟩

theorem collar_iff_rat {ell : ℕ} (hell : 0 < ell) (j : ℕ) (R M d : ℕ) :
    R * bigSide M ell j < d ↔ ((R * M : ℕ) : ℚ) < (d : ℚ) / ((ell : ℚ) ^ j) := by
  have hpos : (0 : ℚ) < (ell : ℚ) ^ j := pow_pos (by exact_mod_cast hell) j
  rw [lt_div_iff₀ hpos]
  have : ((R * bigSide M ell j : ℕ) : ℚ) = ((R * M : ℕ) : ℚ) * (ell : ℚ) ^ j := by
    unfold bigSide; push_cast; ring
  rw [← this]; exact_mod_cast Iff.rfl

/-! ## MAIN: the frozen `Admissible` is the printed (2.1),(2.2) at the same `R`, with `T_1 = T_{L^{-0}}` -/

theorem admissible_iff_print {ell M R k : ℕ} (hell : 0 < ell) (hM : 0 < M) (S : Tower L) :
    Admissible ell M R k S ↔ PrintedTower ell M R k S ∧ PadAbove k S := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨⟨fun j _ => h1 j, h2 (k + 1) (by omega), h3, ?_, ?_, ?_⟩, h2⟩
    · intro j hj; exact (blockClosed_iff_sum hell hM _).1 (h4 j hj)
    · intro j hj x hx y hy
      exact (collar_iff_rat hell j R M _).1 (h5 j hj x hx y hy)
    · exact (om0clause_iff_print hM _ _).1 h6
  · rintro ⟨⟨h1, -, h3, h4, h5, h6⟩, h2⟩
    refine ⟨?_, h2, h3, ?_, ?_, (om0clause_iff_print hM _ _).2 h6⟩
    · intro j
      by_cases hj : j ≤ k
      · exact h1 j hj
      · rw [h2 (j + 1) (by omega)]; exact Set.empty_subset _
    · intro j hj; exact (blockClosed_iff_sum hell hM _).2 (h4 j hj)
    · intro j hj x hx y hy
      exact (collar_iff_rat hell j R M _).2 (h5 j hj x hx y hy)

end AdalyFormal.RBridge
