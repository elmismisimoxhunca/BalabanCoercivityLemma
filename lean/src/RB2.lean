import RB1

/-!
# RB2 -- the readings of the p.396 base law and what each does to `R`.

Readings of "`Omega_0 = {a union of big blocks of the lattice T_1, such that their distances to Omega_1 are <= RM}`":
* distance between sets of SITES, attained (`SetDistLe`)  -- the frozen clause (reading D1, <=, `T_1 = T_{L^{-0}}`)
* "all points of the block within RM" (`SetAllLe`)         -- reading D2
* strict `< RM` (`SetDistLt`)                              -- reading D4
* `T_1` = the unit lattice `Z^d ∩ T_eta` of level `k` (CMP95 p.20 `T_1^{(k)}`): blocks `M ell^k`, radius `R M ell^k` -- reading B.
All are compared with (2.2) at `j = 0`: `dist(Omega_0^c, Omega_1) > R M` (CMP99b p.393: "The condition (2.2) is unchanged").
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.RBridge

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.P409S

variable {L : PeriodicLatticeExtent}

/-- general base law: union of the `s`-blocks within `ρ` of `Om1`. -/
def Om0Rad (s ρ : ℕ) (Om1 : Set (PeriodicLatticeSite L)) : Set (PeriodicLatticeSite L) :=
  {x | ∃ A, IsBigBlock s A ∧ SetDistLe A Om1 ρ ∧ x ∈ A}

theorem om0Print_eq_rad (M R : ℕ) (Om1 : Set (PeriodicLatticeSite L)) :
    Om0Print M R Om1 = Om0Rad M (R * M) Om1 := rfl

/-- reading D2. -/
def Om0All (M R : ℕ) (Om1 : Set (PeriodicLatticeSite L)) : Set (PeriodicLatticeSite L) :=
  {x | ∃ A, IsBigBlock M A ∧ SetAllLe A Om1 (R * M) ∧ x ∈ A}

/-- reading D4. -/
def Om0Lt (M R : ℕ) (Om1 : Set (PeriodicLatticeSite L)) : Set (PeriodicLatticeSite L) :=
  {x | ∃ A, IsBigBlock M A ∧ SetDistLt A Om1 (R * M) ∧ x ∈ A}

/-- reading B (`T_1` = the level-`k` unit lattice). -/
def Om0Unit (ell M R k : ℕ) (Om1 : Set (PeriodicLatticeSite L)) : Set (PeriodicLatticeSite L) :=
  Om0Rad (M * ell ^ k) (R * (M * ell ^ k)) Om1

/-- (2.2) at `j = 0`: `dist(Omega^c, Omega_1) > R M` (a pair statement; the infimum is attained). -/
def Collar0 (M R : ℕ) (Ω Om1 : Set (PeriodicLatticeSite L)) : Prop :=
  ∀ x : PeriodicLatticeSite L, x ∉ Ω → ∀ y ∈ Om1, R * M < pdist x y

theorem cell_mem_iff {s : ℕ} {b : Fin 3 → ℕ} {x : PeriodicLatticeSite L} :
    x ∈ BigBlockCell (L := L) s b ↔ ∀ μ, (x μ).val / s = b μ := Iff.rfl

theorem block_closed_of_mem {s : ℕ} {A : Set (PeriodicLatticeSite L)} (hA : IsBigBlock s A)
    {x x' : PeriodicLatticeSite L} (hx : x ∈ A) (hx' : x' ∈ A) :
    ∀ μ, (x' μ).val / s = (x μ).val / s := by
  obtain ⟨b, rfl⟩ := hA
  intro μ; rw [hx' μ, hx μ]

theorem om0Rad_blockClosed (s ρ : ℕ) (Om1 : Set (PeriodicLatticeSite L)) :
    BlockClosed s (Om0Rad s ρ Om1) := by
  rintro x ⟨A, hA, hd, hx⟩ x' hx'
  refine ⟨BigBlockCell s (fun μ => (x μ).val / s), ⟨_, rfl⟩, ?_, fun μ => hx' μ⟩
  obtain ⟨b, rfl⟩ := hA
  obtain ⟨z, hz, y, hy, hdz⟩ := hd
  refine ⟨z, fun μ => (hz μ).trans (hx μ).symm, y, hy, hdz⟩

theorem pdist_self' (x : PeriodicLatticeSite L) : pdist x x = 0 := by
  unfold pdist pcd
  simp

theorem om1_sub_om0Print {M R : ℕ} (Om1 : Set (PeriodicLatticeSite L)) :
    Om1 ⊆ Om0Print M R Om1 := by
  intro y hy
  refine ⟨BigBlockCell M (fun μ => (y μ).val / M), ⟨_, rfl⟩, ⟨y, fun μ => rfl, y, hy, ?_⟩, fun μ => rfl⟩
  rw [pdist_self']; exact Nat.zero_le _

/-- the printed `Omega_0` satisfies (2.2) at `j = 0` (strict collar). -/
theorem om0Print_collar {M R : ℕ} (Om1 : Set (PeriodicLatticeSite L)) :
    Collar0 M R (Om0Print M R Om1) Om1 := by
  intro x hx y hy
  by_contra hle
  rw [not_lt] at hle
  exact hx ⟨BigBlockCell M (fun μ => (x μ).val / M), ⟨_, rfl⟩, ⟨x, fun μ => rfl, y, hy, hle⟩, fun μ => rfl⟩

/-- the printed `Omega_0` is the LEAST block-closed set that satisfies (2.2) at `j = 0`. -/
theorem om0Print_least {M R : ℕ} {Om1 Ω : Set (PeriodicLatticeSite L)}
    (hbc : BlockClosed M Ω) (hcol : Collar0 M R Ω Om1) : Om0Print M R Om1 ⊆ Ω := by
  rintro x ⟨A, hA, ⟨z, hz, y, hy, hd⟩, hx⟩
  have hzΩ : z ∈ Ω := by
    by_contra hnot
    exact absurd (hcol z hnot y hy) (not_lt.2 hd)
  exact hbc z hzΩ x (fun μ => block_closed_of_mem hA hz hx μ)

/-- any block-closed `Ω` (for instance any reading that is a union of whole blocks) that does not contain the printed `Omega_0`
violates (2.2) at `j = 0`: the readings with a smaller `Omega_0` (all-points, strict, block-lattice distance) are excluded
by "(2.2) is unchanged" (CMP99b p.393). -/
theorem collar0_violated_of_not_sup {M R : ℕ} {Om1 Ω : Set (PeriodicLatticeSite L)}
    (hbc : BlockClosed M Ω) (hns : ¬ Om0Print M R Om1 ⊆ Ω) : ¬ Collar0 M R Ω Om1 :=
  fun h => hns (om0Print_least hbc h)

/-- characterisation: `Ω = printed Omega_0` iff `Ω` is block-closed, satisfies (2.2) at `j = 0`, and every block of `Ω`
has a site within `R M` of `Omega_1` (so `Ω` is the least such set, and is not larger). -/
theorem om0Print_char {M R : ℕ} {Om1 Ω : Set (PeriodicLatticeSite L)} :
    Ω = Om0Print M R Om1 ↔
      BlockClosed M Ω ∧ Collar0 M R Ω Om1 ∧
        ∀ x ∈ Ω, ∃ A, IsBigBlock M A ∧ x ∈ A ∧ SetDistLe A Om1 (R * M) := by
  constructor
  · rintro rfl
    exact ⟨om0Rad_blockClosed M (R * M) Om1, om0Print_collar Om1,
      fun x ⟨A, hA, hd, hx⟩ => ⟨A, hA, hx, hd⟩⟩
  · rintro ⟨hbc, hcol, hnear⟩
    refine Set.Subset.antisymm ?_ (om0Print_least hbc hcol)
    intro x hx
    obtain ⟨A, hA, hxA, hd⟩ := hnear x hx
    exact ⟨A, hA, hd, hxA⟩

/-! ### reading D2 (all points within RM) -/

theorem om0All_sub_print {M R : ℕ} (Om1 : Set (PeriodicLatticeSite L)) :
    Om0All M R Om1 ⊆ Om0Print M R Om1 := by
  rintro x ⟨A, hA, hall, hx⟩
  obtain ⟨y, hy, hd⟩ := hall x hx
  exact ⟨A, hA, ⟨x, hx, y, hy, hd⟩, hx⟩

theorem om0All_blockClosed (M R : ℕ) (Om1 : Set (PeriodicLatticeSite L)) :
    BlockClosed M (Om0All M R Om1) := by
  rintro x ⟨A, hA, hall, hx⟩ x' hx'
  refine ⟨BigBlockCell M (fun μ => (x μ).val / M), ⟨_, rfl⟩, ?_, fun μ => hx' μ⟩
  obtain ⟨b, rfl⟩ := hA
  intro z hz
  exact hall z (fun μ => (hz μ).trans (hx μ))

/-- under reading D2, (2.2) at `j = 0` holds only when the two readings coincide. -/
theorem om0All_collar_imp_eq {M R : ℕ} {Om1 : Set (PeriodicLatticeSite L)}
    (h : Collar0 M R (Om0All M R Om1) Om1) : Om0All M R Om1 = Om0Print M R Om1 :=
  Set.Subset.antisymm (om0All_sub_print Om1) (om0Print_least (om0All_blockClosed M R Om1) h)

/-! ### reading D4 (strict) -/

theorem om0Lt_sub_print {M R : ℕ} (Om1 : Set (PeriodicLatticeSite L)) :
    Om0Lt M R Om1 ⊆ Om0Print M R Om1 := by
  rintro x ⟨A, hA, ⟨z, hz, y, hy, hd⟩, hx⟩
  exact ⟨A, hA, ⟨z, hz, y, hy, hd.le⟩, hx⟩

theorem om0Lt_blockClosed (M R : ℕ) (Om1 : Set (PeriodicLatticeSite L)) :
    BlockClosed M (Om0Lt M R Om1) := by
  rintro x ⟨A, hA, ⟨z, hz, y, hy, hdz⟩, hx⟩ x' hx'
  refine ⟨BigBlockCell M (fun μ => (x μ).val / M), ⟨_, rfl⟩, ?_, fun μ => hx' μ⟩
  obtain ⟨b, rfl⟩ := hA
  exact ⟨z, fun μ => (hz μ).trans (hx μ).symm, y, hy, hdz⟩

theorem om0Lt_collar_imp_eq {M R : ℕ} {Om1 : Set (PeriodicLatticeSite L)}
    (h : Collar0 M R (Om0Lt M R Om1) Om1) : Om0Lt M R Om1 = Om0Print M R Om1 :=
  Set.Subset.antisymm (om0Lt_sub_print Om1) (om0Print_least (om0Lt_blockClosed M R Om1) h)

/-- the strict reading is the printed reading at radius `R M - 1` (not of the form `R' M`). -/
theorem om0Lt_eq_rad {M R : ℕ} (hMR : 1 ≤ R * M) (Om1 : Set (PeriodicLatticeSite L)) :
    Om0Lt M R Om1 = Om0Rad M (R * M - 1) Om1 := by
  ext x
  constructor
  · rintro ⟨A, hA, ⟨z, hz, y, hy, hd⟩, hx⟩
    exact ⟨A, hA, ⟨z, hz, y, hy, by omega⟩, hx⟩
  · rintro ⟨A, hA, ⟨z, hz, y, hy, hd⟩, hx⟩
    exact ⟨A, hA, ⟨z, hz, y, hy, by omega⟩, hx⟩

/-! ### reading B (`T_1` = unit lattice of level `k`) -/

theorem om0Rad_mono {s s' ρ ρ' : ℕ} (hs : s ∣ s') (hs0 : 0 < s) (hρ : ρ ≤ ρ')
    (Om1 : Set (PeriodicLatticeSite L)) : Om0Rad s ρ Om1 ⊆ Om0Rad s' ρ' Om1 := by
  rintro x ⟨A, hA, ⟨z, hz, y, hy, hd⟩, hx⟩
  obtain ⟨q, rfl⟩ := hs
  refine ⟨BigBlockCell (s * q) (fun μ => (x μ).val / (s * q)), ⟨_, rfl⟩, ⟨z, ?_, y, hy, hd.trans hρ⟩, fun μ => rfl⟩
  intro μ
  have h := block_closed_of_mem hA hz hx μ
  show (z μ).val / (s * q) = (x μ).val / (s * q)
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h]

theorem om0Print_sub_unit {ell M R k : ℕ} (hell : 0 < ell) (hM : 0 < M) (Om1 : Set (PeriodicLatticeSite L)) :
    Om0Print M R Om1 ⊆ Om0Unit ell M R k Om1 := by
  rw [om0Print_eq_rad]
  refine om0Rad_mono ⟨ell ^ k, rfl⟩ hM ?_ Om1
  have : 1 ≤ ell ^ k := Nat.one_le_pow _ _ hell
  calc R * M = R * M * 1 := (mul_one _).symm
    _ ≤ R * M * ell ^ k := Nat.mul_le_mul_left _ this
    _ = R * (M * ell ^ k) := by ring

/-- matching the radius alone: radius `R_f M` equals `R_p (M ell^k)` when `R_f = ell^k R_p`. -/
theorem radius_rescale (ell M Rp k : ℕ) : (ell ^ k * Rp) * M = Rp * (M * ell ^ k) := by ring

/-! ### concrete witness that the readings differ (torus with 8 sites per direction, `M = 2`, `R = 1`, `Omega_1 = {0}`) -/

def Lw : PeriodicLatticeExtent := fun _ => 7

def zeroSite : PeriodicLatticeSite Lw := fun _ => 0

def Om1w : Set (PeriodicLatticeSite Lw) := {zeroSite}

def x200 : PeriodicLatticeSite Lw := fun μ => if μ = 0 then 2 else 0

def x311 : PeriodicLatticeSite Lw := fun μ => if μ = 0 then 3 else 1

theorem d200 : pdist x200 zeroSite = 2 := by
  unfold pdist pcd x200 zeroSite Lw; decide

theorem d311 : pdist x311 zeroSite = 5 := by
  unfold pdist pcd x311 zeroSite Lw; decide

theorem same_block_200_311 : ∀ μ : Fin 3, (x311 μ).val / 2 = (x200 μ).val / 2 := by
  intro μ; fin_cases μ <;> simp [x311, x200, Lw]

theorem x200_in_print : x200 ∈ Om0Print 2 1 Om1w :=
  ⟨BigBlockCell 2 (fun μ => (x200 μ).val / 2), ⟨_, rfl⟩,
    ⟨x200, fun μ => rfl, zeroSite, rfl, by rw [d200]⟩, fun μ => rfl⟩

theorem x200_not_in_all : x200 ∉ Om0All 2 1 Om1w := by
  rintro ⟨A, ⟨b, rfl⟩, hall, hx⟩
  have h311 : x311 ∈ BigBlockCell (L := Lw) 2 b := fun μ => by rw [← hx μ]; exact same_block_200_311 μ
  obtain ⟨y, hy, hd⟩ := hall x311 h311
  have : y = zeroSite := hy
  subst this
  rw [d311] at hd; omega

theorem x200_not_in_lt : x200 ∉ Om0Lt 2 1 Om1w := by
  rintro ⟨A, ⟨b, rfl⟩, ⟨z, hz, y, hy, hd⟩, hx⟩
  have hy' : y = zeroSite := hy
  subst hy'
  -- z in the block of x200 = {2,3} x {0,1} x {0,1}; every such z has pdist z 0 >= 2
  have hz0 : ∀ μ, (z μ).val / 2 = (x200 μ).val / 2 := fun μ => by rw [hz μ, ← hx μ]
  have c0 := hz0 0; have c1 := hz0 1; have c2 := hz0 2
  simp [x200, Lw] at c0 c1 c2
  have e0 := (z 0).isLt; have e1 := (z 1).isLt; have e2 := (z 2).isLt
  simp [Lw] at e0 e1 e2
  unfold pdist pcd zeroSite Lw at hd
  simp only [Fin.sum_univ_three] at hd
  simp only [Fin.val_zero] at hd
  split_ifs at hd <;> omega

theorem readings_differ :
    Om0All 2 1 Om1w ≠ Om0Print 2 1 Om1w ∧ Om0Lt 2 1 Om1w ≠ Om0Print 2 1 Om1w :=
  ⟨fun h => x200_not_in_all (h ▸ x200_in_print), fun h => x200_not_in_lt (h ▸ x200_in_print)⟩

/-- so on this instance both alternative readings violate (2.2) at `j = 0` (they are not the printed set, and the
printed set is the least block-closed set satisfying it). -/
theorem alt_readings_violate_collar0 :
    ¬ Collar0 2 1 (Om0All 2 1 Om1w) Om1w ∧ ¬ Collar0 2 1 (Om0Lt 2 1 Om1w) Om1w :=
  ⟨fun h => readings_differ.1 (om0All_collar_imp_eq h), fun h => readings_differ.2 (om0Lt_collar_imp_eq h)⟩

end AdalyFormal.RBridge
