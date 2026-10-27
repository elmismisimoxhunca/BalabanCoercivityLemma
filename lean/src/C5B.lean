import C5A

/-!
# C5B -- the cubes `tilde-square^n` (p.408) and their geometry on the torus.

`cubeR c r` = sites `y` with, in every coordinate, `y = c + t (mod N)` for some integer `t in [-r, r)`; i.e. the periodic cube of side `2r`
centred at the grid point `c` (half-open, so that it is a union of `(2r/g)^3` blocks of side `g` when `g | r`).
`tildeCube n g c = cubeR c ((1+n)*g)` is the print's `tilde-square^n` (side `(2+2n) g`, same centre as `D_j` cube `square = tildeCube 0 g c`
= side `2 g` = `2^3` big blocks of side `g = M ell^j`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409C5

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.P409W

variable {L : PeriodicLatticeExtent}

/-- periodic cube of radius `r` (side `2 r`, half-open) centred at `c`. -/
def cubeR (c : PeriodicLatticeSite L) (r : ℕ) : Set (PeriodicLatticeSite L) :=
  {y | ∀ μ : Fin 3, ∃ t : ℤ, -(r : ℤ) ≤ t ∧ t < (r : ℤ) ∧
      ((y μ).val : ℤ) ≡ ((c μ).val : ℤ) + t [ZMOD ((L μ + 1 : ℕ) : ℤ)]}

/-- p.408: `tilde-square^n` has size `(2+2n) M L^j eta` and the centre of the `D_j` cube `square`; `g = M ell^j` fine sites. -/
def tildeCube (n g : ℕ) (c : PeriodicLatticeSite L) : Set (PeriodicLatticeSite L) := cubeR c ((1 + n) * g)

/-- the `D_j` cube `square` itself (`n = 0`: side `2 g`, a union of `2^3` big blocks). -/
def dCube (g : ℕ) (c : PeriodicLatticeSite L) : Set (PeriodicLatticeSite L) := tildeCube 0 g c

/-- **the cube of p.409**: `tilde-square^5`, side `12 g = (2+2*5) g`, `l^inf` radius `6 g`, centre `c`. -/
def printedCube5 (g : ℕ) (c : PeriodicLatticeSite L) : Set (PeriodicLatticeSite L) := tildeCube 5 g c

theorem tildeCube_side (n g : ℕ) : 2 * ((1 + n) * g) = (2 + 2 * n) * g := by ring

theorem cubeR_mono {c : PeriodicLatticeSite L} {r r' : ℕ} (h : r ≤ r') : cubeR c r ⊆ cubeR c r' := by
  intro y hy μ
  obtain ⟨t, h1, h2, h3⟩ := hy μ
  exact ⟨t, by omega, by omega, h3⟩

/-- circular distance is at most the absolute value of any integer representative of the offset. -/
theorem pcd_cong (N a b : ℕ) (hN : 0 < N) (ha : a < N) (hb : b < N) (t : ℤ)
    (h : (b : ℤ) ≡ (a : ℤ) + t [ZMOD (N : ℤ)]) : pcd N a b ≤ t.natAbs := by
  obtain ⟨q, hq⟩ := Int.modEq_iff_dvd.1 h.symm
  have hp2 : 2 * pcd N a b ≤ N := by unfold pcd; split_ifs <;> omega
  by_cases ht : N ≤ 2 * t.natAbs
  · omega
  · push Not at ht
    have hq1 : q < 2 := by
      by_contra hc
      push Not at hc
      have : (N : ℤ) * 2 ≤ (N : ℤ) * q := by nlinarith
      omega
    have hq2 : -2 < q := by
      by_contra hc
      push Not at hc
      have : (N : ℤ) * q ≤ (N : ℤ) * (-2) := by nlinarith
      omega
    unfold pcd
    interval_cases q <;> split_ifs <;> omega

theorem cube_dist {c x y : PeriodicLatticeSite L} {r1 r2 : ℕ} (hx : x ∈ cubeR c r1) (hy : y ∈ cubeR c r2) :
    pdist x y ≤ 3 * (r1 + r2) := by
  have key : ∀ μ : Fin 3, pcd (L μ + 1) (x μ).val (y μ).val ≤ r1 + r2 := by
    intro μ
    obtain ⟨t1, h11, h12, h13⟩ := hx μ
    obtain ⟨t2, h21, h22, h23⟩ := hy μ
    have hc : ((y μ).val : ℤ) ≡ ((x μ).val : ℤ) + (t2 - t1) [ZMOD ((L μ + 1 : ℕ) : ℤ)] := by
      have h13' : ((c μ).val : ℤ) + t1 ≡ ((x μ).val : ℤ) [ZMOD ((L μ + 1 : ℕ) : ℤ)] := h13.symm
      have e : ((c μ).val : ℤ) + t2 = ((c μ).val : ℤ) + t1 + (t2 - t1) := by ring
      rw [e] at h23
      exact h23.trans (Int.ModEq.add_right (t2 - t1) h13')
    have := pcd_cong (L μ + 1) (x μ).val (y μ).val (Nat.succ_pos _) (x μ).isLt (y μ).isLt (t2 - t1) hc
    omega
  unfold pdist
  rw [Fin.sum_univ_three]
  have := key 0; have := key 1; have := key 2
  omega

/-- shifting a site of the cube `cubeR c g` by `+-g` in one coordinate stays in `cubeR c r` when `2 g <= r`. -/
theorem sh_mem_cube {c x : PeriodicLatticeSite L} {g r : ℕ} (hx : x ∈ cubeR c g) (hgr : 2 * g ≤ r)
    (μ : Fin 3) (s : ℕ) (hs : s = g ∨ s + g = L μ + 1) : sh x μ s ∈ cubeR c r := by
  intro ν
  by_cases hν : ν = μ
  · subst hν
    obtain ⟨t, h1, h2, h3⟩ := hx ν
    have hmod : (((sh x ν s) ν).val : ℤ) ≡ ((x ν).val : ℤ) + (s : ℤ) [ZMOD ((L ν + 1 : ℕ) : ℤ)] := by
      rw [sh_self]
      have := Int.natCast_modEq_iff.2 (Nat.mod_modEq ((x ν).val + s) (L ν + 1))
      push_cast at this
      exact this
    rcases hs with rfl | hs
    · refine ⟨t + s, by omega, by omega, ?_⟩
      have := hmod.trans (Int.ModEq.add_right (s : ℤ) h3)
      have e : ((c ν).val : ℤ) + t + (s : ℤ) = ((c ν).val : ℤ) + (t + s) := by ring
      rwa [e] at this
    · refine ⟨t - g, by omega, by omega, ?_⟩
      have h4 : ((x ν).val : ℤ) + (s : ℤ) ≡ ((x ν).val : ℤ) + (-(g : ℤ)) [ZMOD ((L ν + 1 : ℕ) : ℤ)] := by
        apply Int.modEq_iff_dvd.2
        refine ⟨-1, ?_⟩
        push_cast
        omega
      have := (hmod.trans h4).trans (Int.ModEq.add_right (-(g : ℤ)) h3)
      have e : ((c ν).val : ℤ) + t + -(g : ℤ) = ((c ν).val : ℤ) + (t - g) := by ring
      rwa [e] at this
  · rw [sh_ne x μ ν s hν]
    exact cubeR_mono (by omega) hx ν

/-- the periodic box corner `c - r`. -/
def zsite (c : PeriodicLatticeSite L) (r : ℕ) : PeriodicLatticeSite L := fun μ =>
  ⟨((c μ).val + (L μ + 1) * r - r) % (L μ + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem cubeR_box (c : PeriodicLatticeSite L) (r : ℕ) : cubeR c r ⊆ siteBox (zsite c r) (2 * r) := by
  intro y hy μ
  obtain ⟨t, h1, h2, h3⟩ := hy μ
  set N := L μ + 1 with hN
  have hNpos : 0 < N := Nat.succ_pos _
  have hrle : r ≤ (c μ).val + N * r := by nlinarith
  have hz : (((zsite c r) μ).val : ℤ) ≡ ((c μ).val : ℤ) + (N : ℤ) * r - r [ZMOD (N : ℤ)] := by
    show ((((c μ).val + N * r - r) % N : ℕ) : ℤ) ≡ _ [ZMOD (N : ℤ)]
    have := Int.natCast_modEq_iff.2 (Nat.mod_modEq ((c μ).val + N * r - r) N)
    rw [Nat.cast_sub hrle] at this
    push_cast at this
    exact this
  have hzlt : ((zsite c r) μ).val < N := ((zsite c r) μ).isLt
  have hm : (((y μ).val + N - ((zsite c r) μ).val : ℕ) : ℤ) ≡ (((t + r).toNat : ℕ) : ℤ) [ZMOD (N : ℤ)] := by
    have e1 : (((y μ).val + N - ((zsite c r) μ).val : ℕ) : ℤ) = ((y μ).val : ℤ) + (N : ℤ) - (((zsite c r) μ).val : ℤ) := by
      push_cast [Nat.cast_sub (show ((zsite c r) μ).val ≤ (y μ).val + N by omega)]
      ring
    have e2 : (((t + r).toNat : ℕ) : ℤ) = t + r := by omega
    rw [e1, e2]
    have h5 : ((y μ).val : ℤ) + (N : ℤ) - (((zsite c r) μ).val : ℤ) ≡
        (((c μ).val : ℤ) + t) + (N : ℤ) - (((c μ).val : ℤ) + (N : ℤ) * r - r) [ZMOD (N : ℤ)] :=
      ((h3.add_right (N : ℤ)).sub hz)
    refine h5.trans ?_
    have e3 : (((c μ).val : ℤ) + t) + (N : ℤ) - (((c μ).val : ℤ) + (N : ℤ) * r - r) = (t + r) + (N : ℤ) * (1 - r) := by ring
    rw [e3]
    exact Int.modEq_iff_dvd.2 ⟨-(1 - (r : ℤ)), by ring⟩
  have hn := Int.natCast_modEq_iff.1 hm
  have hle : ((t + r).toNat) % N ≤ (t + r).toNat := Nat.mod_le _ _
  show ((y μ).val + N - ((zsite c r) μ).val) % N < 2 * r
  have : ((y μ).val + N - ((zsite c r) μ).val) % N = ((t + r).toNat) % N := hn
  omega

theorem zsite_dvd (c : PeriodicLatticeSite L) (r gi : ℕ) (hN : ∀ μ : Fin 3, gi ∣ L μ + 1)
    (hc : ∀ μ : Fin 3, gi ∣ (c μ).val) (hr : gi ∣ r) (μ : Fin 3) : gi ∣ ((zsite c r) μ).val := by
  show gi ∣ ((c μ).val + (L μ + 1) * r - r) % (L μ + 1)
  refine (Nat.dvd_mod_iff (hN μ)).2 ?_
  exact Nat.dvd_sub (dvd_add (hc μ) (Dvd.dvd.mul_right (hN μ) r)) hr

/-- a periodic box whose corner and side are multiples of `gi` is closed under level-`gi` blocks. -/
theorem siteBox_closed {z x y : PeriodicLatticeSite L} {gi s : ℕ} (hgi : 0 < gi) (hN : ∀ μ : Fin 3, gi ∣ L μ + 1)
    (hz : ∀ μ : Fin 3, gi ∣ (z μ).val) (hs : gi ∣ s) (hx : x ∈ siteBox z s)
    (hxy : ∀ μ : Fin 3, (y μ).val / gi = (x μ).val / gi) : y ∈ siteBox z s := by
  intro μ
  have hxμ := hx μ
  have hzlt := (z μ).isLt
  have hd : gi ∣ (L μ + 1) - (z μ).val := Nat.dvd_sub (hN μ) (hz μ)
  have key := div_shift gi (L μ + 1) (y μ).val (x μ).val ((L μ + 1) - (z μ).val) hgi (hN μ) hd (hxy μ)
  have e1 : (y μ).val + (L μ + 1) - (z μ).val = (y μ).val + ((L μ + 1) - (z μ).val) := by omega
  have e2 : (x μ).val + (L μ + 1) - (z μ).val = (x μ).val + ((L μ + 1) - (z μ).val) := by omega
  rw [e2] at hxμ
  rw [e1]
  obtain ⟨m, hm⟩ := hs
  set u := ((y μ).val + ((L μ + 1) - (z μ).val)) % (L μ + 1)
  set u' := ((x μ).val + ((L μ + 1) - (z μ).val)) % (L μ + 1)
  have hdiv : u / gi < m := by
    rw [key, Nat.div_lt_iff_lt_mul hgi]
    rw [hm] at hxμ
    nlinarith
  rw [hm]
  exact (Nat.div_lt_iff_lt_mul hgi).1 hdiv |> fun h => by nlinarith

end AdalyFormal.P409C5
