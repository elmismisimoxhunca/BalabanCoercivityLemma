import CvOK7
import CvNe3

/-!
# CvOG1 -- the row geometry of the nested instance: regions, row lengths, the tiling recursion (lane omega)

Regions of the `x₀`-axis of the nested tower (`neP0 < neP1 < neA' < neB' < neA < neB < neQ1 < neQ0`):
* `reg0`: collar `[P0,P1) ∪ [Q1,Q0)` (level-0 rows, singletons),
* `reg2`: `[A',B') ∪ [A,B)` (level-2 rows of length `ell²`),
* `reg1`: `[P1,Q1) \ reg2` (level-1 rows of length `ell`).
`rowLenN v` is the row length at slice `v`; the row starts are `P0, P0 + len, ...` (recursion `stN`).  `tile_step` shows the recursion tiles `[P0,Q0)` by aligned blocks.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open AdalyFormal.CoverNested

section geo

variable (ell M R : ℕ)

def reg0 (v : ℕ) : Prop := (neP0 ell M R ≤ v ∧ v < neP1 ell M R) ∨ (neQ1 ell M R ≤ v ∧ v < neQ0 ell M R)
def reg2 (v : ℕ) : Prop := (neA' ell M R ≤ v ∧ v < neB' ell M R) ∨ (neA ell M R ≤ v ∧ v < neB ell M R)
def reg1 (v : ℕ) : Prop := (neP1 ell M R ≤ v ∧ v < neQ1 ell M R) ∧ ¬ reg2 ell M R v

/-- `isRowN j v`: `v` is the start of a level-`j` row. -/
def isRowN : ℕ → ℕ → Prop
  | 0, v => reg0 ell M R v
  | 1, v => ell ∣ v ∧ reg1 ell M R v
  | 2, v => ell ^ 2 ∣ v ∧ reg2 ell M R v
  | _, _ => False

open Classical in
noncomputable def rowLenN (v : ℕ) : ℕ := if reg0 ell M R v then 1 else if reg2 ell M R v then ell ^ 2 else ell

/-- the chain length. -/
def nN : ℕ := neQ0 ell M R - neP0 ell M R

/-- starts of the rows (relative to `P0`). -/
noncomputable def stN : ℕ → ℕ
  | 0 => 0
  | i + 1 => stN i + rowLenN ell M R (neP0 ell M R + stN i)

end geo

variable {ell M R : ℕ}

/-- all the numeric facts used by the tiling. -/
structure NGeo (ell M R : ℕ) : Prop where
  hell : 2 ≤ ell
  hdell : ell ∣ M
  hP0P1 : neP0 ell M R < neP1 ell M R
  hP1A : neP1 ell M R < neA' ell M R
  hAB' : neA' ell M R < neB' ell M R
  hB'A : neB' ell M R < neA ell M R
  hAB : neA ell M R < neB ell M R
  hBQ1 : neB ell M R < neQ1 ell M R
  hQ1Q0 : neQ1 ell M R < neQ0 ell M R
  dP1 : ell ∣ neP1 ell M R
  dQ1 : ell ∣ neQ1 ell M R
  dA' : ell ^ 2 ∣ neA' ell M R
  dB' : ell ^ 2 ∣ neB' ell M R
  dA : ell ^ 2 ∣ neA ell M R
  dB : ell ^ 2 ∣ neB ell M R
  dB'l : ell ∣ neB' ell M R
  dAl : ell ∣ neA ell M R
  dBl : ell ∣ neB ell M R
  dA'l : ell ∣ neA' ell M R
  cP : neP1 ell M R = neP0 ell M R + R * M
  cQ : neQ0 ell M R = neQ1 ell M R + R * M
  cRM : 1 ≤ R * M

theorem nGeo (hell : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) : NGeo ell M R := by
  have G := ne_geo3 hell hM hR
  obtain ⟨-, -, w2, gap, w2', QN, d0, d1, d2, b0P, b0Q, b1P, b1Q, b2A', b2B', b2A, b2B, cP, cQ, cP2, cQ2⟩ := G
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin hell hM hR
  have h1 : ∀ x, M * ell ∣ x → ell ∣ x := fun x hx => dvd_trans (Dvd.intro_left M rfl) hx
  have h2 : ∀ x, M * ell ^ 2 ∣ x → ell ^ 2 ∣ x := fun x hx => dvd_trans (Dvd.intro_left M rfl) hx
  have h2' : ∀ x, ell ^ 2 ∣ x → ell ∣ x := fun x hx => dvd_trans (dvd_pow_self ell (by norm_num)) hx
  refine ⟨by omega, hdvd, ?_, ?_, w2, ne_gap_pos hell hM hR, w2', ?_, ?_, h1 _ b1P, h1 _ b1Q, h2 _ b2A', h2 _ b2B', h2 _ b2A, h2 _ b2B,
    h2' _ (h2 _ b2B'), h2' _ (h2 _ b2A), h2' _ (h2 _ b2B), h2' _ (h2 _ b2A'), cP, cQ, by simpa using Nat.mul_le_mul hR hM⟩
  · simp only [neP0, neP1, neA']; omega
  · simp only [neP1, neA']; omega
  · simp only [neB, neQ1]; omega
  · simp only [neQ1, neQ0]; omega

#print axioms nGeo

end AdalyFormal.CoverOmega
