import NMX1b

/-!
# NMX1c -- a factor above the left width does not cover alone (lane nonvac_mixed_20261017)

Helpers `pmod`, `upd0`, `upd0_mem` (membership of the site with coordinate 0 replaced).
`mx_not_covers`: for `g > w = R + ell q` the site `x₀ = P₀` (a site of `B⁰` on the far left) lies in no class cube of factor `g`
(a class cube through it has index `0`, is a periodic box of side `g M` in `x₀`; it cannot start before `P₀` (the site `P₀-1 ∉ Ω₀`)
nor end after `P₂ - 1` (the site `P₂ ∈ Ω₂` is not in `B⁰ ∪ B¹`), but `P₂ - P₀ = w M < g M`).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.NonVacMix

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.NonVacC

theorem pmod {N a z : ℕ} (haN : a < N) (hzN : z < N) :
    (a + N - z) % N = if z ≤ a then a - z else a + N - z := by
  split_ifs with h
  · have : a + N - z = (a - z) + N := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- the site obtained from `z` by replacing coordinate 0 with `v`. -/
def upd0 {L : PeriodicLatticeExtent} {N : ℕ} (hN : ∀ μ, L μ + 1 = N) (z : PeriodicLatticeSite L) (v : ℕ) (hv : v < N) :
    PeriodicLatticeSite L := Function.update z 0 ⟨v, by rw [hN 0]; exact hv⟩

theorem upd0_mem {L : PeriodicLatticeExtent} {N : ℕ} (hN : ∀ μ, L μ + 1 = N) (z : PeriodicLatticeSite L) (v : ℕ) (hv : v < N)
    {s : ℕ} (hs : 0 < s) :
    upd0 hN z v hv ∈ siteBox z s ↔ (v + N - (z 0).val) % N < s := by
  rw [mem_box_N hN]
  have h0 : (upd0 hN z v hv 0).val = v := by simp [upd0]
  have h1 : upd0 hN z v hv 1 = z 1 := by simp [upd0]
  have h2 : upd0 hN z v hv 2 = z 2 := by simp [upd0]
  have hz1 : (z 1).val < N := by have := (z 1).isLt; have := hN 1; omega
  have hz2 : (z 2).val < N := by have := (z 2).isLt; have := hN 2; omega
  have hN0 : 0 < N := by have := (z 0).isLt; have := hN 0; omega
  have e1 : ((z 1).val + N - (z 1).val) % N = 0 := by
    have : (z 1).val + N - (z 1).val = N := by omega
    rw [this, Nat.mod_self]
  have e2 : ((z 2).val + N - (z 2).val) % N = 0 := by
    have : (z 2).val + N - (z 2).val = N := by omega
    rw [this, Nat.mod_self]
  rw [h0, h1, h2, e1, e2]
  simp [hs]

section noncov
variable {ell M R T q : ℕ}

theorem mx_not_covers (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (hq : R ≤ q) (hT : 1 ≤ T)
    (hwT : R + ell * q ≤ T) {g : ℕ} (hg : R + ell * q < g) :
    ¬ CoversOm0c ell M g 2 (mxS (scaleUp ell 2 (nvcLu M T)) ell M R T q) := by
  intro hcov
  have hell0 : 0 < ell := by omega
  have hN : ∀ μ, scaleUp ell 2 (nvcLu M T) μ + 1 = nvcN ell M T := fun μ => scaleUp_nvc hell0 hM μ
  have G := slabGeo_mix hell hdvd hM hR hq hT hwT
  have hnest := (slab3_admissible G hN).1
  obtain ⟨d, t, hd, hdd, ht, hdt, hw2, hRw⟩ := mx_left_facts hell hR hq
  have g1 := G.nest01; have g2 := G.nest12; have g3 := G.nestw; have g4 := G.nest21; have g5 := G.nest10
  have g6 := G.QN; have g7 := G.c0P
  have hRM : 0 < R * M := Nat.mul_pos (by omega) hM
  have hP0pos : 1 ≤ mxP0 ell M R q := by
    simp only [mxP0, hdd]
    have : 3 ≤ d := by nlinarith
    have : 1 ≤ d * (R + ell * q) := by nlinarith
    nlinarith
  -- W = M * w
  obtain ⟨W, hW⟩ : ∃ W, W = M * (R + ell * q) := ⟨_, rfl⟩
  have hP20 : mxP2 ell M R q = mxP0 ell M R q + W := by
    simp only [mxP0, mxP2, hdd, hW]
    have e2 : M * ell ^ 2 * (R + ell * q) = M * ((d + 1) * (R + ell * q)) := by rw [← hd]; ring
    rw [e2]; ring
  have hWg : W < g * M := by rw [hW, mul_comm M]; exact Nat.mul_lt_mul_of_pos_right hg hM
  have hP0N : mxP0 ell M R q < nvcN ell M T := by omega
  have hP2N : mxP2 ell M R q < nvcN ell M T := by omega
  have hPm1N : mxP0 ell M R q - 1 < nvcN ell M T := by omega
  let x : PeriodicLatticeSite (scaleUp ell 2 (nvcLu M T)) := siteAt0 (T := T) hell0 hM (mxP0 ell M R q) hP0N
  have hx0 : (x 0).val = mxP0 ell M R q := siteAt0_val hell0 hM _ hP0N
  have hxOm : x ∈ (mxS (scaleUp ell 2 (nvcLu M T)) ell M R T q).Om 0 := by
    unfold mxS; rw [om0_mem, hx0]; omega
  obtain ⟨sites, j, hcl, hxs⟩ := hcov x hxOm
  obtain ⟨⟨hj, ⟨z, hz, hsites⟩, hsub, hne⟩, huniq⟩ := hcl
  have hxB0 : x ∈ towerBj (mxS (scaleUp ell 2 (nvcLu M T)) ell M R T q) 0 := by
    unfold mxS; rw [bj0, hx0]; omega
  have hj0 : j = 0 := by
    rcases hsub hxs with h | h
    · exact (bj_eq hnest hxB0 h).symm
    · have := bj_eq hnest hxB0 h; omega
  subst hj0
  have hbs : bigSide M ell 0 = M := by simp [bigSide]
  rw [hbs] at hsites
  have hs : 0 < g * M := Nat.mul_pos (by omega) hM
  have hzN : (z 0).val < nvcN ell M T := by have := (z 0).isLt; have := hN 0; omega
  rw [hsites] at hxs
  -- x in the box
  have hxmem : (mxP0 ell M R q + nvcN ell M T - (z 0).val) % nvcN ell M T < g * M := by
    have := (mem_box_N hN z x (g * M)).1 hxs |>.1
    rwa [hx0] at this
  -- the site P0 - 1 is not in the cube
  have hy1 : upd0 hN z (mxP0 ell M R q - 1) hPm1N ∉ siteBox z (g * M) := by
    intro hy
    have hys : upd0 hN z (mxP0 ell M R q - 1) hPm1N ∈ sites := by rw [hsites]; exact hy
    rcases hsub hys with h | h
    · have := h.1
      unfold mxS at this; rw [om0_mem] at this
      have h0 : (upd0 hN z (mxP0 ell M R q - 1) hPm1N 0).val = mxP0 ell M R q - 1 := by simp [upd0]
      omega
    · have := h.1
      unfold mxS at this; rw [om1_mem] at this
      have h0 : (upd0 hN z (mxP0 ell M R q - 1) hPm1N 0).val = mxP0 ell M R q - 1 := by simp [upd0]
      omega
  have hy2 : upd0 hN z (mxP2 ell M R q) hP2N ∉ siteBox z (g * M) := by
    intro hy
    have hys : upd0 hN z (mxP2 ell M R q) hP2N ∈ sites := by rw [hsites]; exact hy
    have h0 : (upd0 hN z (mxP2 ell M R q) hP2N 0).val = mxP2 ell M R q := by simp [upd0]
    rcases hsub hys with h | h
    · have := h.2
      unfold mxS at this; rw [om1_mem] at this
      apply this; rw [h0]; omega
    · have := h.2
      unfold mxS at this; rw [om2_mem] at this
      apply this; rw [h0]; omega
  rw [upd0_mem hN z _ hPm1N hs] at hy1
  rw [upd0_mem hN z _ hP2N hs] at hy2
  rw [pmod (by omega) hzN] at hxmem hy1 hy2
  split_ifs at hxmem hy1 hy2 <;> omega

end noncov

end AdalyFormal.NonVacMix
