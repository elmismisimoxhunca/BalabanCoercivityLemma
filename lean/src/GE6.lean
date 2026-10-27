import GE5

/-!
# GE6 -- bands, nearest vertex, and the packaged `cover_geometry` (m2_gluegeo, 2026-10-15)

* `band_cube`: the tube of four blocks on the grid edge from `v` to `v + s e_sigma` lies in ONE class cube; as site sets
  `iota v '' HSlab s sigma true = iota v' '' HSlab s sigma false` (`v' = iota v (s e_sigma)`).
* `site_near_vertex`: every site is `iota v p0` with `v` on the `s`-grid and `2 |p0_i| <= s`.
* `cover_geometry`: anchor `x0 in Omega_j`, `s = M ell^(j-1)`, `rho + 24 s <= R s`: every site `x` of `Ball x0 rho` sits in the middle
  of the box of a grid vertex `v` carrying the six half-slab cubes, and `v` is either good (box in one cube) or bad (box in none).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2GlueGeo

open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_triangle Ball)
open AdalyFormal.M2Bridge (pdist_lt_three_s')
open Fin.CommRing

variable {L : PeriodicLatticeExtent}

theorem fin_add_int_val (n : ℕ) (a : Fin (n + 1)) (p : ℤ) :
    ((a + (p : Fin (n + 1))).val : ℤ) = ((a.val : ℤ) + p) % ((n + 1 : ℕ) : ℤ) := by
  rw [Fin.val_add, Fin.val_intCast]
  have hN : (0 : ℤ) < (n : ℤ) + 1 := by positivity
  push_cast
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hN.ne')]
  exact Int.add_emod_emod _ _ _

theorem iota_iota (v : PeriodicLatticeSite L) (a b : Z3) : iota (iota v a) b = iota v (a + b) := by
  funext μ
  simp only [iota, Pi.add_apply, Int.cast_add]
  ring

theorem coord_near (N s : ℕ) (hs : 0 < s) (hsN : s ∣ N) (xv : ℕ) (hx : xv < N) :
    ∃ vv : ℕ, vv < N ∧ vv % s = 0 ∧ ∃ p : ℤ, 2 * |p| ≤ s ∧ ((vv : ℤ) + p) % (N : ℤ) = xv := by
  obtain ⟨n, hn⟩ := hsN
  have hN0 : 0 < N := by omega
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hn; omega
    · exact h
  have hxe : xv = s * (xv / s) + xv % s := (Nat.div_add_mod xv s).symm
  have hr : xv % s < s := Nat.mod_lt _ hs
  have han : xv / s < n := by
    by_contra hc
    have : s * n ≤ s * (xv / s) := Nat.mul_le_mul_left s (not_lt.mp hc)
    omega
  by_cases h2 : 2 * (xv % s) ≤ s
  · refine ⟨s * (xv / s), by omega, Nat.mul_mod_right _ _, (xv % s : ℕ), ?_, ?_⟩
    · rw [abs_of_nonneg (by positivity)]; exact_mod_cast h2
    · have : ((s * (xv / s) : ℕ) : ℤ) + ((xv % s : ℕ) : ℤ) = (xv : ℤ) := by exact_mod_cast hxe.symm
      rw [this]; exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hx)
  · refine ⟨(s * (xv / s + 1)) % N, Nat.mod_lt _ hN0, ?_, ((xv % s : ℕ) : ℤ) - s, ?_, ?_⟩
    · exact Nat.mod_eq_zero_of_dvd ((Nat.dvd_mod_iff ⟨n, hn⟩).mpr (dvd_mul_right _ _))
    · have h3 : ((xv % s : ℕ) : ℤ) - s < 0 := by
        have : (xv % s : ℕ) < s := hr
        omega
      rw [abs_of_neg h3]; omega
    · have e : (((s * (xv / s + 1)) % N : ℕ) : ℤ) = ((s * (xv / s + 1) : ℕ) : ℤ) % (N : ℤ) := by
        exact_mod_cast Int.natCast_mod _ _
      rw [e, Int.emod_add_emod]
      have : ((s * (xv / s + 1) : ℕ) : ℤ) + (((xv % s : ℕ) : ℤ) - s) = (xv : ℤ) := by
        have : ((s * (xv / s) : ℕ) : ℤ) + ((xv % s : ℕ) : ℤ) = (xv : ℤ) := by exact_mod_cast hxe.symm
        push_cast at this ⊢
        linarith
      rw [this]; exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hx)

theorem site_near_vertex {s : ℕ} (hs : 0 < s) (hsN : ∀ μ, s ∣ L μ + 1) (x : PeriodicLatticeSite L) :
    ∃ v : PeriodicLatticeSite L, (∀ μ, (v μ).val % s = 0) ∧ ∃ p0 : Z3, (∀ i, 2 * |p0 i| ≤ s) ∧ iota v p0 = x := by
  have h : ∀ μ : Fin 3, ∃ vv : ℕ, vv < L μ + 1 ∧ vv % s = 0 ∧ ∃ p : ℤ, 2 * |p| ≤ s ∧
      ((vv : ℤ) + p) % ((L μ + 1 : ℕ) : ℤ) = (x μ).val :=
    fun μ => coord_near (L μ + 1) s hs (hsN μ) (x μ).val (x μ).isLt
  choose vv hvv hvs p hp hpe using h
  refine ⟨fun μ => ⟨vv μ, hvv μ⟩, fun μ => hvs μ, p, fun i => hp i, ?_⟩
  funext μ
  apply Fin.ext
  have := fin_add_int_val (L μ) ⟨vv μ, hvv μ⟩ (p μ)
  unfold iota
  have h2 : (((⟨vv μ, hvv μ⟩ : Fin (L μ + 1)) + ((p μ : ℤ) : Fin (L μ + 1))).val : ℤ) = ((x μ).val : ℤ) := by
    rw [this]; exact hpe μ
  exact_mod_cast h2

theorem emod_aux (a p s N : ℤ) :
    (((a + p) % N + N - (a + (-s)) % N)) % N = (p + s) % N := by
  have h1 : (a + p) % N ≡ a + p [ZMOD N] := Int.mod_modEq _ _
  have h2 : (a + (-s)) % N ≡ a + (-s) [ZMOD N] := Int.mod_modEq _ _
  have h3 : N ≡ 0 [ZMOD N] := by simp [Int.ModEq]
  have := ((h1.add h3).sub h2)
  have e : a + p + 0 - (a + -s) = p + s := by ring
  rw [e] at this
  exact this

theorem iota_mem_box {v : PeriodicLatticeSite L} {s : ℕ} {p : Z3} (hp : p ∈ BoxS s) :
    iota v p ∈ siteBox (iota v (fun _ => -(s : ℤ))) (2 * s) := by
  intro μ
  have hA := iota_val_int v p μ
  have hB := iota_val_int v (fun _ => -(s : ℤ)) μ
  have hAl := (iota v p μ).isLt
  have hBl := (iota v (fun _ => -(s : ℤ)) μ).isLt
  have hN : (0 : ℤ) < ((L μ + 1 : ℕ) : ℤ) := by positivity
  have hle : (iota v (fun _ => -(s : ℤ)) μ).val ≤ (iota v p μ).val + (L μ + 1) := by omega
  have key : ((((iota v p μ).val + (L μ + 1) - (iota v (fun _ => -(s : ℤ)) μ).val) % (L μ + 1) : ℕ) : ℤ)
      = (p μ + s) % ((L μ + 1 : ℕ) : ℤ) := by
    rw [Int.natCast_mod, Nat.cast_sub hle, Nat.cast_add, hA, hB]
    have := emod_aux ((v μ).val : ℤ) (p μ) s ((L μ + 1 : ℕ) : ℤ)
    push_cast at this ⊢
    exact this
  have hp1 := (hp μ).1
  have hp2 := (hp μ).2
  have h0 : 0 ≤ p μ + s := by omega
  have hle2 : (p μ + s) % ((L μ + 1 : ℕ) : ℤ) ≤ p μ + s := by
    have e1 := Int.emod_def (p μ + s) ((L μ + 1 : ℕ) : ℤ)
    have e2 := Int.ediv_nonneg h0 hN.le
    nlinarith
  have : (((((iota v p μ).val + (L μ + 1) - (iota v (fun _ => -(s : ℤ)) μ).val) % (L μ + 1) : ℕ)) : ℤ) < ((2 * s : ℕ) : ℤ) := by
    rw [key]; push_cast at hle2 ⊢; omega
  exact_mod_cast this

/-- **band**: the tube of four blocks on the grid edge `v -> v' = v + s e_sigma` lies in one class cube (width `s` in direction `sigma`). -/
theorem band_cube {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    (hcov : CoversOm0p ell M 12 k S) (hell : 2 ≤ ell) (hM : 0 < M) {m : ℕ} (hmk : m ≤ k)
    {x0 : PeriodicLatticeSite L} (hx0 : x0 ∈ S.Om (m + 1)) {v : PeriodicLatticeSite L}
    (hv : ∀ μ, (v μ).val % bigSide M ell m = 0)
    (hnear : ∀ p ∈ BoxS (bigSide M ell m), pdist (iota v p) x0 + 18 * bigSide M ell m ≤ R * bigSide M ell m)
    (σ : Fin 3) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M 12 k S sites j ∧
      (∀ p ∈ HSlab (bigSide M ell m) σ true, iota v p ∈ sites) ∧
      (∀ q ∈ HSlab (bigSide M ell m) σ false,
        iota (iota v (fun i => if i = σ then (bigSide M ell m : ℤ) else 0)) q ∈ sites) := by
  obtain ⟨sites, j, hq, -, h⟩ := slab_cube hS hcov hell hM hmk hx0 hv hnear σ true
  refine ⟨sites, j, hq, h, fun q hqm => ?_⟩
  rw [iota_iota]
  apply h
  have hs : 0 < bigSide M ell m := bigSide_pos (by omega) hM m
  refine ⟨fun i => ?_, Or.inl ⟨rfl, ?_⟩⟩
  · by_cases hi : i = σ
    · subst hi
      have a := hqm.1 i
      have b : q i ≤ -1 := by
        rcases hqm.2 with ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd h (by simp)
        · exact h
      simp only [Pi.add_apply, if_true]
      constructor <;> omega
    · simp only [Pi.add_apply, hi, if_false, zero_add]
      exact hqm.1 i
  · have a := hqm.1 σ
    have b : q σ ≤ -1 := by
      rcases hqm.2 with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h (by simp)
      · exact h
    simp only [Pi.add_apply, if_true]
    omega

/-- the box of a vertex whose middle region contains a site `x` of the ball is near the anchor. -/
theorem near_of_site {R s ρ : ℕ} {v : PeriodicLatticeSite L} {p0 : Z3} (hp0 : ∀ i, 2 * |p0 i| ≤ s)
    (hs : 0 < s) {x0 : PeriodicLatticeSite L} (hx : pdist (iota v p0) x0 ≤ ρ) (hρ : ρ + 24 * s ≤ R * s) :
    ∀ p ∈ BoxS s, pdist (iota v p) x0 + 18 * s ≤ R * s := by
  intro p hp
  have hp0b : p0 ∈ BoxS s := by
    intro i
    have := hp0 i
    have h1 := neg_abs_le (p0 i)
    have h2 := le_abs_self (p0 i)
    have hs' : (1 : ℤ) ≤ s := by exact_mod_cast hs
    constructor <;> omega
  have h6 := pdist_lt_three_s' (iota_mem_box (v := v) hp) (iota_mem_box (v := v) hp0b)
  have h7 := pdist_triangle (iota v p) (iota v p0) x0
  omega

/-- **cover geometry on a ball.**  Anchor `x0 in Omega_j`, `s = M ell^(j-1)`, `rho + 24 s <= R s`.  Every site `x` of the ball is
in the middle (`2|p0_i| <= s`) of the box of a vertex `v` of the `s`-grid; at `v` the six half-slab cubes exist; and `v` is either
good (box in one class cube) or bad (box in none). -/
theorem cover_geometry {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    (hcov : CoversOm0p ell M 12 k S) (hell : 2 ≤ ell) (hM : 0 < M) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {x0 : PeriodicLatticeSite L} (hx0 : x0 ∈ S.Om j) {ρ : ℕ}
    (hρ : ρ + 24 * bigSide M ell (j - 1) ≤ R * bigSide M ell (j - 1)) {x : PeriodicLatticeSite L}
    (hx : x ∈ Ball x0 ρ) :
    ∃ v : PeriodicLatticeSite L, (∀ μ, (v μ).val % bigSide M ell (j - 1) = 0) ∧
      ∃ p0 : Z3, (∀ i, 2 * |p0 i| ≤ bigSide M ell (j - 1)) ∧ iota v p0 = x ∧
      (∀ p ∈ BoxS (bigSide M ell (j - 1)), pdist (iota v p) x0 + 18 * bigSide M ell (j - 1) ≤ R * bigSide M ell (j - 1)) ∧
      VertexCubes ell M k S (j - 1) v ∧
      (GoodVertex ell M k S (bigSide M ell (j - 1)) v ∨ BadVertex ell M k S (bigSide M ell (j - 1)) v) := by
  have hs : 0 < bigSide M ell (j - 1) := bigSide_pos (by omega) hM _
  have hmk : j - 1 ≤ k := by omega
  have hx0' : x0 ∈ S.Om (j - 1 + 1) := by rw [Nat.sub_add_cancel hj1]; exact hx0
  obtain ⟨v, hv, p0, hp0, hxe⟩ := site_near_vertex hs (fun μ => hS.2.2.1 (j - 1) hmk μ) x
  have hx' : pdist (iota v p0) x0 ≤ ρ := by
    rw [hxe, pdist_comm]; exact hx
  have hnear := near_of_site (R := R) hp0 hs hx' hρ
  exact ⟨v, hv, p0, hp0, hxe, hnear, slab_cube hS hcov hell hM hmk hx0' hv hnear, em _⟩

end AdalyFormal.M2GlueGeo
