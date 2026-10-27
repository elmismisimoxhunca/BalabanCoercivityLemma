import GE11
import GV14

/-!
# BLC1 -- coordinates on a non-wrapping box under the BallCharts guard `2r + 2 ≤ L + 1` (m2_ballcharts, 2026-10-15)

The guard of `BallChartsAtG` is `2 r + 2 ≤ L_σ + 1`.  GV1's `bond_lift` needs injectivity of `iota v` on `Box (r+1)`,
i.e. `2 r + 3 ≤ L + 1`, which the guard does NOT give.  Here: MIXED injectivity (`p ∈ Box r`, `q ∈ Box (r+1)`), which
the guard does give, and the bond / stencil / chart transfer between `ZCh` (coordinates) and `GChart` (sites) on any
`S ⊆ Box r`.  Also `ball_sub_lift`: `Ball v r ⊆ lift v (Box r)` (no hypothesis), and `trans_zbox`: transition
variation along walks inside an integer box in coordinates (no injectivity needed).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2BallCharts

open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3 AdalyFormal.M2Glue2 AdalyFormal.M2GlueGeo
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open Fin.CommRing

variable {L : PeriodicLatticeExtent}

/-- mixed injectivity: `p ∈ Box r`, `q ∈ Box (r+1)`, torus side `> 2r + 1`. -/
theorem mixed_inj (v : PeriodicLatticeSite L) {r : ℕ} (hL : ∀ μ, 2 * r + 1 < L μ + 1) {p q : Z3}
    (hp : p ∈ Box r) (hq : q ∈ Box (r + 1)) (h : iota v p = iota v q) : p = q := by
  funext μ
  have h1 : v μ + ((p μ : ℤ) : Fin (L μ + 1)) = v μ + ((q μ : ℤ) : Fin (L μ + 1)) := congrFun h μ
  have h2 : ((p μ : ℤ) : Fin (L μ + 1)) = ((q μ : ℤ) : Fin (L μ + 1)) := add_left_cancel h1
  have h3 : ((p μ : ℤ) : ZMod (L μ + 1)) = ((q μ : ℤ) : ZMod (L μ + 1)) := h2
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h3
  have hd : ((L μ + 1 : ℕ) : ℤ) ∣ (p μ - q μ) := by
    have := dvd_sub_comm.mp h3; exact_mod_cast this
  have hb : |p μ - q μ| < ((L μ + 1 : ℕ) : ℤ) := by
    have a := hp μ; have b := hq μ
    have c := hL μ
    have : |p μ - q μ| ≤ |p μ| + |q μ| := abs_sub _ _
    have c' : (2 * (r : ℤ) + 1) < ((L μ + 1 : ℕ) : ℤ) := by exact_mod_cast c
    push_cast at b
    linarith
  have := Int.eq_zero_of_abs_lt_dvd hd hb
  linarith

theorem bond_lift' {v : PeriodicLatticeSite L} {r : ℕ} (hL : ∀ μ, 2 * r + 1 < L μ + 1) {S : Set Z3}
    (hS : S ⊆ Box r) {x : PeriodicLatticeSite L} {ν : Fin 3} (hx : x ∈ lift v S)
    (hxν : periodicLatticeShift x ν ∈ lift v S) : ∃ p, x = iota v p ∧ p ∈ S ∧ p + ev ν ∈ S := by
  obtain ⟨p, hp, rfl⟩ := hx
  refine ⟨p, rfl, hp, ?_⟩
  rw [iota_shift] at hxν
  obtain ⟨p', hp', he⟩ := hxν
  have := mixed_inj v hL (hS hp') (add_ev_mem (hS hp) ν) he
  rw [← this]; exact hp'

theorem sten_lift' {v : PeriodicLatticeSite L} {r : ℕ} (hL : ∀ μ, 2 * r + 1 < L μ + 1) {S : Set Z3}
    (hS : S ⊆ Box r) {x : PeriodicLatticeSite L} {μ ν : Fin 3} (h0 : x ∈ lift v S)
    (h1 : periodicLatticeShift x ν ∈ lift v S) (h2 : periodicLatticeShift x μ ∈ lift v S)
    (h3 : periodicLatticeShift (periodicLatticeShift x μ) ν ∈ lift v S) :
    ∃ p, x = iota v p ∧ p ∈ S ∧ p + ev ν ∈ S ∧ p + ev μ ∈ S ∧ p + ev μ + ev ν ∈ S := by
  have B : ∀ {a b : Z3}, a ∈ S → b ∈ S → iota v a = iota v b → a = b := fun ha hb e =>
    mixed_inj v hL (hS ha) (Box_mono (Nat.le_succ r) (hS hb)) e
  obtain ⟨p, rfl, hp, hpν⟩ := bond_lift' hL hS h0 h1
  obtain ⟨p', e', hp', hpμ⟩ := bond_lift' hL hS h0 h2
  have := B hp hp' e'; subst this
  obtain ⟨p'', e'', hp'', hpμν⟩ := bond_lift' hL hS h2 h3
  rw [iota_shift] at e''
  have := B hpμ hp'' e''; subst this
  exact ⟨p, rfl, hp, hpν, hpμ, hpμν⟩

/-- injectivity on `Box r` itself. -/
theorem inj_box (v : PeriodicLatticeSite L) {r : ℕ} (hL : ∀ μ, 2 * r + 1 < L μ + 1) :
    Set.InjOn (iota v) (Box r) :=
  iota_injOn v (fun μ => by have := hL μ; omega)

/-- coordinates `ZCh` on a set `T` give a `GChart` on the sites of `S ⊆ Box r` whose coordinates satisfy `P`,
provided every such coordinate point lies in `T`. -/
theorem gchart_sub_of_zch {v : PeriodicLatticeSite L} {r : ℕ} (hL : ∀ μ, 2 * r + 1 < L μ + 1) {S : Set Z3}
    (hS : S ⊆ Box r) {P : Z3 → Prop} {T : Set Z3} (hT : ∀ p ∈ S, P p → p ∈ T) {U : LinkCfg L}
    {g : PeriodicLatticeSite L → SU2} {a b : ℝ} (h : ZCh U g v T (fun _ => a) (fun _ => b)) :
    GChart U g {x | x ∈ lift v S ∧ P (coord v r x)} a b := by
  have hinj := inj_box v hL
  have hc : ∀ q ∈ S, coord v r (iota v q) = q := fun q hq => coord_iota hinj (hS hq)
  refine ⟨fun x ν hx hxν => ?_, fun x μ ν h0 h1 h2 h3 => ?_⟩
  · obtain ⟨p, rfl, hp, hpν⟩ := bond_lift' hL hS hx.1 hxν.1
    have P0 := hx.2; have P1 := hxν.2
    rw [hc p hp] at P0
    rw [iota_shift, hc _ hpν] at P1
    exact h.1 p ν (hT p hp P0) (hT _ hpν P1)
  · obtain ⟨p, rfl, hp, hpν, hpμ, hpμν⟩ := sten_lift' hL hS h0.1 h1.1 h2.1 h3.1
    have P0 := h0.2; have P1 := h1.2; have P2 := h2.2; have P3 := h3.2
    rw [hc p hp] at P0
    rw [iota_shift, hc _ hpν] at P1
    rw [iota_shift, hc _ hpμ] at P2
    rw [iota_shift2, hc _ hpμν] at P3
    rw [iota_shift]
    exact h.2 p μ ν (hT p hp P0) (hT _ hpν P1) (hT _ hpμ P2) (hT _ hpμν P3)

/-- the converse: a `GChart` on such a site set gives `ZCh` on the coordinate set. -/
theorem zch_of_gchart_sub {v : PeriodicLatticeSite L} {r : ℕ} (hL : ∀ μ, 2 * r + 1 < L μ + 1) {S : Set Z3}
    (hS : S ⊆ Box r) {P : Z3 → Prop} {U : LinkCfg L} {g : PeriodicLatticeSite L → SU2} {a b : ℝ}
    (h : GChart U g {x | x ∈ lift v S ∧ P (coord v r x)} a b) :
    ZCh U g v {p | p ∈ S ∧ P p} (fun _ => a) (fun _ => b) := by
  have hinj := inj_box v hL
  have mem : ∀ q, q ∈ S → P q → iota v q ∈ {x | x ∈ lift v S ∧ P (coord v r x)} := by
    intro q hq hP
    refine ⟨iota_mem_lift hq, ?_⟩
    show P (coord v r (iota v q))
    rw [coord_iota hinj (hS hq)]; exact hP
  refine ⟨fun p ν hp hpν => ?_, fun p μ ν h0 h1 h2 h3 => ?_⟩
  · have := h.1 (iota v p) ν (mem p hp.1 hp.2) (by rw [iota_shift]; exact mem _ hpν.1 hpν.2)
    exact this
  · have := h.2 (iota v p) μ ν (mem p h0.1 h0.2) (by rw [iota_shift]; exact mem _ h1.1 h1.2)
      (by rw [iota_shift]; exact mem _ h2.1 h2.2) (by rw [iota_shift2]; exact mem _ h3.1 h3.2)
    rw [iota_shift] at this
    exact this

/-- the coordinate along `σ` is affine on bonds of `lift v S`, `S ⊆ Box r`. -/
theorem coord_affine {v : PeriodicLatticeSite L} {r : ℕ} (hL : ∀ μ, 2 * r + 1 < L μ + 1) {S : Set Z3}
    (hS : S ⊆ Box r) (σ : Fin 3) {P : Z3 → Prop} :
    ∀ x μ, x ∈ {x | x ∈ lift v S ∧ P (coord v r x)} →
      periodicLatticeShift x μ ∈ {x | x ∈ lift v S ∧ P (coord v r x)} →
      ((coord v r (periodicLatticeShift x μ) σ : ℤ) : ℝ) = ((coord v r x σ : ℤ) : ℝ) + (if μ = σ then 1 else 0) := by
  intro x μ hx hxμ
  have hinj := inj_box v hL
  obtain ⟨p, rfl, hp, hpμ⟩ := bond_lift' hL hS hx.1 hxμ.1
  rw [iota_shift, coord_iota hinj (hS hpμ), coord_iota hinj (hS hp)]
  by_cases h : μ = σ
  · subst h; simp [ev]
  · simp [ev, h, Ne.symm h]

/-! ## the ball inside the coordinate box -/

theorem pcd_rep (N a b : ℕ) (ha : a < N) (hb : b < N) :
    ∃ d : ℤ, |d| ≤ (pcd N a b : ℤ) ∧ ((a : ℤ) + d) % (N : ℤ) = b := by
  have hbN : (b : ℤ) % N = b := Int.emod_eq_of_lt (by omega) (by omega)
  unfold pcd
  by_cases h : a ≤ b
  · rw [if_pos h]
    rcases le_total (b - a) (N - (b - a)) with h2 | h2
    · refine ⟨(b : ℤ) - a, ?_, ?_⟩
      · rw [min_eq_left h2, abs_le]; constructor <;> push_cast [Nat.cast_sub h] <;> omega
      · rw [show (a : ℤ) + ((b : ℤ) - a) = b by ring, hbN]
    · refine ⟨(b : ℤ) - a - N, ?_, ?_⟩
      · rw [min_eq_right h2, abs_le]
        have e1 : ((N - (b - a) : ℕ) : ℤ) = (N : ℤ) - ((b : ℤ) - a) := by omega
        rw [e1]; constructor <;> omega
      · rw [show (a : ℤ) + ((b : ℤ) - a - N) = b + N * (-1) by ring, Int.add_mul_emod_self_left, hbN]
  · rw [if_neg h]
    have h' : b < a := by omega
    rcases le_total (a - b) (N - (a - b)) with h2 | h2
    · refine ⟨(b : ℤ) - a, ?_, ?_⟩
      · rw [min_eq_left h2, abs_le]; constructor <;> omega
      · rw [show (a : ℤ) + ((b : ℤ) - a) = b by ring, hbN]
    · refine ⟨(b : ℤ) - a + N, ?_, ?_⟩
      · rw [min_eq_right h2, abs_le]
        have e1 : ((N - (a - b) : ℕ) : ℤ) = (N : ℤ) - ((a : ℤ) - b) := by omega
        rw [e1]; constructor <;> omega
      · rw [show (a : ℤ) + ((b : ℤ) - a + N) = b + N * 1 by ring, Int.add_mul_emod_self_left, hbN]

theorem pcd_le_pdist (x y : PeriodicLatticeSite L) (μ : Fin 3) : pcd (L μ + 1) (x μ).val (y μ).val ≤ pdist x y := by
  unfold pdist
  exact Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (x μ).val (y μ).val)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ μ)

/-- the `ℓ¹` ball sits inside the coordinate box (no non-wrap hypothesis). -/
theorem ball_sub_lift (v : PeriodicLatticeSite L) (r : ℕ) : Ball v r ⊆ lift v (Box r) := by
  intro x hx
  have hx' : pdist v x ≤ r := hx
  have hrep : ∀ μ : Fin 3, ∃ d : ℤ, |d| ≤ (r : ℤ) ∧ (((v μ).val : ℤ) + d) % ((L μ + 1 : ℕ) : ℤ) = (x μ).val := by
    intro μ
    obtain ⟨d, hd, he⟩ := pcd_rep (L μ + 1) (v μ).val (x μ).val (v μ).isLt (x μ).isLt
    have := pcd_le_pdist v x μ
    refine ⟨d, hd.trans (by exact_mod_cast this.trans hx'), he⟩
  choose d hd using hrep
  refine ⟨d, fun μ => (hd μ).1, ?_⟩
  funext μ
  apply Fin.ext
  have := iota_val_int v d μ
  rw [(hd μ).2] at this
  exact_mod_cast this

/-! ## transitions along walks in an integer box (coordinates; no injectivity) -/

theorem trans_zbox (v : PeriodicLatticeSite L) {U : LinkCfg L} {gP gQ : PeriodicLatticeSite L → SU2}
    {lo hi : Z3} {β : ℝ}
    (hβ : ∀ z μ, z ∈ IBox lo hi → z + ev μ ∈ IBox lo hi →
      frobNorm (((periodicGaugeTransform gP U (iota v z, μ) : SU2) : M2) - 1)
        + frobNorm (((periodicGaugeTransform gQ U (iota v z, μ) : SU2) : M2) - 1) ≤ β)
    {p' : Z3} (hp' : p' ∈ IBox lo hi) :
    ∀ n : ℕ, ∀ p, p ∈ IBox lo hi → l1 p p' = n →
      frobNorm (((trans gP gQ (iota v p) : SU2) : M2) - (trans gP gQ (iota v p') : M2)) ≤ n * β := by
  intro n
  induction n with
  | zero =>
    intro p _ h
    have e : p = p' := by
      unfold l1 at h; funext j; fin_cases j <;> simp <;> omega
    rw [e]; simp [frobNorm, AdalyFormal.Balaban.RMapLipschitz.frobSq]
  | succ n ih =>
    intro p hp h
    obtain ⟨i, hne⟩ := exists_ne_of_l1 h
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hm := add_ev_mem_box hp hp' hlt
      have w := ih (p + ev i) hm (l1_add_ev h hlt)
      have t1 := trans_one _ _ _ _ (trans_rel U gP gQ (iota v p) i)
      rw [iota_shift, frobNorm_sub_comm] at t1
      have := hβ p i hp hm
      have t := frobNorm_sub_le' ((trans gP gQ (iota v p) : SU2) : M2)
        ((trans gP gQ (iota v (p + ev i)) : SU2) : M2) ((trans gP gQ (iota v p') : SU2) : M2)
      push_cast; linarith
    · have hm := sub_ev_mem hp hp' hgt
      have w := ih (p - ev i) hm (l1_sub_ev h hgt)
      have t1 := trans_one _ _ _ _ (trans_rel U gP gQ (iota v (p - ev i)) i)
      rw [iota_shift, ev_sub_add] at t1
      have := hβ (p - ev i) i hm (by rw [ev_sub_add]; exact hp)
      have t := frobNorm_sub_le' ((trans gP gQ (iota v p) : SU2) : M2)
        ((trans gP gQ (iota v (p - ev i)) : SU2) : M2) ((trans gP gQ (iota v p') : SU2) : M2)
      push_cast; linarith

/-- `l1` inside an integer box. -/
theorem l1_le_ibox {lo hi p p' : Z3} (hp : p ∈ IBox lo hi) (hp' : p' ∈ IBox lo hi) :
    (l1 p p' : ℤ) ≤ (hi 0 - lo 0) + (hi 1 - lo 1) + (hi 2 - lo 2) := by
  have a0 := hp 0; have a1 := hp 1; have a2 := hp 2
  have b0 := hp' 0; have b1 := hp' 1; have b2 := hp' 2
  unfold l1; push_cast
  have e0 : ((p 0 - p' 0).natAbs : ℤ) = |p 0 - p' 0| := Int.natCast_natAbs _
  have e1 : ((p 1 - p' 1).natAbs : ℤ) = |p 1 - p' 1| := Int.natCast_natAbs _
  have e2 : ((p 2 - p' 2).natAbs : ℤ) = |p 2 - p' 2| := Int.natCast_natAbs _
  have := abs_sub_le_iff.mpr (show p 0 - p' 0 ≤ hi 0 - lo 0 ∧ p' 0 - p 0 ≤ hi 0 - lo 0 by omega)
  have := abs_sub_le_iff.mpr (show p 1 - p' 1 ≤ hi 1 - lo 1 ∧ p' 1 - p 1 ≤ hi 1 - lo 1 by omega)
  have := abs_sub_le_iff.mpr (show p 2 - p' 2 ≤ hi 2 - lo 2 ∧ p' 2 - p 2 ≤ hi 2 - lo 2 by omega)
  linarith

end AdalyFormal.M2BallCharts
