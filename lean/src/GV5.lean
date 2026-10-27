import GV4

/-!
# GV5 -- local (windowed) two-chart gluing in coordinates (m2_glue3, 2026-10-15)

`glue_zstep`: `glue_two` applied on the radius-2 coordinate window around each bond / stencil of the target
set, so every constant may depend on the position (`T1, T2, τ, κ1, κ2` pointwise, `W*` window bounds).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M2Glue3

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.M2Glue2
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

variable {L : PeriodicLatticeExtent}

/-- the radius-2 window of `p` inside `S`. -/
def win (S : Set Z3) (p : Z3) : Set Z3 := {p' | p' ∈ S ∧ ∀ i, |p' i - p i| ≤ 2}

theorem win_sub (S : Set Z3) (p : Z3) : win S p ⊆ S := fun _ h => h.1

theorem self_mem_win {S : Set Z3} {p : Z3} (hp : p ∈ S) : p ∈ win S p := ⟨hp, fun i => by simp⟩

theorem ev_mem_win {S : Set Z3} {p : Z3} {ν : Fin 3} (hp : p + ev ν ∈ S) : p + ev ν ∈ win S p := by
  refine ⟨hp, fun i => ?_⟩
  have := ev_abs ν i
  simp only [Pi.add_apply, add_sub_cancel_left]; linarith

theorem ev2_mem_win {S : Set Z3} {p : Z3} {μ ν : Fin 3} (hp : p + ev μ + ev ν ∈ S) : p + ev μ + ev ν ∈ win S p := by
  refine ⟨hp, fun i => ?_⟩
  have a := ev_abs μ i; have b := ev_abs ν i
  simp only [Pi.add_apply]
  rw [show p i + ev μ i + ev ν i - p i = ev μ i + ev ν i by ring]
  calc |ev μ i + ev ν i| ≤ |ev μ i| + |ev ν i| := abs_add_le _ _
    _ ≤ 2 := by linarith

theorem glue_zstep {U : LinkCfg L} {v : PeriodicLatticeSite L} {Rb : ℕ}
    (hinj : Set.InjOn (iota v) (Box (Rb + 1))) {SP SQ SD : Set Z3} (hSP : SP ⊆ Box Rb) (hSQ : SQ ⊆ Box Rb)
    (hSD : SD ⊆ Box Rb) {gP gQ : PeriodicLatticeSite L → SU2} {C : Z3 → ℝ} {c : PeriodicLatticeSite L → ℝ}
    (hc : ∀ p ∈ Box Rb, c (iota v p) = C p)
    {T1 T2 τ k1 k2 W1 W2 Wτ Wk1 Wk2 : Z3 → ℝ}
    (hP : ZCh U gP v SP T1 T2) (hQ : ZCh U gQ v SQ T1 T2)
    (hh : ∀ p, p ∈ SP → p ∈ SQ → frobNorm (((trans gP gQ (iota v p) : SU2) : M2) - 1) ≤ τ p)
    (hC : ∀ p ∈ SD, 0 ≤ C p ∧ C p ≤ 1)
    (hC1 : ∀ p ν, p ∈ SD → p + ev ν ∈ SD → |C (p + ev ν) - C p| ≤ k1 p)
    (hC2 : ∀ p μ ν, p ∈ SD → p + ev ν ∈ SD → p + ev μ ∈ SD → p + ev μ + ev ν ∈ SD →
      |C (p + ev μ + ev ν) - C (p + ev μ) - C (p + ev ν) + C p| ≤ k2 p)
    (hbond : ∀ p ν, p ∈ SD → p + ev ν ∈ SD →
      (C p = 0 ∧ C (p + ev ν) = 0 ∧ p ∈ SP ∧ p + ev ν ∈ SP) ∨
      (C p = 1 ∧ C (p + ev ν) = 1 ∧ p ∈ SQ ∧ p + ev ν ∈ SQ) ∨
      (p ∈ SP ∧ p ∈ SQ ∧ p + ev ν ∈ SP ∧ p + ev ν ∈ SQ))
    (hsten : ∀ p μ ν, p ∈ SD → p + ev ν ∈ SD → p + ev μ ∈ SD → p + ev μ + ev ν ∈ SD →
      (∀ y ∈ ({p, p + ev ν, p + ev μ, p + ev μ + ev ν} : Set Z3), C y = 0 ∧ y ∈ SP) ∨
      (∀ y ∈ ({p, p + ev ν, p + ev μ, p + ev μ + ev ν} : Set Z3), C y = 1 ∧ y ∈ SQ) ∨
      (∀ y ∈ ({p, p + ev ν, p + ev μ, p + ev μ + ev ν} : Set Z3), y ∈ SP ∧ y ∈ SQ))
    (hwin : ∀ p p', p ∈ SD → p' ∈ win SD p →
      T1 p' ≤ W1 p ∧ T2 p' ≤ W2 p ∧ τ p' ≤ Wτ p ∧ k1 p' ≤ Wk1 p ∧ k2 p' ≤ Wk2 p)
    (hW : ∀ p ∈ SD, 0 ≤ W1 p ∧ 0 ≤ W2 p ∧ 0 ≤ Wτ p ∧ Wτ p ≤ 2 ∧ 0 ≤ Wk1 p ∧ 0 ≤ Wk2 p) :
    ZCh U (gglue gP gQ c) v SD (fun p => glueT1 (W1 p) (Wτ p) (Wk1 p))
      (fun p => glueT2 (W1 p) (W2 p) (Wτ p) (Wk1 p) (Wk2 p)) := by
  have hinj0 : Set.InjOn (iota v) (Box Rb) := hinj.mono (Box_mono (Nat.le_succ Rb))
  -- the windowed application of `glue_two`
  have key : ∀ p, p ∈ SD → GChart U (gglue gP gQ c) (lift v (win SD p)) (glueT1 (W1 p) (Wτ p) (Wk1 p))
      (glueT2 (W1 p) (W2 p) (Wτ p) (Wk1 p) (Wk2 p)) := by
    intro p hp
    obtain ⟨w1, w2, wτ, wτ2, wk1, wk2⟩ := hW p hp
    set W := win SD p
    have hWD : W ⊆ Box Rb := (win_sub SD p).trans hSD
    have hPW : SP ∩ W ⊆ Box Rb := fun _ h => hSP h.1
    have hQW : SQ ∩ W ⊆ Box Rb := fun _ h => hSQ h.1
    have gP' : GChart U gP (lift v (SP ∩ W)) (W1 p) (W2 p) :=
      gchart_lift hinj hPW (hP.mono Set.inter_subset_left (fun _ _ => le_rfl) (fun _ _ => le_rfl))
        (fun p' h => ⟨(hwin p p' hp h.2).1, (hwin p p' hp h.2).2.1⟩)
    have gQ' : GChart U gQ (lift v (SQ ∩ W)) (W1 p) (W2 p) :=
      gchart_lift hinj hQW (hQ.mono Set.inter_subset_left (fun _ _ => le_rfl) (fun _ _ => le_rfl))
        (fun p' h => ⟨(hwin p p' hp h.2).1, (hwin p p' hp h.2).2.1⟩)
    refine glue_two (DP := lift v (SP ∩ W)) (DQ := lift v (SQ ∩ W)) w1 w2 wτ wτ2 wk1 wk2 gP' gQ' ?_ ?_ ?_ ?_ ?_ ?_
    · rintro x ⟨p', hp', rfl⟩ ⟨p'', hp'', he⟩
      have := hinj0 (hSQ hp''.1) (hSP hp'.1) he
      subst this
      exact (hh p'' hp'.1 hp''.1).trans (hwin p p'' hp hp''.2).2.2.1
    · rintro x ⟨p', hp', rfl⟩
      rw [hc p' (hWD hp')]; exact hC p' (win_sub SD p hp')
    · intro x ν hx hxν
      obtain ⟨p', rfl, h0, h1⟩ := bond_lift hinj hWD hx hxν
      rw [iota_shift, hc _ (hWD h1), hc _ (hWD h0)]
      exact (hC1 p' ν h0.1 h1.1).trans (hwin p p' hp h0).2.2.2.1
    · intro x μ ν h0 h1 h2 h3
      obtain ⟨p', rfl, a0, a1, a2, a3⟩ := sten_lift hinj hWD h0 h1 h2 h3
      rw [iota_shift2, iota_shift, iota_shift, hc _ (hWD a3), hc _ (hWD a2), hc _ (hWD a1), hc _ (hWD a0)]
      exact (hC2 p' μ ν a0.1 a1.1 a2.1 a3.1).trans (hwin p p' hp a0).2.2.2.2
    · intro x ν hx hxν
      obtain ⟨p', rfl, h0, h1⟩ := bond_lift hinj hWD hx hxν
      rw [iota_shift, hc _ (hWD h1), hc _ (hWD h0)]
      rcases hbond p' ν h0.1 h1.1 with ⟨a, b, c1, c2⟩ | ⟨a, b, c1, c2⟩ | ⟨a, b, c1, c2⟩
      · exact Or.inl ⟨a, b, iota_mem_lift ⟨c1, h0⟩, iota_mem_lift ⟨c2, h1⟩⟩
      · exact Or.inr (Or.inl ⟨a, b, iota_mem_lift ⟨c1, h0⟩, iota_mem_lift ⟨c2, h1⟩⟩)
      · exact Or.inr (Or.inr ⟨iota_mem_lift ⟨a, h0⟩, iota_mem_lift ⟨b, h0⟩, iota_mem_lift ⟨c1, h1⟩,
          iota_mem_lift ⟨c2, h1⟩⟩)
    · intro x μ ν h0 h1 h2 h3
      obtain ⟨p', rfl, a0, a1, a2, a3⟩ := sten_lift hinj hWD h0 h1 h2 h3
      rw [iota_shift2, iota_shift, iota_shift]
      have cv : ∀ y ∈ ({p', p' + ev ν, p' + ev μ, p' + ev μ + ev ν} : Set Z3), y ∈ W ∧ c (iota v y) = C y := by
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        have hyW : y ∈ W := by rcases hy with rfl | rfl | rfl | rfl <;> assumption
        exact ⟨hyW, hc y (hWD hyW)⟩
      have im : ∀ y' : PeriodicLatticeSite L,
          y' ∈ ({iota v p', iota v (p' + ev ν), iota v (p' + ev μ), iota v (p' + ev μ + ev ν)} :
            Set (PeriodicLatticeSite L)) →
          ∃ y ∈ ({p', p' + ev ν, p' + ev μ, p' + ev μ + ev ν} : Set Z3), y' = iota v y := by
        intro y' hy'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy'
        rcases hy' with rfl | rfl | rfl | rfl
        · exact ⟨_, by simp, rfl⟩
        · exact ⟨_, by simp, rfl⟩
        · exact ⟨_, by simp, rfl⟩
        · exact ⟨_, by simp, rfl⟩
      rcases hsten p' μ ν a0.1 a1.1 a2.1 a3.1 with hA | hA | hA
      · left; intro y' hy'
        obtain ⟨y, hy, rfl⟩ := im y' hy'
        obtain ⟨hyW, hcy⟩ := cv y hy
        exact ⟨by rw [hcy]; exact (hA y hy).1, iota_mem_lift ⟨(hA y hy).2, hyW⟩⟩
      · right; left; intro y' hy'
        obtain ⟨y, hy, rfl⟩ := im y' hy'
        obtain ⟨hyW, hcy⟩ := cv y hy
        exact ⟨by rw [hcy]; exact (hA y hy).1, iota_mem_lift ⟨(hA y hy).2, hyW⟩⟩
      · right; right; intro y' hy'
        obtain ⟨y, hy, rfl⟩ := im y' hy'
        obtain ⟨hyW, _⟩ := cv y hy
        exact ⟨iota_mem_lift ⟨(hA y hy).1, hyW⟩, iota_mem_lift ⟨(hA y hy).2, hyW⟩⟩
  refine ⟨fun p ν hp hpν => ?_, fun p μ ν h0 h1 h2 h3 => ?_⟩
  · have := (key p hp).1 (iota v p) ν (iota_mem_lift (self_mem_win hp))
      (by rw [iota_shift]; exact iota_mem_lift (ev_mem_win hpν))
    exact this
  · have := (key p h0).2 (iota v p) μ ν (iota_mem_lift (self_mem_win h0))
      (by rw [iota_shift]; exact iota_mem_lift (ev_mem_win h1))
      (by rw [iota_shift]; exact iota_mem_lift (ev_mem_win h2))
      (by rw [iota_shift2]; exact iota_mem_lift (ev2_mem_win h3))
    rw [iota_shift] at this
    exact this

end AdalyFormal.M2Glue3
