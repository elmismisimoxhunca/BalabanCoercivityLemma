import UZ2

/-!
# UZ3 -- clause-1 chart on the whole `ℓ¹` ball from the cell charts (lane unif_20261016)

`ball_chart1` : cell charts (constant `t`) on every `Bz r ∩ cell`, holonomy bound `η` on `Bz r`, and `r ≤ n s` give one
gauge on `Bz r` with constant `Tst n (Tst n (Tst n t η) η) η`, `Tst n t η = t + 2n (2t + η)`
(rows along `x`, then layers along `y`, then the ball along `z`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.UnifLane.Z

open AdalyFormal.M2Glue3 (Z3 ev)
open AdalyFormal.M2BallCharts (Bz)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

/-- one interval-stacking level. -/
noncomputable def Tst (n : ℕ) (t η : ℝ) : ℝ := t + ((n : ℝ) + n) * (2 * t + η)

theorem Tst_nonneg {n : ℕ} {t η : ℝ} (ht : 0 ≤ t) (hη : 0 ≤ η) : 0 ≤ Tst n t η := by unfold Tst; positivity

theorem cell_range {s : ℤ} (hs : 0 < s) (o : Z3) {r n : ℕ} (hrn : (r : ℤ) ≤ n * s) {p : Z3} (hp : p ∈ Bz r) (μ : Fin 3) :
    o μ / s - n ≤ cellZ s o p μ ∧ cellZ s o p μ ≤ o μ / s + n := by
  have hpμ : (p μ).natAbs ≤ r := by
    simp only [Bz, Set.mem_setOf_eq] at hp
    fin_cases μ <;> simp <;> omega
  have h1 : -(r : ℤ) ≤ p μ := by omega
  have h2 : p μ ≤ r := by omega
  constructor
  · have : (o μ + (-(n : ℤ)) * s) / s ≤ (p μ + o μ) / s := div_mono' hs (by nlinarith)
    rw [Int.add_mul_ediv_right _ _ hs.ne'] at this
    show o μ / s - n ≤ (p μ + o μ) / s
    linarith
  · have : (p μ + o μ) / s ≤ (o μ + (n : ℤ) * s) / s := div_mono' hs (by nlinarith)
    rw [Int.add_mul_ediv_right _ _ hs.ne'] at this
    exact this

theorem cyl_cells12 (j k : ℤ) (s : ℤ) (o : Z3) : Cyl 0 {p | cellZ s o p 1 = j ∧ cellZ s o p 2 = k} := by
  intro p q h
  have h1 := h 1 (by decide); have h2 := h 2 (by decide)
  simp only [Set.mem_setOf_eq, cellZ, h1, h2]

theorem cyl_cells2 (k : ℤ) (s : ℤ) (o : Z3) : Cyl 1 {p | cellZ s o p 2 = k} := by
  intro p q h
  have h2 := h 2 (by decide)
  simp only [Set.mem_setOf_eq, cellZ, h2]

theorem cyl_univ : Cyl 2 (Set.univ : Set Z3) := fun _ _ _ => by simp

/-- **the ball chart, clause 1.** -/
theorem ball_chart1 (W : Z3 → Fin 3 → SU2) {s : ℤ} (hs : 0 < s) (o : Z3) {r n : ℕ} (hrn : (r : ℤ) ≤ n * s)
    {t η : ℝ} (ht : 0 ≤ t) (hη : 0 ≤ η) (hhol : HolB W (Bz r) η)
    (hcell : ∀ c : Z3, ∃ G, C1 W G {p | p ∈ Bz r ∧ ∀ μ, cellZ s o p μ = c μ} t) :
    ∃ G, C1 W G (Bz r) (Tst n (Tst n (Tst n t η) η) η) := by
  have hr : ∀ p, p ∈ Bz r → ∀ μ, _ := fun p hp μ => cell_range hs o hrn (p := p) hp μ
  -- rows
  have rows : ∀ j k : ℤ, ∃ G, C1 W G {p | p ∈ Bz r ∧ cellZ s o p 1 = j ∧ cellZ s o p 2 = k} (Tst n t η) := by
    intro j k
    have hpc : ∀ i : ℤ, ∃ G, C1 W G (Pc s o r 0 {p | cellZ s o p 1 = j ∧ cellZ s o p 2 = k} i) t := by
      intro i
      obtain ⟨G, hG⟩ := hcell ![i, j, k]
      refine ⟨G, hG.mono (fun p hp => ⟨hp.1, fun μ => ?_⟩) le_rfl⟩
      obtain ⟨_, ⟨h1, h2⟩, h0⟩ := hp
      fin_cases μ <;> simp [h0, h1, h2]
    obtain ⟨G, hG⟩ := stack_interval W hs o r 0 (cyl_cells12 j k s o) ht hη hhol hpc n n
    exact ⟨G, hG.mono (fun p hp => ⟨hp.1, ⟨hp.2.1, hp.2.2⟩, (hr _ hp.1 0).1, (hr _ hp.1 0).2⟩) le_rfl⟩
  -- layers
  have layers : ∀ k : ℤ, ∃ G, C1 W G {p | p ∈ Bz r ∧ cellZ s o p 2 = k} (Tst n (Tst n t η) η) := by
    intro k
    have hpc : ∀ i : ℤ, ∃ G, C1 W G (Pc s o r 1 {p | cellZ s o p 2 = k} i) (Tst n t η) := by
      intro i
      obtain ⟨G, hG⟩ := rows i k
      exact ⟨G, hG.mono (fun p hp => ⟨hp.1, hp.2.2, hp.2.1⟩) le_rfl⟩
    obtain ⟨G, hG⟩ := stack_interval W hs o r 1 (cyl_cells2 k s o) (Tst_nonneg ht hη) hη hhol hpc n n
    exact ⟨G, hG.mono (fun p hp => ⟨hp.1, hp.2, (hr _ hp.1 1).1, (hr _ hp.1 1).2⟩) le_rfl⟩
  have hpc : ∀ i : ℤ, ∃ G, C1 W G (Pc s o r 2 Set.univ i) (Tst n (Tst n t η) η) := by
    intro i
    obtain ⟨G, hG⟩ := layers i
    exact ⟨G, hG.mono (fun p hp => ⟨hp.1, hp.2.2⟩) le_rfl⟩
  obtain ⟨G, hG⟩ := stack_interval W hs o r 2 cyl_univ (Tst_nonneg (Tst_nonneg ht hη) hη) hη hhol hpc n n
  exact ⟨G, hG.mono (fun p hp => ⟨hp, Set.mem_univ _, (hr _ hp 2).1, (hr _ hp 2).2⟩) le_rfl⟩

end AdalyFormal.UnifLane.Z
