import Q409L0

/-!
# Q409L1 -- coverage `CoversOm0p ell M 12 1 (TU ..)` for the union-of-slabs tower.

A set `T = AdjD N D x` (every coordinate equal to `x_rho`, or one step up on the coordinates allowed by `D`) that lies in `Om 0`
has a coordinate `rho` in which ALL its members lie in the slab `[A0,B0)` (mixing of coordinates); a box with a `12 M`-interval in
that coordinate inside the slab then lies in `Om 0`.  Same for `Om 1` with `12 M ell`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.M2Bridge
open AdalyFormal.GeneralClass
open AdalyFormal.M1 (strat strat_eq_iff IsPatch patch gsp)

/-- coordinatewise: equal, or one step up on the coordinates allowed by `D`. -/
def AdjD {L : PeriodicLatticeExtent} (N : ℕ) (D : Fin 3 → Prop) (x y : PeriodicLatticeSite L) : Prop :=
  ∀ ρ : Fin 3, (y ρ).val = (x ρ).val ∨ (D ρ ∧ (y ρ).val = ((x ρ).val + 1) % N)

theorem adjD_refl {L : PeriodicLatticeExtent} (N : ℕ) (D : Fin 3 → Prop) (x : PeriodicLatticeSite L) :
    AdjD N D x x := fun _ => Or.inl rfl

theorem adjD_shift {L : PeriodicLatticeExtent} {N : ℕ} {D : Fin 3 → Prop} (hN : ∀ μ, L μ + 1 = N) (hN1 : 1 < N)
    {x s : PeriodicLatticeSite L} (h : AdjD N D x s) (μ : Fin 3) (hμ : (s μ).val = (x μ).val) (hD : D μ) :
    AdjD N D x (periodicLatticeShift s μ) := by
  intro ρ
  rw [shift_valN hN hN1]
  by_cases hρ : ρ = μ
  · subst hρ; simp only [if_true]; right; exact ⟨hD, by rw [hμ]⟩
  · simp only [if_neg hρ]; exact h ρ

theorem mix_coord {L : PeriodicLatticeExtent} (T : PeriodicLatticeSite L → Prop) (Q : ℕ → Prop)
    (hmix : ∀ f : Fin 3 → PeriodicLatticeSite L, (∀ ρ, T (f ρ)) → T (fun ρ => f ρ ρ))
    (hall : ∀ y, T y → ∃ μ : Fin 3, Q (y μ).val) : ∃ ρ : Fin 3, ∀ y, T y → Q (y ρ).val := by
  by_contra h
  push Not at h
  choose f hf1 hf2 using h
  obtain ⟨μ, hμ⟩ := hall (fun ρ => f ρ ρ) (hmix f hf1)
  exact hf2 μ hμ

theorem adjD_mix {L : PeriodicLatticeExtent} (N : ℕ) (D : Fin 3 → Prop) (x : PeriodicLatticeSite L) :
    ∀ f : Fin 3 → PeriodicLatticeSite L, (∀ ρ, AdjD N D x (f ρ)) → AdjD N D x (fun ρ => f ρ ρ) :=
  fun _ hf ρ => hf ρ ρ

theorem corner_gen {s a b x0 : ℕ} (hs : 0 < s) (hsa : s ∣ a) (hsb : s ∣ b) (hab : a + 12 * s ≤ b)
    (h : a ≤ x0 ∧ x0 < b) :
    ∃ c0, s ∣ c0 ∧ a ≤ c0 ∧ c0 + 12 * s ≤ b ∧ c0 ≤ x0 ∧ x0 < c0 + 12 * s ∧
      (∀ w0, x0 ≤ w0 → w0 ≤ x0 + 1 → w0 < b → w0 < c0 + 12 * s) := by
  have hd := div_facts s x0 hs
  have hAt := align_ge hs hsa h.1
  by_cases ht : s * (x0 / s) ≤ b - 12 * s
  · exact ⟨s * (x0 / s), dvd_mul_right _ _, hAt, by omega, hd.1, by omega, fun w0 h1 h2 h3 => by omega⟩
  · exact ⟨b - 12 * s, Nat.dvd_sub hsb (Dvd.intro_left 12 rfl), by omega, by omega, by omega, by omega,
      fun w0 h1 h2 h3 => by omega⟩

theorem memBoxAll {L : PeriodicLatticeExtent} {N : ℕ} (hN : ∀ μ, L μ + 1 = N) (z y : PeriodicLatticeSite L) (s : ℕ) :
    y ∈ siteBox z s ↔ ∀ μ : Fin 3, ((y μ).val + N - (z μ).val) % N < s := by
  simp only [siteBox, Set.mem_setOf_eq, hN]

/-- a box of side `12 s` on the `s`-grid with a `12 s`-interval inside the slab `[a,b)` in coordinate `rho`
containing every member of `AdjD N D x`. -/
theorem box_exists {L : PeriodicLatticeExtent} {N s a b : ℕ} (hN : ∀ μ, L μ + 1 = N) (D : Fin 3 → Prop)
    (x : PeriodicLatticeSite L) (ρ : Fin 3)
    (hs : 0 < s) (hsa : s ∣ a) (hsb : s ∣ b) (hab : a + 12 * s ≤ b) (hbN : b ≤ N) (hapos : 0 < a)
    (h2s : 2 * s ≤ N)
    (hslab : ∀ y, AdjD N D x y → a ≤ (y ρ).val ∧ (y ρ).val < b) :
    ∃ z : PeriodicLatticeSite L, GridCorner s z ∧ a ≤ (z ρ).val ∧ (z ρ).val + 12 * s ≤ b ∧
      (∀ y, AdjD N D x y → y ∈ siteBox z (12 * s)) ∧
      (∀ y ∈ siteBox z (12 * s), a ≤ (y ρ).val ∧ (y ρ).val < b) := by
  have hx := hslab x (adjD_refl N D x)
  obtain ⟨c0, hc0d, hc0a, hc0b, hc0x, hc0y, hc0w⟩ := corner_gen hs hsa hsb hab hx
  have hc0N : c0 < N := by omega
  let c : Fin 3 → ℕ := fun μ => if μ = ρ then c0 else s * ((x μ).val / s)
  have hc : ∀ μ, c μ < L μ + 1 := fun μ => by
    have h1 := hN μ
    have h2 := site_lt hN x μ
    have h3 := (div_facts s (x μ).val hs).1
    simp only [c]; split_ifs <;> omega
  let z : PeriodicLatticeSite L := fun μ => ⟨c μ, hc μ⟩
  have hzρ : (z ρ).val = c0 := by simp [z, c]
  have hzo : ∀ μ, μ ≠ ρ → (z μ).val = s * ((x μ).val / s) := by
    intro μ h; simp [z, c, h]
  refine ⟨z, ?_, by omega, by omega, ?_, ?_⟩
  · intro μ
    by_cases h : μ = ρ
    · subst h; rw [hzρ]; exact Nat.mod_eq_zero_of_dvd hc0d
    · rw [hzo μ h]; exact Nat.mul_mod_right _ _
  · intro y hy
    rw [memBoxAll hN]
    intro μ
    by_cases hμ : μ = ρ
    · subst hμ
      rw [hzρ]
      have hys := hslab y hy
      have hyN := site_lt hN y μ
      have hx0N := site_lt hN x μ
      have hw := adj_coord N (x μ).val (y μ).val hx0N ((hy μ).imp id (fun h => h.2))
      have hw0 : (x μ).val ≤ (y μ).val ∧ (y μ).val ≤ (x μ).val + 1 := by
        rcases hw with h | h | h <;> omega
      have := hc0w (y μ).val hw0.1 hw0.2 hys.2
      rw [off_lt_iff _ _ _ _ hyN hc0N]
      omega
    · rw [hzo μ hμ]
      exact cell_off N s (12 * s) (x μ).val (y μ).val hs h2s (by omega) (site_lt hN x μ)
        ((hy μ).imp id (fun h => h.2))
  · intro y hy
    rw [memBoxAll hN] at hy
    have h1 := hy ρ
    have hyN := site_lt hN y ρ
    rw [hzρ, off_lt_iff _ _ _ _ hyN hc0N] at h1
    omega

theorem om0_congr {A0 A B B0 : ℕ} {L : PeriodicLatticeExtent} {y c : PeriodicLatticeSite L}
    (h : ∀ ρ, (y ρ).val = (c ρ).val) (hc : c ∈ (TU A0 A B B0 L).Om 0) : y ∈ (TU A0 A B B0 L).Om 0 := by
  obtain ⟨μ, hμ⟩ := (TU_om0 c).mp hc
  exact (TU_om0 y).mpr ⟨μ, by rw [h μ]; exact hμ⟩

theorem cover_main {L : PeriodicLatticeExtent} {N ell M A0 A B B0 : ℕ} (hN : ∀ μ, L μ + 1 = N)
    (hM : 0 < M) (hell : 2 ≤ ell)
    (hMA0 : M ∣ A0) (hMB0 : M ∣ B0) (hgA : M * ell ∣ A) (hgB : M * ell ∣ B)
    (hA0pos : 0 < A0) (hApos : 0 < A)
    (hW0 : A0 + 12 * M ≤ B0) (hW1 : A + 12 * (M * ell) ≤ B) (hB0N : B0 ≤ N) (hBN : B ≤ N)
    (hNb : 12 * M + 12 * (M * ell) ≤ N)
    (D : Fin 3 → Prop) (x : PeriodicLatticeSite L)
    (hT : ∀ y, AdjD N D x y → y ∈ (TU A0 A B B0 L).Om 0) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M 12 1 (TU A0 A B B0 L) sites j ∧
      ∀ y, AdjD N D x y → y ∈ sites := by
  have hg2 : M * 2 ≤ M * ell := Nat.mul_le_mul_left M hell
  have hg0 : 0 < M * ell := by omega
  by_cases hall : ∀ y, AdjD N D x y → y ∈ (TU A0 A B B0 L).Om 1
  · -- index 1
    obtain ⟨ρ, hρ⟩ := mix_coord (AdjD N D x) (fun v => A ≤ v ∧ v < B) (adjD_mix N D x)
      (fun y hy => (TU_om1 y).mp (hall y hy))
    obtain ⟨z, hgc, hz1, hz2, hbox, hsl⟩ := box_exists (s := M * ell) (a := A) (b := B) hN D x ρ hg0 hgA hgB hW1 hBN
      hApos (by omega) hρ
    have hzz : z ∈ siteBox z (12 * (M * ell)) := by
      rw [memBoxAll hN]
      intro μ
      have := site_lt hN z μ
      rw [off_lt_iff _ _ _ _ this this]; omega
    have hdesc : DescribedAt ell M 12 1 (TU A0 A B B0 L) (siteBox z (12 * bigSide M ell 1)) 1 := by
      rw [bigSide1]
      refine ⟨le_rfl, ⟨z, by rw [bigSide1]; exact hgc, by rw [bigSide1]⟩, ?_, ⟨z, hzz, ?_⟩⟩
      · intro y hy
        left
        rw [TU_bj1]
        exact ⟨ρ, hsl y hy⟩
      · rw [TU_bj1]; exact ⟨ρ, hz1, by omega⟩
    refine ⟨siteBox z (12 * bigSide M ell 1), 1, isClassCube_of hN hM hell hNb (le_refl 1) hdesc, ?_⟩
    intro y hy
    rw [bigSide1]; exact hbox y hy
  · -- index 0
    push Not at hall
    obtain ⟨y0, hy0, hy0n⟩ := hall
    obtain ⟨ρ, hρ⟩ := mix_coord (AdjD N D x) (fun v => A0 ≤ v ∧ v < B0) (adjD_mix N D x)
      (fun y hy => (TU_om0 y).mp (hT y hy))
    obtain ⟨z, hgc, hz1, hz2, hbox, hsl⟩ := box_exists (s := M) (a := A0) (b := B0) hN D x ρ hM hMA0 hMB0 hW0 hB0N
      hA0pos (by omega) hρ
    have hdesc : DescribedAt ell M 12 1 (TU A0 A B B0 L) (siteBox z (12 * bigSide M ell 0)) 0 := by
      rw [bigSide0]
      refine ⟨Nat.zero_le _, ⟨z, by rw [bigSide0]; exact hgc, by rw [bigSide0]⟩, ?_, ⟨y0, hbox y0 hy0, ?_⟩⟩
      · intro y hy
        by_cases h1 : y ∈ (TU A0 A B B0 L).Om 1
        · right
          exact (TU_bj1 y).mpr ((TU_om1 y).mp h1)
        · left
          rw [TU_bj0]
          exact ⟨⟨ρ, hsl y hy⟩, fun h => h1 ((TU_om1 y).mpr h)⟩
      · rw [TU_bj0]
        exact ⟨(TU_om0 y0).mp (hT y0 hy0), fun h => hy0n ((TU_om1 y0).mpr h)⟩
    refine ⟨siteBox z (12 * bigSide M ell 0), 0, isClassCube_of hN hM hell hNb (Nat.zero_le 1) hdesc, ?_⟩
    intro y hy
    rw [bigSide0]; exact hbox y hy

theorem TU_coversp {L : PeriodicLatticeExtent} {N ell M A0 A B B0 : ℕ} (hN : ∀ μ, L μ + 1 = N) (hN1 : 1 < N)
    (hM : 0 < M) (hell : 2 ≤ ell)
    (hMA0 : M ∣ A0) (hMB0 : M ∣ B0) (hgA : M * ell ∣ A) (hgB : M * ell ∣ B)
    (hA0pos : 0 < A0) (hApos : 0 < A)
    (hW0 : A0 + 12 * M ≤ B0) (hW1 : A + 12 * (M * ell) ≤ B) (hB0N : B0 ≤ N) (hBN : B ≤ N)
    (hNb : 12 * M + 12 * (M * ell) ≤ N) :
    CoversOm0p ell M 12 1 (TU A0 A B B0 L) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨sites, j, hc, hall⟩ := cover_main hN hM hell hMA0 hMB0 hgA hgB hA0pos hApos hW0 hW1 hB0N hBN hNb
      (fun _ => False) x (by
        intro y hy
        refine om0_congr (c := x) (fun ρ => ?_) hx
        rcases hy ρ with h | h
        · exact h
        · exact h.1.elim)
    exact ⟨sites, j, hc, hall x (adjD_refl N _ x)⟩
  · intro p hp
    have hmu : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
    have hnu : p.2.1.2 ≠ p.2.1.1 := fun h => hmu h.symm
    have hmem : ∀ e : PeriodicLatticeEdge L, e ∈ periodicPlaquetteBoundaryEdges p ↔
        (e = (p.1, p.2.1.1) ∨ e = (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) ∨
          e = (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) ∨ e = (p.1, p.2.1.2)) := by
      intro e
      simp [periodicPlaquetteBoundaryEdges]
    obtain ⟨m00, mμ⟩ := hp (p.1, p.2.1.1) ((hmem _).mpr (Or.inl rfl))
    obtain ⟨_, mν⟩ := hp (p.1, p.2.1.2) ((hmem _).mpr (Or.inr (Or.inr (Or.inr rfl))))
    obtain ⟨_, mμν⟩ := hp (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)
      ((hmem _).mpr (Or.inr (Or.inl rfl)))
    let D : Fin 3 → Prop := fun ρ => ρ = p.2.1.1 ∨ ρ = p.2.1.2
    have hDμ : D p.2.1.1 := Or.inl rfl
    have hDν : D p.2.1.2 := Or.inr rfl
    have hT : ∀ y, AdjD N D p.1 y → y ∈ (TU A0 A B B0 L).Om 0 := by
      intro y hy
      have hyμ : (y p.2.1.1).val = (p.1 p.2.1.1).val ∨ (y p.2.1.1).val = ((p.1 p.2.1.1).val + 1) % N :=
        (hy _).imp id (fun h => h.2)
      have hyν : (y p.2.1.2).val = (p.1 p.2.1.2).val ∨ (y p.2.1.2).val = ((p.1 p.2.1.2).val + 1) % N :=
        (hy _).imp id (fun h => h.2)
      have hyo : ∀ ρ, ρ ≠ p.2.1.1 → ρ ≠ p.2.1.2 → (y ρ).val = (p.1 ρ).val := by
        intro ρ h1 h2
        exact (hy ρ).elim id (fun h => absurd h.1 (fun h' => h'.elim h1 h2))
      rcases hyμ with h1 | h1 <;> rcases hyν with h2 | h2
      · refine om0_congr (c := p.1) (fun ρ => ?_) m00
        by_cases a1 : ρ = p.2.1.1
        · subst a1; exact h1
        · by_cases a2 : ρ = p.2.1.2
          · subst a2; exact h2
          · exact hyo ρ a1 a2
      · refine om0_congr (c := periodicLatticeShift p.1 p.2.1.2) (fun ρ => ?_) mν
        rw [shift_valN hN hN1]
        by_cases a2 : ρ = p.2.1.2
        · subst a2; simp only [if_true]; exact h2
        · simp only [if_neg a2]
          by_cases a1 : ρ = p.2.1.1
          · subst a1; exact h1
          · exact hyo ρ a1 a2
      · refine om0_congr (c := periodicLatticeShift p.1 p.2.1.1) (fun ρ => ?_) mμ
        rw [shift_valN hN hN1]
        by_cases a1 : ρ = p.2.1.1
        · subst a1; simp only [if_true]; exact h1
        · simp only [if_neg a1]
          by_cases a2 : ρ = p.2.1.2
          · subst a2; exact h2
          · exact hyo ρ a1 a2
      · refine om0_congr (c := periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2) (fun ρ => ?_) mμν
        rw [shift_valN hN hN1, shift_valN hN hN1]
        by_cases a2 : ρ = p.2.1.2
        · subst a2
          simp only [if_true, if_neg hnu]
          exact h2
        · simp only [if_neg a2]
          by_cases a1 : ρ = p.2.1.1
          · subst a1; simp only [if_true]; exact h1
          · simp only [if_neg a1]; exact hyo ρ a1 a2
    obtain ⟨sites, j, hc, hall⟩ := cover_main hN hM hell hMA0 hMB0 hgA hgB hA0pos hApos hW0 hW1 hB0N hBN hNb
      D p.1 hT
    refine ⟨sites, j, hc, fun e he => ?_⟩
    have a0 : AdjD N D p.1 p.1 := adjD_refl N D _
    have aμ : AdjD N D p.1 (periodicLatticeShift p.1 p.2.1.1) := adjD_shift hN hN1 a0 _ rfl hDμ
    have aν : AdjD N D p.1 (periodicLatticeShift p.1 p.2.1.2) := adjD_shift hN hN1 a0 _ rfl hDν
    have aμν : AdjD N D p.1 (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2) :=
      adjD_shift hN hN1 aμ _ (adjN_shift_coord hN hN1 _ hnu) hDν
    have aνμ : AdjD N D p.1 (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.2) p.2.1.1) :=
      adjD_shift hN hN1 aν _ (adjN_shift_coord hN hN1 _ hmu) hDμ
    refine ⟨?_, ?_⟩
    · rcases (hmem e).mp he with rfl | rfl | rfl | rfl
      · exact hall _ a0
      · exact hall _ aμ
      · exact hall _ aν
      · exact hall _ a0
    · rcases (hmem e).mp he with rfl | rfl | rfl | rfl
      · exact hall _ aμ
      · exact hall _ aμν
      · exact hall _ aνμ
      · exact hall _ aν

end AdalyFormal.P409
