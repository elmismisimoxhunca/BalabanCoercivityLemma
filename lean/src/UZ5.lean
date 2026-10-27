import UZ4
import UA

/-!
# UZ5 -- the COVER_GEOM interface and `BallChartsGU` for `j ≤ 1` (lane unif_20261016)

* `BallHyp` : the hypotheses of `OneGap.BallChartsAtG` on `(j, w, r)`; `ballChartsAtG_iff`.
* `CoverGeomZ W s o r a1 a2` (`j ≤ 1`) : in ball coordinates, cells `cellZ s o` (side `s`, offset `o`): every cell of `Bz r`
  carries one gauge with clause 1 at `a1`, and every plaquette of `Bz r` has holonomy within `a2` of `1`.
* `CoverGeomBox W s o n a1 a2` (`j ≥ 2`) : every full cell and every face-adjacent pair of full cells of the box of cells within `n`
  of the centre cell carries one gauge with clause 1 at `a1` and clause 2 at `a2`; plaquette bound `a2` on the box.
* `CoverGeomU`, `CoverGeomBoxU` : **THE INTERFACE** (owned by the cover_geom lane), at every admissible ball (`j ≤ 1`, resp. `j ≥ 2`),
  cell side `bigSide M ℓ (j-1)`, offset the torus coordinates of `w`, constants `c X1 = c·12Mα₀ℓ^{-(j-1)}`,
  `c X2 = c·12Mα₀ℓ^{-2(j-1)}`, `c` and the threshold depending on `ℓ` only (the `ClassFamU` shape).
* `BallChartsGUJ P` : `BallChartsGU` restricted to the levels `j` with `P j`; `ballChartsGU_of_split` :
  `BallChartsGUJ (· ≤ 1)` and `BallChartsGUJ (2 ≤ ·)` give `BallChartsGU`.
* `ballChartsGUJ_le1 : CoverGeomU → BallChartsGUJ (· ≤ 1)` (clause 2 follows from clause 1 at scale `ℓ⁰`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.UnifLane.Z

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK pdist bigSide)
open AdalyFormal.StatementLane2 (ClassCoupled)
open AdalyFormal.StatementLaneG (LambdaOK2)
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.M2Glue3 (Z3 ev)
open AdalyFormal.M2Glue2 (GChart GChart.mono)
open AdalyFormal.M2BallCharts (Bz)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.UnifLane (ClassFamU BallChartsGU)

variable {L : PeriodicLatticeExtent}

/-- the ball hypotheses of `BallChartsAtG`. -/
def BallHyp (ell M k : ℕ) (S : Tower L) (j : ℕ) (w : PeriodicLatticeSite L) (r : ℕ) : Prop :=
  j ≤ k ∧ (∃ x₀ ∈ S.Om j, pdist w x₀ ≤ 3 * (M * ell ^ j)) ∧ r ≤ 7 * M * ell ^ j ∧ (∀ σ : Fin 3, 2 * r + 2 ≤ L σ + 1) ∧
    (∀ x ∈ Ball w r, x ∈ S.Om (j - 1)) ∧ (∀ x ∈ Ball w r, x ∉ S.Om (j + 2)) ∧
    (r ≤ 1000 * ell ^ (j + 1) ∨ ∀ x ∈ Ball w r, x ∉ S.Om (j + 1))

/-- the two chart constants of `BallChartsAtG` at level `j` (without the factor `C`). -/
noncomputable def X1 (ell M : ℕ) (α₀ : ℝ) (j : ℕ) : ℝ := ((12 : ℕ) : ℝ) * M * α₀ * ((ell : ℝ) ^ (j - 1))⁻¹
noncomputable def X2 (ell M : ℕ) (α₀ : ℝ) (j : ℕ) : ℝ := ((12 : ℕ) : ℝ) * M * α₀ * (((ell : ℝ) ^ (j - 1))⁻¹) ^ 2

/-- `BallChartsAtG` restricted to the levels with `P j`. -/
def BallChartsAtGJ (P : ℕ → Prop) (ell M k : ℕ) (S : Tower L) (U : LinkCfg L) (C α₀ : ℝ) : Prop :=
  ∀ j w r, P j → BallHyp ell M k S j w r → ∃ g : PeriodicLatticeSite L → SU2,
    GChart U g (Ball w r) (C * X1 ell M α₀ j) (C * X2 ell M α₀ j)

theorem ballChartsAtG_of_J {ell M k : ℕ} {S : Tower L} {U : LinkCfg L} {C α₀ η : ℝ}
    (h : ∀ j w r, BallHyp ell M k S j w r → ∃ g : PeriodicLatticeSite L → SU2,
      GChart U g (Ball w r) (C * X1 ell M α₀ j) (C * X2 ell M α₀ j)) :
    AdalyFormal.OneGap.BallChartsAtG ell M k S U C α₀ η := by
  intro j hjk w hw r hr7 hnw hin hout hsm
  exact h j w r ⟨hjk, hw, hr7, hnw, hin, hout, hsm⟩

/-- `BallChartsGU` restricted to the levels with `P j`. -/
def BallChartsGUJ (P : ℕ → Prop) : Prop :=
  ∀ (ell : ℕ), 2 ≤ ell →
    ClassFamU ell ℝ (fun _ _ C => 1 ≤ C) (fun M _ k _ C S Lam U α₀ => BallChartsAtGJ P ell M k S U C α₀)

theorem X1_nonneg {ell M : ℕ} {α₀ : ℝ} (hα : 0 ≤ α₀) (j : ℕ) : 0 ≤ X1 ell M α₀ j := by unfold X1; positivity
theorem X2_nonneg {ell M : ℕ} {α₀ : ℝ} (hα : 0 ≤ α₀) (j : ℕ) : 0 ≤ X2 ell M α₀ j := by unfold X2; positivity

/-- **the two halves give the residual.** -/
theorem ballChartsGU_of_split (h1 : BallChartsGUJ (· ≤ 1)) (h2 : BallChartsGUJ (2 ≤ ·)) : BallChartsGU := by
  intro ell hell
  obtain ⟨m₁, R₁, C₁, s₁, hs₁, hf₁⟩ := h1 ell hell
  obtain ⟨m₂, R₂, C₂, s₂, hs₂, hf₂⟩ := h2 ell hell
  refine ⟨max m₁ m₂, max R₁ R₂, max C₁ C₂, min s₁ s₂, lt_min hs₁ hs₂, fun m hm R hR => ⟨?_, ?_⟩⟩
  · exact le_max_of_le_left (hf₁ m (le_of_max_le_left hm) R (le_of_max_le_left hR)).1
  intro k hk Lu α₀ hα hsα hT S hS Lam hL U hU hloc
  refine ballChartsAtG_of_J (fun j w r hB => ?_)
  rcases le_or_gt j 1 with hj | hj
  · obtain ⟨-, hf⟩ := hf₁ m (le_of_max_le_left hm) R (le_of_max_le_left hR)
    obtain ⟨g, hg⟩ := hf k hk Lu α₀ hα (hsα.trans (min_le_left _ _)) hT S hS Lam hL U hU hloc j w r hj hB
    exact ⟨g, hg.mono subset_rfl (mul_le_mul_of_nonneg_right (le_max_left _ _) (X1_nonneg hα.le j))
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (X2_nonneg hα.le j))⟩
  · obtain ⟨-, hf⟩ := hf₂ m (le_of_max_le_right hm) R (le_of_max_le_right hR)
    obtain ⟨g, hg⟩ := hf k hk Lu α₀ hα (hsα.trans (min_le_right _ _)) hT S hS Lam hL U hU hloc j w r hj hB
    exact ⟨g, hg.mono subset_rfl (mul_le_mul_of_nonneg_right (le_max_right _ _) (X1_nonneg hα.le j))
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (X2_nonneg hα.le j))⟩

/-! ## the interface -/

/-- the cell of `c` in the ball. -/
def cellSet (s : ℤ) (o : Z3) (r : ℕ) (c : Z3) : Set Z3 := {p | p ∈ Bz r ∧ ∀ μ, cellZ s o p μ = c μ}

/-- cell charts + plaquette bound in ball coordinates (the `j ≤ 1` interface). -/
def CoverGeomZ (W : Z3 → Fin 3 → SU2) (s : ℤ) (o : Z3) (r : ℕ) (a1 a2 : ℝ) : Prop :=
  (∀ c : Z3, ∃ G : Z3 → SU2, C1 W G (cellSet s o r c) a1) ∧ HolB W (Bz r) a2

/-- the full cells of a box of cells (the `j ≥ 2` interface). -/
def cellBox (s : ℤ) (o : Z3) (c : Z3) : Set Z3 := {p | ∀ μ, cellZ s o p μ = c μ}

/-- the box of cells within `n` of the centre cell. -/
def BoxR (s : ℤ) (o : Z3) (n : ℕ) : Set Z3 := {p | ∀ μ, o μ / s - n ≤ cellZ s o p μ ∧ cellZ s o p μ ≤ o μ / s + n}

/-- cell and face-adjacent PAIR charts (clauses 1 and 2) on the full cells of the box, and the plaquette bound on the box. -/
def CoverGeomBox (W : Z3 → Fin 3 → SU2) (s : ℤ) (o : Z3) (n : ℕ) (a1 a2 : ℝ) : Prop :=
  (∀ c c' : Z3, (∀ μ, o μ / s - n ≤ c μ ∧ c μ ≤ o μ / s + n) → (∀ μ, o μ / s - n ≤ c' μ ∧ c' μ ≤ o μ / s + n) →
      (c' = c ∨ ∃ μ, c' = c + ev μ) → ∃ G : Z3 → SU2,
      C1 W G (cellBox s o c ∪ cellBox s o c') a1 ∧ C2 W G (cellBox s o c ∪ cellBox s o c') a2) ∧
    HolB W (BoxR s o n) a2

/-- the torus coordinates of the centre. -/
def wo (w : PeriodicLatticeSite L) : Z3 := fun μ => ((w μ).val : ℤ)

/-- **COVER_GEOM INTERFACE, `j ≤ 1` part** (cells of the `ℓ¹` ball, clause 1). -/
def CoverGeomU : Prop :=
  ∀ (ell : ℕ), 2 ≤ ell →
    ClassFamU ell ℝ (fun _ _ c => 1 ≤ c) (fun M _ k _ c S Lam U α₀ =>
      ∀ j w r, j ≤ 1 → BallHyp ell M k S j w r →
        CoverGeomZ (Wof U w) ((bigSide M ell (j - 1) : ℕ) : ℤ) (wo w) r (c * X1 ell M α₀ j) (c * X2 ell M α₀ j))

/-- **COVER_GEOM INTERFACE, `j ≥ 2` part** (full cells of the box of `7ℓ` cells around the centre; pairs; clauses 1, 2). -/
def CoverGeomBoxU : Prop :=
  ∀ (ell : ℕ), 2 ≤ ell →
    ClassFamU ell ℝ (fun _ _ c => 1 ≤ c) (fun M _ k _ c S Lam U α₀ =>
      ∀ j w r, 2 ≤ j → BallHyp ell M k S j w r →
        CoverGeomBox (Wof U w) ((bigSide M ell (j - 1) : ℕ) : ℤ) (wo w) (7 * ell) (c * X1 ell M α₀ j) (c * X2 ell M α₀ j))

/-! ## `j ≤ 1` -/

theorem Tst_le {n : ℕ} {t η A : ℝ} (ht : t ≤ A) (hη : η ≤ A) (h0 : 0 ≤ η) (ht0 : 0 ≤ t) :
    Tst n t η ≤ (1 + 6 * n) * A := by
  unfold Tst
  have hn : (0 : ℝ) ≤ n := by positivity
  nlinarith

theorem T3_le {n : ℕ} {t η A : ℝ} (ht : t ≤ A) (hη : η ≤ A) (h0 : 0 ≤ η) (ht0 : 0 ≤ t) :
    Tst n (Tst n (Tst n t η) η) η ≤ (1 + 6 * n) ^ 3 * A := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn : (1 : ℝ) ≤ 1 + 6 * n := by linarith
  have hA : 0 ≤ A := ht0.trans ht
  have l1 := Tst_le (n := n) ht hη h0 ht0
  have l1' : η ≤ (1 + 6 * n) * A := hη.trans (by nlinarith)
  have l2 := Tst_le (n := n) l1 l1' h0 (Tst_nonneg ht0 h0)
  have l2' : η ≤ (1 + 6 * n) * ((1 + 6 * n) * A) := l1'.trans (by nlinarith)
  have l3 := Tst_le (n := n) l2 l2' h0 (Tst_nonneg (Tst_nonneg ht0 h0) h0)
  calc _ ≤ (1 + 6 * (n : ℝ)) * ((1 + 6 * n) * ((1 + 6 * n) * A)) := l3
    _ = (1 + 6 * n) ^ 3 * A := by ring

theorem cellSet_union_self (s : ℤ) (o : Z3) (r : ℕ) (c : Z3) : cellSet s o r c ∪ cellSet s o r c = cellSet s o r c :=
  Set.union_self _

/-- **`BallChartsGU` for `j ≤ 1` from the interface.** -/
theorem ballChartsGUJ_le1 (hCG : CoverGeomU) : BallChartsGUJ (· ≤ 1) := by
  intro ell hell
  obtain ⟨m₁, R₁, c, sG, hsG, hF⟩ := hCG ell hell
  have hc1 : 1 ≤ c := (hF m₁ le_rfl R₁ le_rfl).1
  set C : ℝ := 2 * (1 + 6 * ((7 * ell : ℕ) : ℝ)) ^ 3 * c with hC
  have hCc : 1 ≤ C := by
    have h7 : (0 : ℝ) ≤ ((7 * ell : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 : (1 : ℝ) ≤ 1 + 6 * ((7 * ell : ℕ) : ℝ) := by linarith
    have : (1 : ℝ) ≤ (1 + 6 * ((7 * ell : ℕ) : ℝ)) ^ 3 := one_le_pow₀ h1
    rw [hC]; nlinarith
  refine ⟨m₁, R₁, C, sG, hsG, fun m hm R hR => ⟨hCc, ?_⟩⟩
  intro k hk Lu α₀ hα hsα hT S hS Lam hLam U hU hloc j w r hj hB
  have hCZ := (hF m hm R hR).2 k hk Lu α₀ hα hsα hT S hS Lam hLam U hU hloc j w r hj hB
  obtain ⟨hcells, hhol⟩ := hCZ
  have hj0 : j - 1 = 0 := by omega
  have hX1 : X1 ell (ell ^ m) α₀ j = ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ := by
    unfold X1; rw [hj0]; simp
  have hX2 : X2 ell (ell ^ m) α₀ j = ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ := by
    unfold X2; rw [hj0]; simp
  set X : ℝ := ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ with hXd
  have hX0 : 0 ≤ X := by positivity
  have hs : (0 : ℤ) < ((bigSide (ell ^ m) ell (j - 1) : ℕ) : ℤ) := by
    have : 0 < bigSide (ell ^ m) ell (j - 1) := Nat.mul_pos (pow_pos (by omega) m) (pow_pos (by omega) _)
    exact_mod_cast this
  have hrn : (r : ℤ) ≤ ((7 * ell : ℕ) : ℤ) * ((bigSide (ell ^ m) ell (j - 1) : ℕ) : ℤ) := by
    obtain ⟨-, -, hr7, -⟩ := hB
    have hpj : ell ^ j ≤ ell := by
      rcases Nat.lt_or_ge j 1 with h | h
      · have : j = 0 := by omega
        subst this; simp; omega
      · have : j = 1 := by omega
        subst this; simp
    have hb : bigSide (ell ^ m) ell (j - 1) = ell ^ m := by simp [bigSide, hj0]
    rw [hb]
    have : r ≤ 7 * ell * ell ^ m := by
      calc r ≤ 7 * ell ^ m * ell ^ j := hr7
        _ ≤ 7 * ell ^ m * ell := Nat.mul_le_mul_left _ hpj
        _ = 7 * ell * ell ^ m := by ring
    exact_mod_cast this
  have hcellc : ∀ cc : Z3, ∃ G, C1 (Wof U w) G {p | p ∈ Bz r ∧ ∀ μ,
      cellZ ((bigSide (ell ^ m) ell (j - 1) : ℕ) : ℤ) (wo w) p μ = cc μ} (c * X) := by
    intro cc
    obtain ⟨G, hG1⟩ := hcells cc
    rw [hX1] at hG1
    exact ⟨G, hG1⟩
  rw [hX2] at hhol
  have hcX : 0 ≤ c * X := by positivity
  obtain ⟨G, hG⟩ := ball_chart1 (Wof U w) hs (wo w) hrn hcX hcX hhol hcellc
  have hT3 := T3_le (n := 7 * ell) (le_refl (c * X)) (le_refl (c * X)) hcX hcX
  have hL : ∀ μ, 2 * r + 1 < scaleUp ell k Lu μ + 1 := fun μ => by have := hB.2.2.2.1 μ; omega
  obtain ⟨g, hg⟩ := gchart_of_C12 U w hL hG (C2_of_C1 hG)
  refine ⟨g, hg.mono subset_rfl ?_ ?_⟩
  · calc _ ≤ (1 + 6 * ((7 * ell : ℕ) : ℝ)) ^ 3 * (c * X) := hT3
      _ ≤ C * X := by rw [hC]; nlinarith [pow_pos (show (0 : ℝ) < 1 + 6 * ((7 * ell : ℕ) : ℝ) by positivity) 3]
      _ = C * X1 ell (ell ^ m) α₀ j := by rw [hX1]
  · calc _ ≤ 2 * ((1 + 6 * ((7 * ell : ℕ) : ℝ)) ^ 3 * (c * X)) := by linarith
      _ = C * X := by rw [hC]; ring
      _ = C * X2 ell (ell ^ m) α₀ j := by rw [hX2]

end AdalyFormal.UnifLane.Z
