import ZStatementP428
import AdalyFormal.Balaban.QjComposite
import AdalyFormal.Balaban.TowerLawCovariant

/-!
# ZR8Geo -- r8 locality, geometry layer: the periodic `ℓ¹` distance `pdist` (the statement's own, `ZStatementP428.pdist`),
balls, agreement of link configurations on a set of sites, and the collar facts read off `Admissible`.

Nothing here is new mathematics: triangle inequality of the circular distance, one shift moves `pdist` by at most `1`, a stride-`s`
path of length `n` stays in the `s n` ball, a strided block lies in the `3 s ell` ball, and `Admissible`'s collar conjunct
"`x ∉ Ω_j`, `y ∈ Ω_{j+1}` ⇒ `R M ell^j < |x - y|`" read as a ball inclusion.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace AdalyFormal.StatementLaneR8

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.TowerLawCov (coarsePathEndpoint coarseGammaPath coarseStraightSegment coarseCoordSteps)
open AdalyFormal.Balaban.QjComposite (stepBlockOf inStepBlock mem_stepBlockOf)

variable {L : PeriodicLatticeExtent}

/-! ## 1. the circular distance -/

theorem pcd_triangle (N a b c : ℕ) (_ha : a < N) (hb : b < N) (hc : c < N) :
    pcd N a c ≤ pcd N a b + pcd N b c := by
  unfold pcd
  simp only [min_def]
  split_ifs <;> omega

theorem pcd_comm (N a b : ℕ) : pcd N a b = pcd N b a := by
  unfold pcd
  split_ifs <;> omega

theorem pcd_self (N a : ℕ) : pcd N a a = 0 := by
  unfold pcd; simp

theorem pcd_le_diff (N a b : ℕ) (h : a ≤ b) : pcd N a b ≤ b - a := by
  unfold pcd; rw [if_pos h]; exact min_le_left _ _

theorem pcd_succ_le (n a : ℕ) (ha : a < n + 1) :
    pcd (n + 1) a (if a = n then 0 else a + 1) ≤ 1 := by
  unfold pcd
  split_ifs <;> simp only [min_def] <;> split_ifs <;> omega

/-! ## 2. `pdist` -/

theorem pdist_triangle (x y z : PeriodicLatticeSite L) : pdist x z ≤ pdist x y + pdist y z := by
  unfold pdist
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun μ _ => pcd_triangle _ _ _ _ (x μ).isLt (y μ).isLt (z μ).isLt)

theorem pdist_comm (x y : PeriodicLatticeSite L) : pdist x y = pdist y x := by
  unfold pdist
  exact Finset.sum_congr rfl (fun μ _ => pcd_comm _ _ _)

theorem pdist_self (x : PeriodicLatticeSite L) : pdist x x = 0 := by
  unfold pdist
  simp [pcd_self]

theorem pdist_shift_le (x : PeriodicLatticeSite L) (μ : Fin 3) : pdist x (periodicLatticeShift x μ) ≤ 1 := by
  unfold pdist
  rw [Finset.sum_eq_single μ]
  · show pcd (L μ + 1) (x μ).val (Function.update x μ (x μ + 1) μ).val ≤ 1
    rw [Function.update_self, Fin.val_add_one]
    have h := pcd_succ_le (L μ) (x μ).val (x μ).isLt
    by_cases hl : x μ = Fin.last (L μ)
    · have hv : (x μ).val = L μ := by rw [hl]; rfl
      rw [if_pos hl]; rw [if_pos hv] at h; exact h
    · have hv : (x μ).val ≠ L μ := fun e => hl (Fin.ext (by rw [e]; rfl))
      rw [if_neg hl]; rw [if_neg hv] at h; exact h
  · intro ν _ hν
    show pcd (L ν + 1) (x ν).val (Function.update x μ (x μ + 1) ν).val = 0
    rw [Function.update_of_ne hν, pcd_self]
  · intro h; exact absurd (Finset.mem_univ μ) h

theorem pdist_coarseShift_le (x : PeriodicLatticeSite L) (s : ℕ) (μ : Fin 3) : pdist x (coarseShift x s μ) ≤ s := by
  induction s with
  | zero => simp [coarseShift, pdist_self]
  | succ n ih =>
      have e : coarseShift x (n + 1) μ = periodicLatticeShift (coarseShift x n μ) μ := by
        unfold coarseShift
        rw [Function.iterate_succ_apply']
      rw [e]
      have h1 := pdist_triangle x (coarseShift x n μ) (periodicLatticeShift (coarseShift x n μ) μ)
      have h2 := pdist_shift_le (coarseShift x n μ) μ
      omega

/-! ## 3. balls and agreement -/

/-- the closed `ℓ¹` ball. -/
def Ball (y : PeriodicLatticeSite L) (r : ℕ) : Set (PeriodicLatticeSite L) := {z | pdist y z ≤ r}

theorem mem_Ball_self (y : PeriodicLatticeSite L) (r : ℕ) : y ∈ Ball y r := by
  show pdist y y ≤ r; rw [pdist_self]; exact Nat.zero_le _

theorem Ball_mono {y : PeriodicLatticeSite L} {r r' : ℕ} (h : r ≤ r') : Ball y r ⊆ Ball y r' :=
  fun _ hz => le_trans hz h

/-- a ball around a point at distance `d` of `y` is inside the ball around `y` of radius `d + r`. -/
theorem Ball_sub {y y' : PeriodicLatticeSite L} {d r R : ℕ} (hd : pdist y y' ≤ d) (hR : d + r ≤ R) :
    Ball y' r ⊆ Ball y R :=
  fun z hz => le_trans (pdist_triangle y y' z) (by have : pdist y' z ≤ r := hz; omega)

/-- two configurations agree at every bond based at a site of `W` (all three directions). -/
def AgreeAt {G : Type*} (W : Set (PeriodicLatticeSite L)) (U U' : PeriodicLinkConfiguration G L) : Prop :=
  ∀ z ∈ W, ∀ μ : Fin 3, U (z, μ) = U' (z, μ)

theorem AgreeAt.mono {G : Type*} {W W' : Set (PeriodicLatticeSite L)} {U U' : PeriodicLinkConfiguration G L}
    (h : AgreeAt W U U') (hW : W' ⊆ W) : AgreeAt W' U U' := fun z hz μ => h z (hW hz) μ

theorem AgreeAt.symm {G : Type*} {W : Set (PeriodicLatticeSite L)} {U U' : PeriodicLinkConfiguration G L}
    (h : AgreeAt W U U') : AgreeAt W U' U := fun z hz μ => (h z hz μ).symm

/-! ## 4. paths and blocks -/

theorem pdist_coarsePathEndpoint_le (s : ℕ) (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    pdist y (coarsePathEndpoint s y p) ≤ s * p.length := by
  induction p generalizing y with
  | nil => simp [coarsePathEndpoint, pdist_self]
  | cons μ rest ih =>
      show pdist y (coarsePathEndpoint s (coarseShift y s μ) rest) ≤ s * (rest.length + 1)
      have h1 := pdist_coarseShift_le y s μ
      have h2 := ih (coarseShift y s μ)
      have := pdist_triangle y (coarseShift y s μ) (coarsePathEndpoint s (coarseShift y s μ) rest)
      rw [Nat.mul_succ]; omega

/-- a strided block lies in the `3 s ell` ball of its base. -/
theorem pdist_stepBlock_le {y x : PeriodicLatticeSite L} {s ell : ℕ} (hx : x ∈ stepBlockOf y s ell) :
    pdist y x ≤ 3 * (s * ell) := by
  rw [mem_stepBlockOf] at hx
  unfold pdist
  have : ∀ μ : Fin 3, pcd (L μ + 1) (y μ).val (x μ).val ≤ s * ell := fun μ => by
    have h := hx μ
    exact le_trans (pcd_le_diff _ _ _ h.1) (by omega)
  calc ∑ μ : Fin 3, pcd (L μ + 1) (y μ).val (x μ).val ≤ ∑ _μ : Fin 3, s * ell := Finset.sum_le_sum (fun μ _ => this μ)
    _ = 3 * (s * ell) := by simp

theorem coarseCoordSteps_le {a b : PeriodicLatticeSite L} {s ell : ℕ} (μ : Fin 3) (hs : 0 < s)
    (h1 : (a μ).val ≤ (b μ).val) (h2 : (b μ).val < (a μ).val + s * ell) : coarseCoordSteps s a b μ ≤ ell := by
  unfold coarseCoordSteps
  rw [Fin.sub_val_of_le (show a μ ≤ b μ from h1)]
  exact le_trans (Nat.div_le_div_right (show (b μ).val - (a μ).val ≤ s * ell by omega)) (by rw [Nat.mul_div_cancel_left _ hs])

/-- the staircase from `y` to a point of its strided block has at most `3 ell` steps. -/
theorem length_coarseGammaPath_le {y x : PeriodicLatticeSite L} {s ell : ℕ} (hs : 0 < s) (hx : x ∈ stepBlockOf y s ell) :
    (coarseGammaPath s y x).length ≤ 3 * ell := by
  rw [mem_stepBlockOf] at hx
  unfold coarseGammaPath coarseStraightSegment
  simp only [List.length_append, List.length_replicate]
  have e1 : (Function.update y 2 (x 2)) 1 = y 1 := Function.update_of_ne (by decide) _ _
  have e0 : (Function.update (Function.update y 2 (x 2)) 1 (x 1)) 0 = y 0 := by
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
  have h2 := coarseCoordSteps_le (a := y) (b := x) (ell := ell) 2 hs (hx 2).1 (hx 2).2.1
  have h1 : coarseCoordSteps s (Function.update y 2 (x 2)) x 1 ≤ ell :=
    coarseCoordSteps_le (ell := ell) 1 hs (by rw [e1]; exact (hx 1).1) (by rw [e1]; exact (hx 1).2.1)
  have h0 : coarseCoordSteps s (Function.update (Function.update y 2 (x 2)) 1 (x 1)) x 0 ≤ ell :=
    coarseCoordSteps_le (ell := ell) 0 hs (by rw [e0]; exact (hx 0).1) (by rw [e0]; exact (hx 0).2.1)
  omega

/-! ## 5. the collar of `Admissible` as ball inclusions -/

/-- `Admissible`, conjunct 5, as an inclusion: the `R M ell^j` ball around a point of `Ω_{j+1}` lies in `Ω_j` (`j ≤ k`). -/
theorem admissible_ball {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) {j : ℕ} (hj : j ≤ k)
    {y : PeriodicLatticeSite L} (hy : y ∈ S.Om (j + 1)) : Ball y (R * bigSide M ell j) ⊆ S.Om j := by
  intro x hx
  by_contra hxn
  have := hS.2.2.2.2.1 j hj x hxn y hy
  have hx' : pdist y x ≤ R * bigSide M ell j := hx
  rw [pdist_comm] at hx'
  omega

theorem admissible_mono {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) :
    ∀ j, S.Om j ⊆ S.Om 0 := by
  intro j
  induction j with
  | zero => exact le_rfl
  | succ j ih => exact le_trans (hS.1 j) ih

/-- the `R M ell^(j-1)` ball around a point of `Ω_j` (`1 ≤ j ≤ k + 1`) lies in `Ω₀`. -/
theorem admissible_ball_Om0 {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) {j : ℕ} (hj1 : 1 ≤ j)
    (hjk : j ≤ k + 1) {y : PeriodicLatticeSite L} (hy : y ∈ S.Om j) :
    Ball y (R * (M * ell ^ (j - 1))) ⊆ S.Om 0 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have := admissible_ball hS (j := i) (by omega) hy
  simp only [Nat.add_sub_cancel]
  exact le_trans this (admissible_mono hS i)

#print axioms pcd_triangle
#print axioms pdist_triangle
#print axioms pdist_shift_le
#print axioms pdist_coarseShift_le
#print axioms pdist_coarsePathEndpoint_le
#print axioms pdist_stepBlock_le
#print axioms length_coarseGammaPath_le
#print axioms admissible_ball
#print axioms admissible_ball_Om0

end AdalyFormal.StatementLaneR8
