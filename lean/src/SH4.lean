import SH3

/-!
# SH4 -- the "lone block" tower: `Omega_m` = one level-`m` block, `Omega_i` (`i < m`) the minimal admissible neighbourhoods, `Omega_i = empty` for `i > m`.

`nbhdOp gi rad X` = `{x | exists y in X, exists z in the gi-block of x, pdist z y <= rad}` (the form of the `Omega_0` clause of `Admissible`).
`loneOm ell M R m X i` : `X` at `i = m`, `nbhdOp (M ell^i) (R M ell^i) (loneOm (i+1))` for `i < m`, `empty` for `i > m`.
`lone_admissible`: for ANY `R`, `1 <= m <= k`, block-closed `X`, and `M ell^k | N`, this is an `Admissible ell M R k` tower.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409S

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.M2Bridge
open AdalyFormal.GeneralClass
open AdalyFormal.P409
open AdalyFormal.P409W
open AdalyFormal.P409C5
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_triangle)

variable {L : PeriodicLatticeExtent}

/-- the `gi`-block `rad`-neighbourhood: some point of the `gi`-block of `x` is within `l^1` distance `rad` of a point of `X`. -/
def nbhdOp (gi rad : ℕ) (X : Set (PeriodicLatticeSite L)) : Set (PeriodicLatticeSite L) :=
  {x | ∃ y ∈ X, ∃ z : PeriodicLatticeSite L, (∀ μ : Fin 3, (z μ).val / gi = (x μ).val / gi) ∧ pdist z y ≤ rad}

/-- `chainOm .. d` = the set of level `m - d`. -/
def chainOm (ell M R m : ℕ) (X : Set (PeriodicLatticeSite L)) : ℕ → Set (PeriodicLatticeSite L)
  | 0 => X
  | d + 1 => nbhdOp (bigSide M ell (m - (d + 1))) (R * bigSide M ell (m - (d + 1))) (chainOm ell M R m X d)

def loneOm (ell M R m : ℕ) (X : Set (PeriodicLatticeSite L)) (i : ℕ) : Set (PeriodicLatticeSite L) :=
  if i ≤ m then chainOm ell M R m X (m - i) else ∅

def loneTower (ell M R m : ℕ) (X : Set (PeriodicLatticeSite L)) : Tower L := ⟨loneOm ell M R m X⟩

theorem loneOm_top (ell M R m : ℕ) (X : Set (PeriodicLatticeSite L)) : loneOm ell M R m X m = X := by
  simp [loneOm, chainOm]

theorem loneOm_above (ell M R m : ℕ) (X : Set (PeriodicLatticeSite L)) {i : ℕ} (h : m < i) :
    loneOm ell M R m X i = ∅ := by
  simp [loneOm, show ¬ i ≤ m by omega]

theorem loneOm_below (ell M R m : ℕ) (X : Set (PeriodicLatticeSite L)) {i : ℕ} (h : i < m) :
    loneOm ell M R m X i = nbhdOp (bigSide M ell i) (R * bigSide M ell i) (loneOm ell M R m X (i + 1)) := by
  obtain ⟨d, hd⟩ : ∃ d, m - i = d + 1 := ⟨m - i - 1, by omega⟩
  have e1 : m - (i + 1) = d := by omega
  have e2 : m - (d + 1) = i := by omega
  simp only [loneOm, show i ≤ m by omega, show i + 1 ≤ m by omega, if_true, hd, e1, chainOm, e2]

theorem nbhd_blockClosed (gi rad : ℕ) (Y : Set (PeriodicLatticeSite L)) : BlockClosed gi (nbhdOp gi rad Y) := by
  intro x hx y hxy
  obtain ⟨w, hw, z, hz, hd⟩ := hx
  exact ⟨w, hw, z, fun μ => (hz μ).trans (hxy μ).symm, hd⟩

theorem subset_nbhd (gi rad : ℕ) (Y : Set (PeriodicLatticeSite L)) : Y ⊆ nbhdOp gi rad Y := by
  intro y hy
  exact ⟨y, hy, y, fun μ => rfl, by rw [pdist_self]; exact Nat.zero_le _⟩

theorem lone_admissible {ell M R k m : ℕ} {X : Set (PeriodicLatticeSite L)} (hm : 1 ≤ m) (hmk : m ≤ k)
    (hX : BlockClosed (bigSide M ell m) X) (hdiv : ∀ μ : Fin 3, bigSide M ell k ∣ L μ + 1) :
    Admissible ell M R k (loneTower ell M R m X) := by
  have hOm : ∀ i, (loneTower ell M R m X).Om i = loneOm ell M R m X i := fun i => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [hOm, hOm]
    by_cases hj : j + 1 ≤ m
    · rw [loneOm_below ell M R m X (show j < m by omega)]
      exact subset_nbhd _ _ _
    · rw [loneOm_above ell M R m X (show m < j + 1 by omega)]
      exact Set.empty_subset _
  · intro j hj
    rw [hOm]
    exact loneOm_above ell M R m X (by omega)
  · intro j hj μ
    exact dvd_trans (bigSide_dvd' M ell hj) (hdiv μ)
  · intro j hj
    rw [hOm]
    by_cases hjm : j < m
    · rw [loneOm_below ell M R m X hjm]
      exact nbhd_blockClosed _ _ _
    · by_cases hjm' : j = m
      · subst hjm'
        rw [loneOm_top]; exact hX
      · rw [loneOm_above ell M R m X (show m < j by omega)]
        intro x hx; exact absurd hx (Set.notMem_empty _)
  · intro j hj x hx y hy
    rw [hOm] at hx hy
    by_cases hjm : j + 1 ≤ m
    · rw [loneOm_below ell M R m X (show j < m by omega)] at hx
      by_contra hle
      push Not at hle
      exact hx ⟨y, hy, x, fun μ => rfl, hle⟩
    · rw [loneOm_above ell M R m X (show m < j + 1 by omega)] at hy
      exact absurd hy (Set.notMem_empty _)
  · intro x
    show x ∈ loneOm ell M R m X 0 ↔ _
    rw [loneOm_below ell M R m X (show 0 < m by omega), bigSide_zero]
    exact Iff.rfl

end AdalyFormal.P409S
