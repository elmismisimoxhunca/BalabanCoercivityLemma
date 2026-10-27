import TL1

/-!
# TL2 -- `tower_FG_gen` (tower_FG for an arbitrary background tower) and `rows_FG_loc`
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.TowerLoc

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (scaleUp pdist)
open AdalyFormal.StatementLaneR8
open AdalyFormal.BondComposite
open SmallnessBridge.Assemble (loopFactorBound)
open EstimatesLayer.E1E3
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

section gen
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent)

/-- `tower_FG` (BC5) for an ARBITRARY background tower `bg` (the class is used only through the per-level aligned-link bound). -/
theorem tower_FG_gen (hell : 0 < ell) (bg : ℕ → PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)) (ε : ℕ → ℝ)
    (hreg : RegTower ell bg k)
    (hcl : ∀ j, j < k → ∀ y ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ j), ∀ μ : Fin 3,
      frobNorm (((bg j (y, μ) : SU2) : M2) - 1) ≤ ε j)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (a : XS (scaleUp ell k Lu)) :
    ∀ j, j ≤ k →
      nrm (ell ^ j) (QlinCompX ell bg j a)
        ≤ (rr ell) ^ j * Real.exp ((∑ i ∈ Finset.range j, thetaOf ell (ε i)) / rr ell) * nrm 1 a
      ∧ nrm (ell ^ j) (QlinCompX ell bg j a - QlinCompX ell (flatBg ell k Lu) j a)
        ≤ (rr ell) ^ j * ((∑ i ∈ Finset.range j, thetaOf ell (ε i)) / rr ell)
            * Real.exp ((∑ i ∈ Finset.range j, thetaOf ell (ε i)) / rr ell) * nrm 1 a := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hr : 0 < rr ell := Real.sqrt_pos.mpr (by positivity)
  have hstep : ∀ j, j < k →
      nrm (ell ^ (j + 1)) (QlinCompX ell bg (j + 1) a)
          ≤ (rr ell + thetaOf ell (ε j)) * nrm (ell ^ j) (QlinCompX ell bg j a)
      ∧ nrm (ell ^ (j + 1)) (QlinCompX ell bg (j + 1) a - QlinCompX ell (flatBg ell k Lu) (j + 1) a)
          ≤ rr ell * nrm (ell ^ j) (QlinCompX ell bg j a - QlinCompX ell (flatBg ell k Lu) j a)
            + thetaOf ell (ε j) * nrm (ell ^ j) (QlinCompX ell bg j a) := by
    intro j hjk
    have hs := hsLq ell k Lu hell j hjk.le
    have hV : ∀ e : PeriodicLatticeEdge (scaleUp ell (k - j) Lu),
        frobNorm (((resV hs (bg j)) e : M2) - 1) ≤ ε j := by
      intro e
      have hmem : embS hs e.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ j) := by
        rw [mem_CoarseLattice]
        intro μ
        rw [embS_val]
        exact Nat.mul_mod_right _ _
      exact hcl j hjk _ hmem e.2
    have := step_bounds ell bg (flatBg ell k Lu) k hreg (regTower_flat ell k Lu hell k) j hjk hs hell
      (hdvdLq ell k Lu hell j hjk) (ε j) (hε0 j hjk) hV (hsm j hjk) rfl a
    rw [← pow_succ, mul_one] at this
    exact this
  have hX : 0 ≤ nrm 1 a := nrm_nonneg _ _
  exact seq_bound k (rr ell) hr (fun j => thetaOf ell (ε j))
    (fun j => nrm (ell ^ j) (QlinCompX ell bg j a))
    (fun j => nrm (ell ^ j) (QlinCompX ell bg j a - QlinCompX ell (flatBg ell k Lu) j a)) (nrm 1 a) hX
    (fun j hj => thetaOf_nonneg ell _ (hε0 j hj))
    (by simp [QlinCompX_zero_apply])
    (by simp only [QlinCompX_zero_apply, sub_self, nrm_zero])
    (fun j hj => (hstep j hj).1) (fun j hj => (hstep j hj).2)

end gen

variable {L : PeriodicLatticeExtent}

/-- rows of a finite set of `m`-aligned bonds against the whole level-`m` coarse sum -/
theorem rows_sum_le (m : ℕ) (X : Finset (PeriodicLatticeEdge L)) (hX : ∀ b ∈ X, b.1 ∈ CoarseLattice L m)
    (Z : XS L) : ∑ b ∈ X, ‖suOf (Z b)‖ ^ 2 ≤ nrm m Z ^ 2 := by
  classical
  rw [nrm_sq]
  let φ : X → CoarseBond L m := fun b => (⟨b.1.1, hX b.1 b.2⟩, b.1.2)
  have hφ : Function.Injective φ := by
    intro b b' h
    apply Subtype.ext
    exact Prod.ext (congrArg (fun c : CoarseBond L m => c.1.1) h) (congrArg (fun c : CoarseBond L m => c.2) h)
  have h := sum_le_of_injective φ hφ (fun c : CoarseBond L m => ‖suOf (Z (c.1.1, c.2))‖ ^ 2) (fun _ => sq_nonneg _)
  rw [← Finset.sum_coe_sort X]
  exact h

/-- **`tower_FG_loc`**: bounds for the rows `X` of level `j` of the LOCAL composite `QlinCompL`, with the class
assumed only on `W l` (regional `ε`), `W l ⊇ Ball b₋ (rhoT j - rhoT l)` for `b ∈ X`.  -/
theorem rows_FG_loc (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (bg : ℕ → PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)) (ε : ℕ → ℝ)
    (W : ℕ → Set (PeriodicLatticeSite (scaleUp ell k Lu)))
    (hcl : ∀ l, l < k → ∀ z ∈ W l, z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l) → ∀ μ : Fin 3,
      frobNorm (((bg l (z, μ) : SU2) : M2) - 1) ≤ ε l)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (hr : ∀ j, j < k → Real.pi / 2 * ((loopFactorBound ell : ℝ) * ε j) < r0)
    (j : ℕ) (hj : j ≤ k) (X : Finset (PeriodicLatticeEdge (scaleUp ell k Lu)))
    (hX : ∀ b ∈ X, b.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ j))
    (hW : ∀ b ∈ X, ∀ l, l < j → Ball b.1 (rhoT ell j - rhoT ell l) ⊆ W l)
    (a : XS (scaleUp ell k Lu)) :
    (∑ b ∈ X, ‖suOf (QlinCompL ell bg j a b)‖ ^ 2
        ≤ ((rr ell) ^ j * Real.exp ((∑ i ∈ Finset.range j, thetaOf ell (ε i)) / rr ell) * nrm 1 a) ^ 2)
    ∧ (∑ b ∈ X, ‖suOf ((QlinCompL ell bg j a - QlinCompL ell (flatBg ell k Lu) j a) b)‖ ^ 2
        ≤ ((rr ell) ^ j * ((∑ i ∈ Finset.range j, thetaOf ell (ε i)) / rr ell)
            * Real.exp ((∑ i ∈ Finset.range j, thetaOf ell (ε i)) / rr ell) * nrm 1 a) ^ 2) := by
  classical
  set bg' := bgCut ell bg W with hbg'
  let ε' : ℕ → ℝ := fun i => if i < k then ε i else 0
  have hε'1 : ∀ i, 0 ≤ ε' i := fun i => by
    by_cases h : i < k
    · simp only [ε', if_pos h]; exact hε0 i h
    · simp only [ε', if_neg h]; exact le_rfl
  have hε'2 : ∀ i, i < k → ε' i = ε i := fun i h => by simp only [ε', if_pos h]
  have hV : ∀ i, i < k → ∀ e, frobNorm (((bg' i e : SU2) : M2) - 1) ≤ ε' i := by
    intro i hi e
    rw [hε'2 i hi]
    exact bgCut_frob ell bg W ε i (hε0 i hi) (hcl i hi) e
  have hreg : RegTower ell bg' k :=
    regTower_of_small_bc hell bg' k ε' hε'1 hV (fun i hi => by rw [hε'2 i hi]; exact hr i hi)
  have hFG := tower_FG_gen ell k Lu hell bg' ε hreg
    (fun i hi y _ μ => by simpa [hε'2 i hi] using hV i hi (y, μ)) hε0 hsm a j hj
  have hd : ∀ l, l < j → ∀ ρ : Fin 3, ell ^ l ∣ scaleUp ell k Lu ρ + 1 :=
    fun l hl ρ => hdvd_scaleUp ell k Lu hell l (by omega) ρ
  have hrow : ∀ b ∈ X, QlinCompL ell bg j a b = QlinCompX ell bg' j a b := by
    intro b hb
    rw [compL_cut ell hell bg W j hd b (hX b hb) (hW b hb) a,
      QlinCompL_eq_QlinCompX ell bg' k hreg j hj]
  have hflat : QlinCompL ell (flatBg ell k Lu) j = QlinCompX ell (flatBg ell k Lu) j :=
    QlinCompL_eq_QlinCompX ell (flatBg ell k Lu) k (regTower_flat ell k Lu hell k) j hj
  have hS : 0 ≤ nrm 1 a := nrm_nonneg _ _
  constructor
  · calc ∑ b ∈ X, ‖suOf (QlinCompL ell bg j a b)‖ ^ 2
        = ∑ b ∈ X, ‖suOf (QlinCompX ell bg' j a b)‖ ^ 2 :=
          Finset.sum_congr rfl (fun b hb => by rw [hrow b hb])
      _ ≤ nrm (ell ^ j) (QlinCompX ell bg' j a) ^ 2 := rows_sum_le _ X hX _
      _ ≤ _ := pow_le_pow_left₀ (nrm_nonneg _ _) hFG.1 2
  · calc ∑ b ∈ X, ‖suOf ((QlinCompL ell bg j a - QlinCompL ell (flatBg ell k Lu) j a) b)‖ ^ 2
        = ∑ b ∈ X, ‖suOf ((QlinCompX ell bg' j a - QlinCompX ell (flatBg ell k Lu) j a) b)‖ ^ 2 :=
          Finset.sum_congr rfl (fun b hb => by
            rw [hflat]
            show ‖suOf (QlinCompL ell bg j a b - QlinCompX ell (flatBg ell k Lu) j a b)‖ ^ 2 = _
            rw [hrow b hb]; rfl)
      _ ≤ nrm (ell ^ j) (QlinCompX ell bg' j a - QlinCompX ell (flatBg ell k Lu) j a) ^ 2 :=
          rows_sum_le _ X hX _
      _ ≤ _ := pow_le_pow_left₀ (nrm_nonneg _ _) hFG.2 2

end AdalyFormal.TowerLoc

#print axioms AdalyFormal.TowerLoc.tower_FG_gen
#print axioms AdalyFormal.TowerLoc.rows_sum_le
#print axioms AdalyFormal.TowerLoc.rows_FG_loc
