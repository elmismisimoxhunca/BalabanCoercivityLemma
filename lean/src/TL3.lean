import TL2
import W6E

/-!
# TL3 -- region-restricted level drift and the k-free drift form `hD` (W6I `qs_injective_of_drift`)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.TowerLoc

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp)
open AdalyFormal.StatementLaneR8
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.DLayer (Foot bondRestr QlinCompX_row_local suCoord_zero_of)
open AdalyFormal.BondComposite
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.W6

/-- the regular cut-off tower and its class, from the regional data -/
theorem cut_reg (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (bg : ℕ → PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)) (ε : ℕ → ℝ)
    (W : ℕ → Set (PeriodicLatticeSite (scaleUp ell k Lu)))
    (hcl : ∀ l, l < k → ∀ z ∈ W l, z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l) → ∀ μ : Fin 3,
      frobNorm (((bg l (z, μ) : SU2) : M2) - 1) ≤ ε l)
    (hε0 : ∀ j, j < k → 0 ≤ ε j)
    (hr : ∀ j, j < k → Real.pi / 2 * ((loopFactorBound ell : ℝ) * ε j) < r0) :
    RegTower ell (bgCut ell bg W) k := by
  classical
  let ε' : ℕ → ℝ := fun i => if i < k then ε i else 0
  have hε'1 : ∀ i, 0 ≤ ε' i := fun i => by
    by_cases h : i < k
    · simp only [ε', if_pos h]; exact hε0 i h
    · simp only [ε', if_neg h]; exact le_rfl
  have hε'2 : ∀ i, i < k → ε' i = ε i := fun i h => by simp only [ε', if_pos h]
  exact regTower_of_small_bc hell (bgCut ell bg W) k ε' hε'1
    (fun i hi e => by rw [hε'2 i hi]; exact bgCut_frob ell bg W ε i (hε0 i hi) (hcl i hi) e)
    (fun i hi => by rw [hε'2 i hi]; exact hr i hi)

/-- **input locality of a row of the LOCAL composite on a regional tower**: the row `b` reads its input only on
`Foot ell j b` (no global regularity of `bg`). -/
theorem compL_row_local_loc (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (bg : ℕ → PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)) (ε : ℕ → ℝ)
    (W : ℕ → Set (PeriodicLatticeSite (scaleUp ell k Lu)))
    (hcl : ∀ l, l < k → ∀ z ∈ W l, z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l) → ∀ μ : Fin 3,
      frobNorm (((bg l (z, μ) : SU2) : M2) - 1) ≤ ε l)
    (hε0 : ∀ j, j < k → 0 ≤ ε j)
    (hr : ∀ j, j < k → Real.pi / 2 * ((loopFactorBound ell : ℝ) * ε j) < r0)
    (j : ℕ) (hj : j ≤ k) (b : PeriodicLatticeEdge (scaleUp ell k Lu))
    (hb : b.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ j))
    (hW : ∀ l, l < j → Ball b.1 (rhoT ell j - rhoT ell l) ⊆ W l)
    (v : XS (scaleUp ell k Lu)) (hv : ∀ e, Foot ell j b e → v e = 0) :
    QlinCompL ell bg j v b = 0 := by
  have hreg := cut_reg ell k Lu hell bg ε W hcl hε0 hr
  have hd : ∀ l, l < j → ∀ ρ : Fin 3, ell ^ l ∣ scaleUp ell k Lu ρ + 1 :=
    fun l hl ρ => hdvd_scaleUp ell k Lu hell l (by omega) ρ
  rw [compL_cut ell hell bg W j hd b hb hW v, QlinCompL_eq_QlinCompX ell (bgCut ell bg W) k hreg j hj]
  exact QlinCompX_row_local ell (bgCut ell bg W) k hreg j hj b v hv

/-- the flat tower: row locality -/
theorem compL_row_local_flat (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (j : ℕ) (hj : j ≤ k) (b : PeriodicLatticeEdge (scaleUp ell k Lu))
    (v : XS (scaleUp ell k Lu)) (hv : ∀ e, Foot ell j b e → v e = 0) :
    QlinCompL ell (flatBg ell k Lu) j v b = 0 := by
  rw [QlinCompL_eq_QlinCompX ell (flatBg ell k Lu) k (regTower_flat ell k Lu hell k) j hj]
  exact QlinCompX_row_local ell (flatBg ell k Lu) k (regTower_flat ell k Lu hell k) j hj b v hv

/-- the regional per-level constant `δ_j = (S_j/r) e^{S_j/r}`, `S_j = Σ_{i<j} θ(ε_i)` -/
def delLoc (ell : ℕ) (ε : ℕ → ℝ) (j : ℕ) : ℝ :=
  ((∑ i ∈ range j, thetaOf ell (ε i)) / rr ell) * Real.exp ((∑ i ∈ range j, thetaOf ell (ε i)) / rr ell)

section drift
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

/-- **region-restricted level-`j` drift**: the hypothesis on the background is only the regional class on `W l`,
`W l ⊇ Ball r₋ (rhoT j - rhoT l)` for the rows `r` of level `j`. -/
theorem level_drift_loc (hell : 0 < ell) (V : Cfg (scaleUp ell k Lu)) (ε : ℕ → ℝ)
    (W : ℕ → Set (PeriodicLatticeSite (scaleUp ell k Lu)))
    (hcl : ∀ l, l < k → ∀ z ∈ W l, z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l) → ∀ μ : Fin 3,
      frobNorm (((bgTower (GF ell k Lu) V l (z, μ) : SU2) : M2) - 1) ≤ ε l)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (hr : ∀ j, j < k → Real.pi / 2 * ((loopFactorBound ell : ℝ) * ε j) < r0)
    (j : Fin (k + 1))
    (hW : ∀ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j}, ∀ l, l < (j : ℕ) →
      Ball r.1.1 (rhoT ell j - rhoT ell l) ⊆ W l)
    (x : BondFnL2 (scaleUp ell k Lu)) :
    ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
      ((ell : ℝ) ^ (j : ℕ)) ^ 3 * ‖(bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩
        - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩‖ ^ 2
      ≤ delLoc ell ε j ^ 2 * ‖bondRestr (FootL (S := S) j) x‖ ^ 2 := by
  classical
  have hjk : (j : ℕ) ≤ k := Nat.lt_succ_iff.mp j.isLt
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  set bg := bgTower (GF ell k Lu) V with hbg
  set xr := bondRestr (FootL (S := S) j) x with hxr
  have hal : ∀ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
      r.1.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ (j : ℕ)) :=
    fun r => AdalyFormal.M1IMS.row_aligned (S := S) hell ⟨j, r⟩
  -- input locality of both rows
  have hzero : ∀ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
      ∀ e, Foot ell (j : ℕ) r.1 e → (suCoord x - suCoord xr) e = 0 := by
    intro r e he
    have h1 : (x - xr) e = 0 := by
      show x e - (if FootL (S := S) j e then x e else 0) = 0
      rw [if_pos ⟨r, he⟩, sub_self]
    have := suCoord_zero_of (x - xr) e h1
    rwa [map_sub] at this
  have hloc : ∀ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
      QlinCompL ell bg j (suCoord x) r.1 - QlinCompL ell (flatBg ell k Lu) j (suCoord x) r.1
        = QlinCompL ell bg j (suCoord xr) r.1 - QlinCompL ell (flatBg ell k Lu) j (suCoord xr) r.1 := by
    intro r
    have h1 := compL_row_local_loc ell k Lu hell bg ε W hcl hε0 hr j hjk r.1 (hal r) (hW r) _ (hzero r)
    have h2 := compL_row_local_flat ell k Lu hell j hjk r.1 _ (hzero r)
    rw [map_sub] at h1 h2
    simp only [Pi.sub_apply] at h1 h2
    linear_combination h1 - h2
  have hrow : ∀ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
      (bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩ - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩
        = ((ell : ℝ) ^ (j : ℕ))⁻¹ • suOf ((QlinCompL ell bg j (suCoord xr)
            - QlinCompL ell (flatBg ell k Lu) j (suCoord xr)) r.1) := by
    intro r
    have e1 : (bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩
        = ((ell : ℝ) ^ (j : ℕ))⁻¹ • suOf (QlinCompL ell bg j (suCoord x) r.1) := rfl
    have e2 : (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩
        = ((ell : ℝ) ^ (j : ℕ))⁻¹ • suOf (QlinCompL ell (flatBg ell k Lu) j (suCoord x) r.1) := by
      show ((ell : ℝ) ^ (j : ℕ))⁻¹ • suOf (QlinCompL ell (bgTower (geomOf ell k S) (trivialU _)) j (suCoord x) r.1) = _
      rw [bgTower_geom_trivial]
    rw [e1, e2, ← smul_sub, ← suOf_sub]
    congr 2
    have := hloc r
    exact this
  -- the cone bound
  let X : Finset (PeriodicLatticeEdge (scaleUp ell k Lu)) :=
    (Finset.univ : Finset {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j}).map
      (Function.Embedding.subtype _)
  have hXal : ∀ b ∈ X, b.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ (j : ℕ)) := by
    intro b hb
    obtain ⟨r, _, rfl⟩ := Finset.mem_map.mp hb
    exact hal r
  have hXW : ∀ b ∈ X, ∀ l, l < (j : ℕ) → Ball b.1 (rhoT ell j - rhoT ell l) ⊆ W l := by
    intro b hb l hl
    obtain ⟨r, _, rfl⟩ := Finset.mem_map.mp hb
    exact hW r l hl
  have hFG := (rows_FG_loc ell k Lu hell bg ε W hcl hε0 hsm hr (j : ℕ) hjk X hXal hXW (suCoord xr)).2
  rw [nrm_one_suCoord] at hFG
  have hsumX : ∑ b ∈ X, ‖suOf ((QlinCompL ell bg j (suCoord xr)
        - QlinCompL ell (flatBg ell k Lu) j (suCoord xr)) b)‖ ^ 2
      = ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
        ‖suOf ((QlinCompL ell bg j (suCoord xr) - QlinCompL ell (flatBg ell k Lu) j (suCoord xr)) r.1)‖ ^ 2 := by
    simp only [X, Finset.sum_map]
    rfl
  rw [hsumX] at hFG
  have hr0 := rr_pos hell
  calc ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
        ((ell : ℝ) ^ (j : ℕ)) ^ 3 * ‖(bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩
          - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩‖ ^ 2
      = ((ell : ℝ) ^ (j : ℕ)) ^ 3 * (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2
          * ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
            ‖suOf ((QlinCompL ell bg j (suCoord xr) - QlinCompL ell (flatBg ell k Lu) j (suCoord xr)) r.1)‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [hrow r, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (pow_pos hellR _)]
        ring
    _ ≤ ((ell : ℝ) ^ (j : ℕ)) ^ 3 * (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2
          * ((rr ell) ^ (j : ℕ) * ((∑ i ∈ Finset.range (j : ℕ), thetaOf ell (ε i)) / rr ell)
            * Real.exp ((∑ i ∈ Finset.range (j : ℕ), thetaOf ell (ε i)) / rr ell) * ‖xr‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hFG (by positivity)
    _ = (((ell : ℝ) ^ (j : ℕ)) ^ 3 * (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ((rr ell) ^ (j : ℕ)) ^ 2)
          * (delLoc ell ε j ^ 2 * ‖xr‖ ^ 2) := by unfold delLoc; ring
    _ = delLoc ell ε j ^ 2 * ‖xr‖ ^ 2 := by rw [scale_one hell, one_mul]

end drift

end AdalyFormal.TowerLoc

#print axioms AdalyFormal.TowerLoc.cut_reg
#print axioms AdalyFormal.TowerLoc.compL_row_local_loc
#print axioms AdalyFormal.TowerLoc.compL_row_local_flat
#print axioms AdalyFormal.TowerLoc.level_drift_loc
