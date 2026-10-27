import UB2
import TL3
import MA6

/-!
# UB3 -- the chart bond defect `D_q` from the row drift of FOUR rows (lane m2_unit_20261014)

* `rows_drift_sub` : TL3 `level_drift_loc` for an arbitrary finite family `R` of level-`j` rows: the regional class is needed only
  on the cones of the rows in `R`, and the input only on their footprints.
* `row_identity` : MA6's per-row identity `n³‖q₁ⁿ y(b) − B b‖² = n³‖Q_V y(row b) − Q_1 y(row b)‖²` for a unit bond `b` whose
  embedding is a top row, at any configuration `V` with `Q_V y = τ* B`.
* `Qgauge` : `Q_U y = τ* B` transports to the chart: `Q_{U^γ}(γ·y) = τ*(u·B)`, `u = γ ∘ embY`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.M2Unit

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
open AdalyFormal.TowerLoc

section drift
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

/-- **row-family drift**: `level_drift_loc` for a finite family `Rw` of level-`j` rows. -/
theorem rows_drift_sub (hell : 0 < ell) (V : Cfg (scaleUp ell k Lu)) (ε : ℕ → ℝ)
    (W : ℕ → Set (PeriodicLatticeSite (scaleUp ell k Lu)))
    (hcl : ∀ l, l < k → ∀ z ∈ W l, z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l) → ∀ μ : Fin 3,
      frobNorm (((bgTower (GF ell k Lu) V l (z, μ) : SU2) : M2) - 1) ≤ ε l)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (hr : ∀ j, j < k → Real.pi / 2 * ((loopFactorBound ell : ℝ) * ε j) < r0)
    (j : Fin (k + 1)) (Rw : Finset {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j})
    (hW : ∀ r ∈ Rw, ∀ l, l < (j : ℕ) → Ball r.1.1 (rhoT ell j - rhoT ell l) ⊆ W l)
    (x : BondFnL2 (scaleUp ell k Lu)) :
    ∑ r ∈ Rw, ((ell : ℝ) ^ (j : ℕ)) ^ 3 * ‖(bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩
        - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩‖ ^ 2
      ≤ delLoc ell ε j ^ 2 * ‖bondRestr (fun e => ∃ r ∈ Rw, Foot ell (j : ℕ) r.1 e) x‖ ^ 2 := by
  classical
  have hjk : (j : ℕ) ≤ k := Nat.lt_succ_iff.mp j.isLt
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  set bg := bgTower (GF ell k Lu) V with hbg
  set xr := bondRestr (fun e => ∃ r ∈ Rw, Foot ell (j : ℕ) r.1 e) x with hxr
  have hal : ∀ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
      r.1.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ (j : ℕ)) :=
    fun r => AdalyFormal.M1IMS.row_aligned (S := S) hell ⟨j, r⟩
  have hzero : ∀ r ∈ Rw, ∀ e, Foot ell (j : ℕ) r.1 e → (suCoord x - suCoord xr) e = 0 := by
    intro r hr' e he
    have hxe : xr e = x e := by
      simp only [hxr, bondRestr, PiLp.toLp_apply]
      split_ifs with h
      · rfl
      · exact absurd ⟨r, hr', he⟩ h
    have h1 : (x - xr) e = 0 := by rw [PiLp.sub_apply, hxe, sub_self]
    have := suCoord_zero_of (x - xr) e h1
    rwa [map_sub] at this
  have hloc : ∀ r ∈ Rw,
      QlinCompL ell bg j (suCoord x) r.1 - QlinCompL ell (flatBg ell k Lu) j (suCoord x) r.1
        = QlinCompL ell bg j (suCoord xr) r.1 - QlinCompL ell (flatBg ell k Lu) j (suCoord xr) r.1 := by
    intro r hr'
    have h1 := compL_row_local_loc ell k Lu hell bg ε W hcl hε0 hr j hjk r.1 (hal r) (hW r hr') _ (hzero r hr')
    have h2 := compL_row_local_flat ell k Lu hell j hjk r.1 _ (hzero r hr')
    rw [map_sub] at h1 h2
    simp only [Pi.sub_apply] at h1 h2
    linear_combination h1 - h2
  have hrow : ∀ r ∈ Rw,
      (bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩ - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩
        = ((ell : ℝ) ^ (j : ℕ))⁻¹ • suOf ((QlinCompL ell bg j (suCoord xr)
            - QlinCompL ell (flatBg ell k Lu) j (suCoord xr)) r.1) := by
    intro r hr'
    have e1 : (bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩
        = ((ell : ℝ) ^ (j : ℕ))⁻¹ • suOf (QlinCompL ell bg j (suCoord x) r.1) := rfl
    have e2 : (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩
        = ((ell : ℝ) ^ (j : ℕ))⁻¹ • suOf (QlinCompL ell (flatBg ell k Lu) j (suCoord x) r.1) := by
      show ((ell : ℝ) ^ (j : ℕ))⁻¹ • suOf (QlinCompL ell (bgTower (geomOf ell k S) (trivialU _)) j (suCoord x) r.1) = _
      rw [bgTower_geom_trivial]
    rw [e1, e2, ← smul_sub, ← suOf_sub]
    congr 2
    exact hloc r hr'
  let X : Finset (PeriodicLatticeEdge (scaleUp ell k Lu)) := Rw.map (Function.Embedding.subtype _)
  have hXal : ∀ b ∈ X, b.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ (j : ℕ)) := by
    intro b hb
    obtain ⟨r, _, rfl⟩ := Finset.mem_map.mp hb
    exact hal r
  have hXW : ∀ b ∈ X, ∀ l, l < (j : ℕ) → Ball b.1 (rhoT ell j - rhoT ell l) ⊆ W l := by
    intro b hb l hl
    obtain ⟨r, hr', rfl⟩ := Finset.mem_map.mp hb
    exact hW r hr' l hl
  have hFG := (rows_FG_loc ell k Lu hell bg ε W hcl hε0 hsm hr (j : ℕ) hjk X hXal hXW (suCoord xr)).2
  rw [nrm_one_suCoord] at hFG
  have hsumX : ∑ b ∈ X, ‖suOf ((QlinCompL ell bg j (suCoord xr)
        - QlinCompL ell (flatBg ell k Lu) j (suCoord xr)) b)‖ ^ 2
      = ∑ r ∈ Rw,
        ‖suOf ((QlinCompL ell bg j (suCoord xr) - QlinCompL ell (flatBg ell k Lu) j (suCoord xr)) r.1)‖ ^ 2 := by
    simp only [X, Finset.sum_map]
    rfl
  rw [hsumX] at hFG
  calc ∑ r ∈ Rw,
        ((ell : ℝ) ^ (j : ℕ)) ^ 3 * ‖(bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩
          - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩‖ ^ 2
      = ((ell : ℝ) ^ (j : ℕ)) ^ 3 * (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2
          * ∑ r ∈ Rw,
            ‖suOf ((QlinCompL ell bg j (suCoord xr) - QlinCompL ell (flatBg ell k Lu) j (suCoord xr)) r.1)‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun r hr' => ?_)
        rw [hrow r hr', norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (pow_pos hellR _)]
        ring
    _ ≤ ((ell : ℝ) ^ (j : ℕ)) ^ 3 * (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2
          * ((rr ell) ^ (j : ℕ) * ((∑ i ∈ Finset.range (j : ℕ), thetaOf ell (ε i)) / rr ell)
            * Real.exp ((∑ i ∈ Finset.range (j : ℕ), thetaOf ell (ε i)) / rr ell) * ‖xr‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hFG (by positivity)
    _ = (((ell : ℝ) ^ (j : ℕ)) ^ 3 * (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ((rr ell) ^ (j : ℕ)) ^ 2)
          * (delLoc ell ε j ^ 2 * ‖xr‖ ^ 2) := by unfold delLoc; ring
    _ = delLoc ell ε j ^ 2 * ‖xr‖ ^ 2 := by rw [scale_one hell, one_mul]

end drift

end AdalyFormal.M2Unit

#print axioms AdalyFormal.M2Unit.rows_drift_sub
