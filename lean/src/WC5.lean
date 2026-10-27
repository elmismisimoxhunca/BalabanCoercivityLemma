import TL4
import WC3
import WC4d
import WC6b

/-!
# WC5 -- per-source bounds (M2 W6 lane)

For the flat kernel `ψ_p w` of ONE row `p` and a configuration `V` whose background tower is near the identity only on a REGION
around the base of `p` (regional class, `rows_FG_loc`), the interacting rows `p'` (`Inter p' p`) satisfy
* `F`: `Σ_{p'} wF p' ‖(Q_V ψ_p w)(p')‖² ≤ 3 E*² ‖ψ_p w‖²`;
* `G`: `Σ_{p'} wF p' ‖((Q_V - Q₁) ψ_p w)(p')‖² ≤ 3 δ*² ‖ψ_p w‖²`,
and every other row vanishes (`Qfull_zero_of_not_inter`, unconditional far-locality `compL_far_zero`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace AdalyFormal.M2W6

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice blockOf mem_blockOf)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist)
open AdalyFormal.StatementLaneR8
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.DLayer (suCoord_zero_of)
open AdalyFormal.BondComposite
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.W6
open AdalyFormal.TowerLoc

section src
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

/-- **vanishing outside the interaction set**: for ANY configuration `V`, a row `p'` that does not interact with `p` does not see
the kernel of `p`. -/
theorem Qfull_zero_of_not_inter (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M) (hroom : 17 * ell ≤ R * M)
    (V : Cfg (scaleUp ell k Lu)) (p p' : BIdx (geomOf ell k S)) (hni : ¬ Inter p' p) (w : SuTwo) :
    (bondSectorOf (geomOf ell k S) V).Qfull (psiL (by omega : 0 < ell) p w) p' = 0 := by
  classical
  have hell : 0 < ell := by omega
  have hj' : (p'.1 : ℕ) ≤ k := Nat.lt_succ_iff.mp p'.1.isLt
  have hdv : ∀ l, l < (p'.1 : ℕ) → ∀ ρ : Fin 3, ell ^ l ∣ scaleUp ell k Lu ρ + 1 :=
    fun l hl ρ => AdalyFormal.BondComposite.hdvd_scaleUp ell k Lu hell l (by omega) ρ
  have hrow : (bondSectorOf (geomOf ell k S) V).Qfull (psiL hell p w) p'
      = (((ell : ℝ) ^ (p'.1 : ℕ))⁻¹) • suOf (QlinCompL ell (bgTower (GF ell k Lu) V) (p'.1 : ℕ)
          (suCoord (psiL hell p w)) p'.2.1) := rfl
  have hz : QlinCompL ell (bgTower (GF ell k Lu) V) (p'.1 : ℕ) (suCoord (psiL hell p w)) p'.2.1 = 0 := by
    have := compL_far_zero ell hell (bgTower (GF ell k Lu) V) (p'.1 : ℕ) hdv (p'.1 : ℕ) le_rfl p'.2.1
      (AdalyFormal.M1IMS.row_aligned (S := S) hell p') (suCoord (psiL hell p w)) (fun e he => by
        by_cases h0 : psiL hell p w e = 0
        · exact suCoord_zero_of _ e h0
        · exfalso
          have hph : phiK hell p e ≠ 0 := by
            intro hh; apply h0; rw [psiL_apply, hh, zero_smul]
          apply hni
          have hst := phi_strat hell hS p e hph
          have hrho : rhoT ell (p'.1 : ℕ) + 8 ≤ 8 * ell ^ (p'.1 : ℕ) := rhoT_le ell hell2 _
          have hw := ball_window hS hM hell2 hroom p' e.1 (by omega)
          -- the support radius of the kernel
          have hsup : pdist p.2.1.1 e.1 ≤ 4 * ell ^ (p.1 : ℕ) := by
            obtain ⟨-, hs⟩ := phi_support hell p e hph
            have hn : 0 < ell ^ (p.1 : ℕ) := pow_pos hell _
            rcases hs with ⟨-, hb⟩ | ⟨-, hb⟩
            · have : pdist p.2.1.1 e.1 ≤ 3 * ell ^ (p.1 : ℕ) := pdist_block_le hb
              omega
            · have h1 : pdist (coarseShift p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2) e.1 ≤ 3 * ell ^ (p.1 : ℕ) :=
                pdist_block_le hb
              have h2 := pdist_coarseShift_le p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2
              have h3 := pdist_triangle p.2.1.1 (coarseShift p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2) e.1
              omega
          have ht := pdist_triangle p'.2.1.1 e.1 p.2.1.1
          rw [pdist_comm e.1 p.2.1.1] at ht
          refine ⟨by omega, by omega, by omega⟩)
    exact this
  have h0 : suOf (0 : Fin 3 → ℝ) = 0 := by
    have := suOf_sub (0 : Fin 3 → ℝ) 0
    simpa using this
  rw [hrow, hz, h0, smul_zero]


open Classical in
/-- **one level, rows in a predicate `Pp`, regional class**: both the size (`F`) and the drift (`G`) bounds of `rows_FG_loc`
in the row-normalised form. -/
theorem level_FG_src (hell : 0 < ell) (V : Cfg (scaleUp ell k Lu)) (Pp : BIdx (geomOf ell k S) → Prop) (ε : ℕ → ℝ)
    (W : ℕ → Set (PeriodicLatticeSite (scaleUp ell k Lu)))
    (hcl : ∀ l, l < k → ∀ z ∈ W l, z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l) → ∀ μ : Fin 3,
      frobNorm (((bgTower (GF ell k Lu) V l (z, μ) : SU2) : M2) - 1) ≤ ε l)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (hr : ∀ j, j < k → Real.pi / 2 * ((loopFactorBound ell : ℝ) * ε j) < r0)
    (j : Fin (k + 1))
    (hW : ∀ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j}, Pp ⟨j, r⟩ → ∀ l, l < (j : ℕ) →
      Ball r.1.1 (rhoT ell j - rhoT ell l) ⊆ W l)
    (x : BondFnL2 (scaleUp ell k Lu)) :
    (∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
        (if Pp ⟨j, r⟩ then wF (⟨j, r⟩ : BIdx (geomOf ell k S))
          * ‖(bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩‖ ^ 2 else 0)
      ≤ (Real.exp ((∑ i ∈ Finset.range (j : ℕ), thetaOf ell (ε i)) / rr ell)) ^ 2 * ‖x‖ ^ 2) ∧
    (∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
        (if Pp ⟨j, r⟩ then wF (⟨j, r⟩ : BIdx (geomOf ell k S))
          * ‖(bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩
              - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩‖ ^ 2 else 0)
      ≤ delLoc ell ε j ^ 2 * ‖x‖ ^ 2) := by
  have hjk : (j : ℕ) ≤ k := Nat.lt_succ_iff.mp j.isLt
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  set bg := bgTower (GF ell k Lu) V with hbg
  have hal : ∀ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
      r.1.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ (j : ℕ)) :=
    fun r => AdalyFormal.M1IMS.row_aligned (S := S) hell ⟨j, r⟩
  let X : Finset (PeriodicLatticeEdge (scaleUp ell k Lu)) :=
    ((Finset.univ : Finset {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j}).filter
      (fun r => Pp ⟨j, r⟩)).map (Function.Embedding.subtype _)
  have hXal : ∀ b ∈ X, b.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ (j : ℕ)) := by
    intro b hb
    obtain ⟨r, _, rfl⟩ := Finset.mem_map.mp hb
    exact hal r
  have hXW : ∀ b ∈ X, ∀ l, l < (j : ℕ) → Ball b.1 (rhoT ell j - rhoT ell l) ⊆ W l := by
    intro b hb l hl
    obtain ⟨r, hr', rfl⟩ := Finset.mem_map.mp hb
    exact hW r (Finset.mem_filter.mp hr').2 l hl
  have hFG := rows_FG_loc ell k Lu hell bg ε W hcl hε0 hsm hr (j : ℕ) hjk X hXal hXW (suCoord x)
  rw [nrm_one_suCoord] at hFG
  have e1 : ∀ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
      (bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩
        = (((ell : ℝ) ^ (j : ℕ))⁻¹) • suOf (QlinCompL ell bg j (suCoord x) r.1) := fun r => rfl
  have e2 : ∀ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
      (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩
        = (((ell : ℝ) ^ (j : ℕ))⁻¹) • suOf (QlinCompL ell (flatBg ell k Lu) j (suCoord x) r.1) := by
    intro r
    show ((ell : ℝ) ^ (j : ℕ))⁻¹ • suOf (QlinCompL ell (bgTower (geomOf ell k S) (trivialU _)) j (suCoord x) r.1) = _
    rw [bgTower_geom_trivial]
  have hc : ((ell : ℝ) ^ (j : ℕ)) ^ 3 * (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ((rr ell) ^ (j : ℕ)) ^ 2 = 1 :=
    scale_one hell (j : ℕ)
  have hr0 := rr_pos hell
  have hwF : ∀ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
      wF (⟨j, r⟩ : BIdx (geomOf ell k S)) = ((ell : ℝ) ^ (j : ℕ)) ^ 3 := fun r => rfl
  constructor
  · -- F
    have hsumX : ∑ b ∈ X, ‖suOf (QlinCompL ell bg j (suCoord x) b)‖ ^ 2
        = ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
          (if Pp ⟨j, r⟩ then ‖suOf (QlinCompL ell bg j (suCoord x) r.1)‖ ^ 2 else 0) := by
      simp only [X, Finset.sum_map, Finset.sum_filter]
      rfl
    have h1 := hFG.1
    rw [hsumX] at h1
    calc _ = ((ell : ℝ) ^ (j : ℕ)) ^ 3 * (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2
          * ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
            (if Pp ⟨j, r⟩ then ‖suOf (QlinCompL ell bg j (suCoord x) r.1)‖ ^ 2 else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun r _ => ?_)
          split_ifs with hP
          · rw [hwF r, e1 r, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (pow_pos hellR _)]
            ring
          · simp
      _ ≤ ((ell : ℝ) ^ (j : ℕ)) ^ 3 * (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2
          * ((rr ell) ^ (j : ℕ) * Real.exp ((∑ i ∈ Finset.range (j : ℕ), thetaOf ell (ε i)) / rr ell) * ‖x‖) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (((ell : ℝ) ^ (j : ℕ)) ^ 3 * (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ((rr ell) ^ (j : ℕ)) ^ 2)
          * ((Real.exp ((∑ i ∈ Finset.range (j : ℕ), thetaOf ell (ε i)) / rr ell)) ^ 2 * ‖x‖ ^ 2) := by ring
      _ = _ := by rw [hc, one_mul]
  · -- G
    have hsumX : ∑ b ∈ X, ‖suOf ((QlinCompL ell bg j (suCoord x)
          - QlinCompL ell (flatBg ell k Lu) j (suCoord x)) b)‖ ^ 2
        = ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
          (if Pp ⟨j, r⟩ then ‖suOf ((QlinCompL ell bg j (suCoord x)
            - QlinCompL ell (flatBg ell k Lu) j (suCoord x)) r.1)‖ ^ 2 else 0) := by
      simp only [X, Finset.sum_map, Finset.sum_filter]
      rfl
    have h1 := hFG.2
    rw [hsumX] at h1
    calc _ = ((ell : ℝ) ^ (j : ℕ)) ^ 3 * (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2
          * ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
            (if Pp ⟨j, r⟩ then ‖suOf ((QlinCompL ell bg j (suCoord x)
              - QlinCompL ell (flatBg ell k Lu) j (suCoord x)) r.1)‖ ^ 2 else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun r _ => ?_)
          split_ifs with hP
          · rw [hwF r, e1 r, e2 r, ← smul_sub, ← suOf_sub, norm_smul, Real.norm_eq_abs, abs_inv,
              abs_of_pos (pow_pos hellR _)]
            simp only [Pi.sub_apply]
            ring
          · simp
      _ ≤ ((ell : ℝ) ^ (j : ℕ)) ^ 3 * (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2
          * ((rr ell) ^ (j : ℕ) * ((∑ i ∈ Finset.range (j : ℕ), thetaOf ell (ε i)) / rr ell)
            * Real.exp ((∑ i ∈ Finset.range (j : ℕ), thetaOf ell (ε i)) / rr ell) * ‖x‖) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (((ell : ℝ) ^ (j : ℕ)) ^ 3 * (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ((rr ell) ^ (j : ℕ)) ^ 2)
          * (delLoc ell ε j ^ 2 * ‖x‖ ^ 2) := by unfold delLoc; ring
      _ = _ := by rw [hc, one_mul]

end src

end AdalyFormal.M2W6

#print axioms AdalyFormal.M2W6.Qfull_zero_of_not_inter
