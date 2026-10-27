import DW1
import DC3

/-!
# DW2 -- the D2 Combes–Thomas weight `phiC` satisfies lane E's weight conditions `WtOK`, and the stratum of a row base
(M1 D-layer lane, 2026-10-14)

* `pdist_block` : `x ∈ blockOf y n ⇒ pdist y x ≤ 3n`;
* `strat_block` : a site of a level-`j` constraint block (`y ∈ Λ_j`) has stratum `j` and lies in `Ω₀`;
* **`phiC_WtOK`** : `WtOK (geomOf ℓ k S) ℓ (phiC θ c) (3θℓ²) (6θ)` (`R, M ≥ 1`, `ℓ ≥ 2`, `θ ≥ 0`);
* `phiC_lip` : the stratified Lipschitz bound `|φ(x+e_μ) − φ(x)| ≤ 3θℓ/ℓ^{strat x}` and its negative;
* **`rowBase_strat`** : for a constraint row `p` of level `j`, `j ≤ strat(rowBase p) + 1` (`ℓ ≤ R M`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M1DStrat

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.M1Site
open AdalyFormal.M1IMS
open AdalyFormal.StatementLane (Tower Admissible bigSide pdist pcd)
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_shift_le pdist_triangle pdist_coarseShift_le)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.M1

variable {L : PeriodicLatticeExtent}

theorem pdist_block {y x : PeriodicLatticeSite L} {n : ℕ} (hx : x ∈ blockOf y n) : pdist y x ≤ 3 * n := by
  rw [mem_blockOf] at hx
  unfold pdist
  have hb : ∀ μ : Fin 3, pcd (L μ + 1) (y μ).val (x μ).val ≤ n := by
    intro μ
    unfold pcd
    have h1 := (hx μ).1
    have h2 := (hx μ).2
    rw [if_pos h1]
    exact (min_le_left _ _).trans (by omega)
  calc ∑ μ : Fin 3, pcd (L μ + 1) (y μ).val (x μ).val ≤ ∑ _μ : Fin 3, n := Finset.sum_le_sum (fun μ _ => hb μ)
    _ = 3 * n := by simp

section geo
variable {ell M R k : ℕ} {S : Tower L} (hA : Admissible ell M R k S) (hR : 1 ≤ R) (hM : 1 ≤ M) (hell : 2 ≤ ell)
include hA hell

/-- a site of a level-`j` constraint block -/
theorem strat_block {j : ℕ} (hj : j ≤ k) {y x : PeriodicLatticeSite L} (hy : y ∈ (geomOf ell k S).Lam j)
    (hx : x ∈ blockOf y (ell ^ j)) : strat S k x = j ∧ x ∈ S.Om 0 := by
  have hell0 : 0 < ell := by omega
  have hP := properTower_geomOf hell0 hA
  have hs := stratG_eq hP hj hy hx
  rw [← strat_eq_stratG hell0 hA] at hs
  refine ⟨hs, ?_⟩
  have hO : OmGe (geomOf ell k S) j x := ⟨j, le_rfl, hj, y, hy, mem_blockOf.mp hx⟩
  have hx' := (omGe_iff_om ell M R k hell0 S hA j x).mp hO
  exact om_anti hA (Nat.zero_le j) hx'

include hR hM in
/-- **the D2 weight is a `WtOK` weight** -/
theorem phiC_WtOK {θ : ℝ} (hθ : 0 ≤ θ) (c : PeriodicLatticeSite L) :
    WtOK (geomOf ell k S) ell (phiC S ell M R k θ c) (3 * θ * (ell : ℝ) ^ 2) (6 * θ) := by
  have hell0 : 0 < ell := by omega
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  refine ⟨fun b _ => ?_, fun q x hx => ?_⟩
  · -- bond clause
    have h := phiC_step hA hR hM hell hθ c b.1 b.2
    rw [abs_sub_comm] at h
    have hadj := (strat_adj hA hR hM (show 1 ≤ ell by omega) b.1 b.2).1
    rw [← strat_eq_stratG hell0 hA]
    refine h.trans ?_
    have hp1 : (0 : ℝ) < (ell : ℝ) ^ strat S k b.1 := by have := one_le_pow₀ (n := strat S k b.1) hellr; positivity
    have hp2 : (0 : ℝ) < (ell : ℝ) ^ strat S k (periodicLatticeShift b.1 b.2) := by
      have := one_le_pow₀ (n := strat S k (periodicLatticeShift b.1 b.2)) hellr; positivity
    rw [div_le_div_iff₀ hp1 hp2]
    have hpow : (ell : ℝ) ^ strat S k (periodicLatticeShift b.1 b.2) ≤ (ell : ℝ) ^ strat S k b.1 * ell := by
      rw [← pow_succ]; exact pow_le_pow_right₀ hellr hadj
    have h0 : (0 : ℝ) ≤ 3 * θ * ell := by positivity
    calc 3 * θ * ell * (ell : ℝ) ^ strat S k (periodicLatticeShift b.1 b.2)
        ≤ 3 * θ * ell * ((ell : ℝ) ^ strat S k b.1 * ell) := mul_le_mul_of_nonneg_left hpow h0
      _ = 3 * θ * (ell : ℝ) ^ 2 * (ell : ℝ) ^ strat S k b.1 := by ring
  · -- block clause
    have hjk : jq q ≤ k := Nat.lt_succ_iff.mp q.1.1.isLt
    have hy : yq q ∈ (geomOf ell k S).Lam (jq q) := q.2
    have hyy : yq q ∈ blockOf (yq q) (ell ^ jq q) := by
      rw [mem_blockOf]; intro μ; exact ⟨le_rfl, by have := Nat.one_le_pow (jq q) ell hell0; omega⟩
    obtain ⟨hsx, hx0⟩ := strat_block hA hell hjk hy hx
    obtain ⟨hsy, hy0⟩ := strat_block hA hell hjk hy hyy
    have hd : (pdist (yq q) x : ℝ) ≤ 3 * (ell : ℝ) ^ jq q := by exact_mod_cast pdist_block hx
    exact phiC_block hA hR hM hell hθ c hy0 hx0 hsy hsx hd

include hR hM in
theorem phiC_lip {θ : ℝ} (hθ : 0 ≤ θ) (c : PeriodicLatticeSite L) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    |phiC S ell M R k θ c (periodicLatticeShift x μ) - phiC S ell M R k θ c x|
      ≤ 3 * θ * ell / (ell : ℝ) ^ strat S k x :=
  phiC_step hA hR hM hell hθ c x μ

include hR hM in
/-- **the stratum of a row base** -/
theorem rowBase_strat (hRM : ell ≤ R * M) (p : BIdx (geomOf ell k S)) :
    (p.1 : ℕ) ≤ strat S k (rowBase (geomOf ell k S) p) + 1 := by
  classical
  have hell0 : 0 < ell := by omega
  set j : ℕ := (p.1 : ℕ) with hjdef
  have hjk : j ≤ k := Nat.lt_succ_iff.mp p.1.isLt
  have hLs : ∀ z, z ∈ (geomOf ell k S).Lam j → strat S k z = j := by
    intro z hz
    have hzz : z ∈ blockOf z (ell ^ j) := by
      rw [mem_blockOf]; intro μ; exact ⟨le_rfl, by have := Nat.one_le_pow j ell hell0; omega⟩
    exact (strat_block hA hell hjk hz hzz).1
  have hb : p.2.1.1 ∈ (geomOf ell k S).Lam j ∨
      coarseShift p.2.1.1 ((geomOf ell k S).ell ^ j) p.2.1.2 ∈ (geomOf ell k S).Lam j := p.2.2.1
  unfold rowBase
  split_ifs with h0
  · rcases hb with h | h
    · rw [hLs _ h]; omega
    · -- the tail is within `ℓ^j` of a stratum-`j` site
      by_cases hj0 : j = 0
      · omega
      have hz := h.2.1
      have hd : pdist p.2.1.1 (coarseShift p.2.1.1 (ell ^ j) p.2.1.2) ≤ ell ^ j :=
        pdist_coarseShift_le p.2.1.1 (ell ^ j) p.2.1.2
      by_contra hlt
      push Not at hlt
      have hnot : p.2.1.1 ∉ S.Om (j - 1) := by
        intro hm
        have := le_strat_of_mem (k := k) (by omega) hm
        omega
      have hz' : coarseShift p.2.1.1 (ell ^ j) p.2.1.2 ∈ S.Om (j - 1 + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ j)]; exact hz
      have hcol := collar hA (j := j - 1) (by omega) hnot hz'
      unfold bigSide at hcol
      have hpow : ell ^ j = ell * ell ^ (j - 1) := by rw [← pow_succ']; congr 1; omega
      have : ell ^ j ≤ R * (M * ell ^ (j - 1)) := by
        rw [hpow]
        calc ell * ell ^ (j - 1) ≤ (R * M) * ell ^ (j - 1) := Nat.mul_le_mul_right _ hRM
          _ = R * (M * ell ^ (j - 1)) := by ring
      omega
  · rcases hb with h | h
    · exact absurd (om_anti hA (Nat.zero_le j) h.2.1) h0
    · rw [show (geomOf ell k S).ell = ell from rfl] at h
      rw [show (geomOf ell k S).ell = ell from rfl, hLs _ h]; omega

end geo

#print axioms pdist_block
#print axioms strat_block
#print axioms phiC_WtOK
#print axioms phiC_lip
#print axioms rowBase_strat

end AdalyFormal.M1DStrat
