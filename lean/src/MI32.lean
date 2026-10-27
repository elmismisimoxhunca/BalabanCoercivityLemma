import MI31

/-!
# MI32 -- footprint multiplicity on a proper tower and **`massComm_proper`** (M1 lane E, 2026-10-13)

* `levels_le_three` : at most three levels `j ≤ k` satisfy `s ≤ j + 1 ∧ j ≤ s + 1`;
* `foot_count` : `Σ_p ℓ^{−2 j_p} [e ∈ Foot(p)] ≤ 1944 ℓ² ℓ^{−2 strat(e)}` (rows inject into (level, bond); at a fixed level the
  base sites reaching `e` in `Rfoot ≤ 5ℓ^j` steps are `≤ 6³` (DL29 `card_reach_coarse_le`), `3` directions; `3` levels);
* **`massComm_proper`** : `MassComm ell M k κ c S U a CM`, `CM = a · e^{2S/r} · 49 ℓ² K_G · 1944 ℓ²`, under `Admissible`, the
  G4 partition constants (`κ, M, R, c`), and the M0-chain tower hypotheses (`RegTower`, `TowerClass ε`, `ε ≥ 0`, `ρ(ε) < π/2`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1IMS

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.DLayer (Foot Reach Rfoot Foot_reach Rfoot_le card_reach_coarse_le bondRestr bondWt bondWt_apply)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.StatementLane (Tower Admissible scaleUp bigSide pdist)
open AdalyFormal.NonflatJet (rhoOf)
open AdalyFormal.BondComposite (rr TowerClass hdvd_scaleUp sum_le_of_injective)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

theorem levels_le_three (k s : ℕ) :
    ∑ j : Fin (k + 1), (if s ≤ (j : ℕ) + 1 ∧ (j : ℕ) ≤ s + 1 then (1 : ℝ) else 0) ≤ 3 := by
  classical
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h1 : (Finset.univ.filter (fun j : Fin (k + 1) => s ≤ (j : ℕ) + 1 ∧ (j : ℕ) ≤ s + 1)).card
      ≤ (Finset.Icc (s - 1) (s + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun j => (j : ℕ)) ?_ ?_
    · intro j hj
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj
      simp only [Finset.coe_Icc, Set.mem_Icc]
      omega
    · intro j _ j' _ h; exact Fin.ext h
  have h2 : (Finset.Icc (s - 1) (s + 1)).card ≤ 3 := by rw [Nat.card_Icc]; omega
  exact_mod_cast h1.trans h2

section count
variable {ell M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}
  (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 2 ≤ ell) (hR1 : 1 ≤ R)
  (hR : (c + 3) * κ * ell ≤ R) (hc : 5 ≤ c)
include hS hκ hM hell hR1 hR hc

open Classical in
/-- **footprint multiplicity**. -/
theorem foot_count (e : Bond (scaleUp ell k Lu)) :
    ∑ p : BIdx (geomOf ell k S), (if Foot ell (p.1 : ℕ) p.2.1 e then (((ell : ℝ) ^ (p.1 : ℕ))⁻¹) ^ 2 else 0)
      ≤ 1944 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ AdalyFormal.M1.strat S k e.1)⁻¹) ^ 2 := by
  have hell0 : 0 < ell := by omega
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell0
  set s := AdalyFormal.M1.strat S k e.1 with hs
  set g : Fin (k + 1) × Bond (scaleUp ell k Lu) → ℝ := fun jc =>
    if jc.2.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ (jc.1 : ℕ)) ∧ Reach (Rfoot ell (jc.1 : ℕ)) jc.2.1 e.1
        ∧ s ≤ (jc.1 : ℕ) + 1 ∧ (jc.1 : ℕ) ≤ s + 1
    then (((ell : ℝ) ^ (jc.1 : ℕ))⁻¹) ^ 2 else 0 with hg
  have hg0 : ∀ jc, 0 ≤ g jc := fun jc => by simp only [hg]; split_ifs <;> positivity
  -- rows inject into (level, bond)
  set φ : BIdx (geomOf ell k S) → Fin (k + 1) × Bond (scaleUp ell k Lu) := fun p => (p.1, p.2.1) with hφ
  have hφinj : Function.Injective φ := by
    rintro ⟨j, ⟨b, hb⟩⟩ ⟨j', ⟨b', hb'⟩⟩ h
    simp only [hφ, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  have hle : ∀ p : BIdx (geomOf ell k S),
      (if Foot ell (p.1 : ℕ) p.2.1 e then (((ell : ℝ) ^ (p.1 : ℕ))⁻¹) ^ 2 else 0) ≤ g (φ p) := by
    intro p
    split_ifs with he
    · have hw := row_window hS hκ hM hell hR1 hR hc p e he
      have hal := row_aligned hell0 p
      have hre := Foot_reach ell hell0 (p.1 : ℕ) p.2.1 e he
      simp only [hg, hφ]
      rw [if_pos ⟨hal, hre, hw.1, hw.2⟩]
    · exact hg0 _
  refine (Finset.sum_le_sum (fun p _ => hle p)).trans ?_
  refine (sum_le_of_injective φ hφinj g hg0).trans ?_
  rw [Fintype.sum_prod_type]
  -- one level
  have hlev : ∀ j : Fin (k + 1), ∑ b : Bond (scaleUp ell k Lu), g (j, b)
      ≤ (if s ≤ (j : ℕ) + 1 ∧ (j : ℕ) ≤ s + 1 then (1 : ℝ) else 0) * (648 * (ell : ℝ) ^ 2 * ((ell : ℝ) ^ s)⁻¹ ^ 2) := by
    intro j
    have hjk : (j : ℕ) ≤ k := Nat.lt_succ_iff.mp j.isLt
    by_cases hw : s ≤ (j : ℕ) + 1 ∧ (j : ℕ) ≤ s + 1
    · rw [if_pos hw, one_mul]
      -- the weight
      have hwt : (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 ≤ (ell : ℝ) ^ 2 * ((ell : ℝ) ^ s)⁻¹ ^ 2 := by
        have hp : (0 : ℝ) < (ell : ℝ) ^ s := by positivity
        have h1 : (ell : ℝ) ^ s ≤ (ell : ℝ) ^ ((j : ℕ) + 1) :=
          pow_le_pow_right₀ (by exact_mod_cast hell0) hw.1
        have h2 : ((ell : ℝ) ^ ((j : ℕ) + 1))⁻¹ ≤ ((ell : ℝ) ^ s)⁻¹ := inv_anti₀ hp h1
        have h3 : (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 = (ell : ℝ) ^ 2 * (((ell : ℝ) ^ ((j : ℕ) + 1))⁻¹) ^ 2 := by
          field_simp; ring
        rw [h3]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2 2) (by positivity)
      -- the count
      have hcnt : ∑ b : Bond (scaleUp ell k Lu),
          (if b.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ (j : ℕ)) ∧ Reach (Rfoot ell (j : ℕ)) b.1 e.1 then (1 : ℝ) else 0)
          ≤ 648 := by
        rw [Fintype.sum_prod_type_right]
        have hsite : ∑ y : PeriodicLatticeSite (scaleUp ell k Lu),
            (if y ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ (j : ℕ)) ∧ Reach (Rfoot ell (j : ℕ)) y e.1 then (1 : ℝ) else 0)
            ≤ 216 := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
          have hdv : ∀ ν : Fin 3, ell ^ (j : ℕ) ∣ scaleUp ell k Lu ν + 1 := fun ν => hdvd_scaleUp ell k Lu hell0 _ hjk ν
          have h1 := card_reach_coarse_le (ell ^ (j : ℕ)) (pow_pos hell0 _) hdv (Rfoot ell (j : ℕ)) e.1
          have hset : Finset.univ.filter (fun y : PeriodicLatticeSite (scaleUp ell k Lu) =>
                y ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ (j : ℕ)) ∧ Reach (Rfoot ell (j : ℕ)) y e.1)
              = Finset.univ.filter (fun y : PeriodicLatticeSite (scaleUp ell k Lu) =>
                (∀ ν, ell ^ (j : ℕ) ∣ (y ν).val) ∧ Reach (Rfoot ell (j : ℕ)) y e.1) := by
            ext y
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_CoarseLattice, Nat.dvd_iff_mod_eq_zero]
          rw [hset]
          have hdiv : Rfoot ell (j : ℕ) / ell ^ (j : ℕ) ≤ 5 := by
            have := Rfoot_le ell hell (j : ℕ)
            exact Nat.div_le_of_le_mul (by rw [mul_comm]; exact this)
          have h2 : (Rfoot ell (j : ℕ) / ell ^ (j : ℕ) + 1) ^ 3 ≤ 216 := by
            have : Rfoot ell (j : ℕ) / ell ^ (j : ℕ) + 1 ≤ 6 := by omega
            calc (Rfoot ell (j : ℕ) / ell ^ (j : ℕ) + 1) ^ 3 ≤ 6 ^ 3 := Nat.pow_le_pow_left this 3
              _ = 216 := by norm_num
          exact_mod_cast h1.trans h2
        refine (Finset.sum_le_sum (fun μ _ => hsite)).trans ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num
      have hg' : ∀ b : Bond (scaleUp ell k Lu), g (j, b)
          = (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2
            * (if b.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ (j : ℕ)) ∧ Reach (Rfoot ell (j : ℕ)) b.1 e.1
                then (1 : ℝ) else 0) := by
        intro b
        simp only [hg]
        by_cases hb : b.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ (j : ℕ)) ∧ Reach (Rfoot ell (j : ℕ)) b.1 e.1
        · rw [if_pos ⟨hb.1, hb.2, hw.1, hw.2⟩, if_pos hb, mul_one]
        · rw [if_neg (fun h => hb ⟨h.1, h.2.1⟩), if_neg hb, mul_zero]
      rw [Finset.sum_congr rfl (fun b _ => hg' b), ← Finset.mul_sum]
      calc (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ∑ b : Bond (scaleUp ell k Lu),
            (if b.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ (j : ℕ)) ∧ Reach (Rfoot ell (j : ℕ)) b.1 e.1
              then (1 : ℝ) else 0)
          ≤ ((ell : ℝ) ^ 2 * ((ell : ℝ) ^ s)⁻¹ ^ 2) * 648 :=
            mul_le_mul hwt hcnt (Finset.sum_nonneg (fun b _ => by split_ifs <;> norm_num)) (by positivity)
        _ = 648 * (ell : ℝ) ^ 2 * ((ell : ℝ) ^ s)⁻¹ ^ 2 := by ring
    · rw [if_neg hw, zero_mul]
      refine le_of_eq (Finset.sum_eq_zero (fun b _ => ?_))
      simp only [hg]
      rw [if_neg (fun h => hw ⟨h.2.2.1, h.2.2.2⟩)]
  refine (Finset.sum_le_sum (fun j _ => hlev j)).trans ?_
  rw [← Finset.sum_mul]
  have h3 := levels_le_three k s
  have hK : 0 ≤ 648 * (ell : ℝ) ^ 2 * ((ell : ℝ) ^ s)⁻¹ ^ 2 := by positivity
  calc (∑ j : Fin (k + 1), (if s ≤ (j : ℕ) + 1 ∧ (j : ℕ) ≤ s + 1 then (1 : ℝ) else 0))
        * (648 * (ell : ℝ) ^ 2 * ((ell : ℝ) ^ s)⁻¹ ^ 2)
      ≤ 3 * (648 * (ell : ℝ) ^ 2 * ((ell : ℝ) ^ s)⁻¹ ^ 2) := mul_le_mul_of_nonneg_right h3 hK
    _ = 1944 * (ell : ℝ) ^ 2 * ((ell : ℝ) ^ s)⁻¹ ^ 2 := by ring

end count

/-- the mass commutator constant. -/
noncomputable def CMc (ell M κ c k : ℕ) (a : ℝ) (ε : ℕ → ℝ) : ℝ :=
  a * EQ ell k ε ^ 2 * (49 * (ell : ℝ) ^ 2 * KG ell M κ c) * (1944 * (ell : ℝ) ^ 2)

section main
variable {ell M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}
  (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 2 ≤ ell) (hR1 : 1 ≤ R)
  (hR : (c + 3) * κ * ell ≤ R) (hc : 5 ≤ c)
include hS hκ hM hell hR1 hR hc

open Classical in
/-- **the mass commutator on a proper tower**. -/
theorem massComm_proper (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 ≤ a) (ε : ℕ → ℝ)
    (hreg : RegTower ell (bgTower (GF ell k Lu) U) k) (hcl : TowerClass ell k Lu U ε)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2) :
    MassComm ell M k κ c S U a (CMc ell M κ c k a ε) := by
  intro A
  have hell0 : 0 < ell := by omega
  have hK0 := KG_nonneg ell M κ c
  set K1 := a * EQ ell k ε ^ 2 * (49 * (ell : ℝ) ^ 2 * KG ell M κ c) with hK1
  have hK10 : 0 ≤ K1 := by positivity
  simp only [PiLp.norm_sq_eq_of_L2]
  rw [Finset.sum_comm]
  have hrow := fun p => row_comm_sum hS hκ hM hell hR1 hR hc U a ha ε hreg hcl hε0 hsm A p
  refine (Finset.sum_le_sum (fun p _ => hrow p)).trans ?_
  rw [← Finset.mul_sum]
  -- swap rows and bonds
  have hswap : ∑ p : BIdx (geomOf ell k S), (((ell : ℝ) ^ (p.1 : ℕ))⁻¹) ^ 2
        * ∑ e, (if Foot ell (p.1 : ℕ) p.2.1 e then ‖A e‖ ^ 2 else 0)
      = ∑ e, ‖A e‖ ^ 2 * ∑ p : BIdx (geomOf ell k S),
          (if Foot ell (p.1 : ℕ) p.2.1 e then (((ell : ℝ) ^ (p.1 : ℕ))⁻¹) ^ 2 else 0) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun p _ => ?_))
    split_ifs <;> ring
  rw [hswap]
  have hcnt : ∀ e, ‖A e‖ ^ 2 * ∑ p : BIdx (geomOf ell k S),
        (if Foot ell (p.1 : ℕ) p.2.1 e then (((ell : ℝ) ^ (p.1 : ℕ))⁻¹) ^ 2 else 0)
      ≤ (1944 * (ell : ℝ) ^ 2) * ‖bondWt (-sigG (geomOf ell k S)) A e‖ ^ 2 := by
    intro e
    have h := foot_count hS hκ hM hell hR1 hR hc e
    have hw : ‖bondWt (-sigG (geomOf ell k S)) A e‖ ^ 2
        = (((ell : ℝ) ^ AdalyFormal.M1.strat S k e.1)⁻¹) ^ 2 * ‖A e‖ ^ 2 := by
      rw [bondWt_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
      show Real.exp (-(sigG (geomOf ell k S) e.1)) ^ 2 * _ = _
      rw [Real.exp_neg, exp_sig (geomOf ell k S) hell0, ← strat_eq_stratG hell0 hS]
      try rfl
    rw [hw]
    have := mul_le_mul_of_nonneg_left h (sq_nonneg ‖A e‖)
    calc ‖A e‖ ^ 2 * ∑ p : BIdx (geomOf ell k S),
          (if Foot ell (p.1 : ℕ) p.2.1 e then (((ell : ℝ) ^ (p.1 : ℕ))⁻¹) ^ 2 else 0)
        ≤ ‖A e‖ ^ 2 * (1944 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ AdalyFormal.M1.strat S k e.1)⁻¹) ^ 2) := this
      _ = _ := by ring
  have hsum := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hcnt e)
  rw [← Finset.mul_sum] at hsum
  calc K1 * ∑ e, ‖A e‖ ^ 2 * ∑ p : BIdx (geomOf ell k S),
          (if Foot ell (p.1 : ℕ) p.2.1 e then (((ell : ℝ) ^ (p.1 : ℕ))⁻¹) ^ 2 else 0)
      ≤ K1 * ((1944 * (ell : ℝ) ^ 2) * ∑ e, ‖bondWt (-sigG (geomOf ell k S)) A e‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsum hK10
    _ = CMc ell M κ c k a ε * ∑ e, ‖bondWt (-sigG (geomOf ell k S)) A e‖ ^ 2 := by
        rw [hK1]; unfold CMc; ring

end main

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.levels_le_three
#print axioms AdalyFormal.M1IMS.foot_count
#print axioms AdalyFormal.M1IMS.CMc
#print axioms AdalyFormal.M1IMS.massComm_proper
