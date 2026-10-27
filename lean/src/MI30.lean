import MI29
import MI10

/-!
# MI30 -- oscillation of the IMS partition across a bond-jet footprint (M1 lane E, 2026-10-13)

For a constraint row `p = (j, c)` of `G = geomOf ell k S` and a bond `e` of its footprint `Foot ℓ j c`:
`Σ_i (hbond_i(e) − hrow_i(p))² ≤ 49 ℓ² K_G`  (`j ≥ 1`), and `= 0` at `j = 0`.
* `hvec_reach` : telescoping of `x ↦ (h_i(x))_i ∈ ℓ²` along a positive-step path (`Reach`) whose points stay in a set where the
  steps are bounded;
* `pdist_of_reach` : `Reach m x z → pdist x z ≤ m`;
* the anchor of a row lies in `Ω_j`; the collar (`admissible_ball`) puts the `6ℓ^j + 2` ball around it in `Ω_{j-1}`
  (`R ≥ 8ℓ`, `M ≥ 1`), where the G4 step bound is `K_G/ℓ^{2(j-1)}`.
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
open AdalyFormal.DLayer (Foot Reach Rfoot Foot_reach Rfoot_le Reach_trans Reach_coarseShift Reach_refl Reach_mono)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.StatementLane (Tower Admissible scaleUp bigSide pdist)
open AdalyFormal.StatementLaneR8 (pdist_triangle pdist_comm pdist_shift_le pdist_coarseShift_le admissible_ball Ball)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

variable {L : PeriodicLatticeExtent}

theorem pdist_of_reach {m : ℕ} {x z : PeriodicLatticeSite L} (h : Reach m x z) : pdist x z ≤ m := by
  obtain ⟨l, hl, rfl⟩ := h
  have key : ∀ (l : List (Fin 3)) (x : PeriodicLatticeSite L),
      pdist x (l.foldl (fun w μ => periodicLatticeShift w μ) x) ≤ l.length := by
    intro l
    induction l with
    | nil => intro x; simp [AdalyFormal.StatementLaneR8.pdist_self]
    | cons μ rest ih =>
      intro x
      rw [List.foldl_cons, List.length_cons]
      have h1 := pdist_shift_le x μ
      have h2 := ih (periodicLatticeShift x μ)
      have := pdist_triangle x (periodicLatticeShift x μ) (rest.foldl (fun w μ => periodicLatticeShift w μ)
        (periodicLatticeShift x μ))
      omega
  exact (key l x).trans hl

section reach
variable {ι : Type*} [Fintype ι]

/-- telescoping along a `Reach` path inside a ball where every step is bounded. -/
theorem hvec_reach (h : ι → PeriodicLatticeSite L → ℝ) (s0 : ℝ) (hs0 : 0 ≤ s0) :
    ∀ (l : List (Fin 3)) (x : PeriodicLatticeSite L) (m : ℕ), l.length ≤ m →
      (∀ w, pdist x w < m → ∀ μ, dist (hvec h w) (hvec h (periodicLatticeShift w μ)) ≤ s0) →
      dist (hvec h x) (hvec h (l.foldl (fun w μ => periodicLatticeShift w μ) x)) ≤ m * s0 := by
  intro l
  induction l with
  | nil =>
    intro x m _ _
    simp only [List.foldl_nil, dist_self]
    positivity
  | cons μ rest ih =>
    intro x m hl hstep
    rw [List.foldl_cons]
    rw [List.length_cons] at hl
    have hm : 1 ≤ m := by omega
    have h1 : dist (hvec h x) (hvec h (periodicLatticeShift x μ)) ≤ s0 :=
      hstep x (by rw [AdalyFormal.StatementLaneR8.pdist_self]; omega) μ
    have h2 := ih (periodicLatticeShift x μ) (m - 1) (by omega) (fun w hw ν => hstep w (by
      have := pdist_triangle x (periodicLatticeShift x μ) w
      have := pdist_shift_le x μ
      omega) ν)
    have h3 := dist_triangle (hvec h x) (hvec h (periodicLatticeShift x μ))
      (hvec h (rest.foldl (fun w μ => periodicLatticeShift w μ) (periodicLatticeShift x μ)))
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub hm]; simp
    rw [hcast] at h2
    nlinarith

theorem hvec_reach' (h : ι → PeriodicLatticeSite L → ℝ) (s0 : ℝ) (hs0 : 0 ≤ s0) {m : ℕ} {x z : PeriodicLatticeSite L}
    (hr : Reach m x z) (hstep : ∀ w, pdist x w < m → ∀ μ, dist (hvec h w) (hvec h (periodicLatticeShift w μ)) ≤ s0) :
    dist (hvec h x) (hvec h z) ≤ m * s0 := by
  obtain ⟨l, hl, rfl⟩ := hr
  exact hvec_reach h s0 hs0 l x m hl hstep

end reach

section osc
variable {ell M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}
  (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 2 ≤ ell) (hR1 : 1 ≤ R)
  (hR : (c + 3) * κ * ell ≤ R) (hc : 5 ≤ c)
include hS hκ hM hell hR1 hR hc

/-- the endpoint of a bond at which `hbond` reads the partition. -/
noncomputable def bpt (S : Tower L) (e : Bond L) : PeriodicLatticeSite L :=
  open Classical in if e.1 ∈ S.Om 0 then e.1 else periodicLatticeShift e.1 e.2

omit hS hκ hM hell hR1 hR hc in
theorem hbond_eq_bpt (i : Fin (k + 1) × PeriodicLatticeSite (scaleUp ell k Lu)) (e : Bond (scaleUp ell k Lu)) :
    hbond ell M k κ c S i e = AdalyFormal.M1.hpart ell M k κ c S i (bpt S e) := by
  classical
  unfold hbond bpt
  split_ifs <;> rfl

/-- **oscillation of the partition across a footprint**. -/
theorem osc_foot (p : BIdx (geomOf ell k S)) (e : Bond (scaleUp ell k Lu)) (he : Foot ell (p.1 : ℕ) p.2.1 e) :
    ∑ i, (hbond ell M k κ c S i e - hrow ell M k κ c S i p) ^ 2 ≤ 49 * (ell : ℝ) ^ 2 * KG ell M κ c := by
  classical
  have hell0 : 0 < ell := by omega
  have hK0 := KG_nonneg ell M κ c
  set j : ℕ := (p.1 : ℕ) with hjdef
  have hj : j ≤ k := Nat.lt_succ_iff.mp p.1.isLt
  set x0 := p.2.1.1 with hx0
  -- j = 0: the footprint is the row's own bond and both read the same endpoint
  by_cases hj0 : j = 0
  · have hfe : e = p.2.1 := by
      have : Foot ell 0 p.2.1 e := by rw [← hj0]; exact he
      exact this
    have h10 : (p.1 : ℕ) = 0 := hj0
    have hrb : rowBase (geomOf ell k S) p = bpt S p.2.1 := by
      unfold rowBase bpt
      simp only [show (geomOf ell k S).ell = ell from rfl, h10, pow_zero]
      by_cases hin : p.2.1.1 ∈ S.Om 0
      · have hin' : p.2.1.1 ∈ (geomOf ell k S).Om0 := hin
        rw [if_pos hin', if_pos hin]
      · have hin' : p.2.1.1 ∉ (geomOf ell k S).Om0 := hin
        rw [if_neg hin', if_neg hin]; rfl
    have hz : ∀ i, hbond ell M k κ c S i e - hrow ell M k κ c S i p = 0 := by
      intro i
      rw [hbond_eq_bpt, hfe]
      unfold hrow
      rw [hrb, sub_self]
    calc ∑ i, (hbond ell M k κ c S i e - hrow ell M k κ c S i p) ^ 2 = 0 :=
          Finset.sum_eq_zero (fun i _ => by rw [hz i]; ring)
      _ ≤ 49 * (ell : ℝ) ^ 2 * KG ell M κ c := mul_nonneg (by positivity) hK0
  have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
  -- the anchor `a ∈ Λ_j ⊆ Ω_j` and its distance to `x0`
  have hanc : ∃ a, a ∈ S.Om j ∧ pdist a x0 ≤ ell ^ j := by
    have hb : p.2.1.1 ∈ (geomOf ell k S).Lam (p.1 : ℕ) ∨
        coarseShift p.2.1.1 ((geomOf ell k S).ell ^ (p.1 : ℕ)) p.2.1.2 ∈ (geomOf ell k S).Lam (p.1 : ℕ) := p.2.2.1
    rcases hb with h | h
    · exact ⟨x0, h.2.1, by rw [AdalyFormal.StatementLaneR8.pdist_self]; exact Nat.zero_le _⟩
    · refine ⟨coarseShift x0 (ell ^ j) p.2.1.2, h.2.1, ?_⟩
      rw [pdist_comm]; exact pdist_coarseShift_le x0 (ell ^ j) p.2.1.2
  obtain ⟨a, haO, had⟩ := hanc
  -- the collar ball
  have hRl : 8 * ell ≤ R := by
    have h1 : 8 ≤ (c + 3) * κ := le_trans (by omega : 8 ≤ c + 3) (Nat.le_mul_of_pos_right _ hκ)
    exact le_trans (Nat.mul_le_mul_right ell h1) hR
  have hball : ∀ w, pdist x0 w ≤ 6 * ell ^ j → w ∈ S.Om (j - 1) := by
    intro w hw
    have hsub := admissible_ball hS (j := j - 1) (by omega) (y := a) (by rw [Nat.sub_add_cancel hj1]; exact haO)
    apply hsub
    show pdist a w ≤ R * bigSide M ell (j - 1)
    have htri := pdist_triangle a x0 w
    have hpow : ell ^ j = ell * ell ^ (j - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h1 : 7 * ell ^ j ≤ R * (M * ell ^ (j - 1)) := by
      have hM1 : 1 ≤ M := hM
      calc 7 * ell ^ j ≤ 8 * ell ^ j := by omega
        _ = (8 * ell) * ell ^ (j - 1) := by rw [hpow]; ring
        _ ≤ R * ell ^ (j - 1) := Nat.mul_le_mul_right _ hRl
        _ ≤ R * (M * ell ^ (j - 1)) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hM)
    unfold bigSide
    omega
  -- the step bound in the ball
  have hlr : (0 : ℝ) < (ell : ℝ) ^ (j - 1) := by have : (0 : ℝ) < ell := (by exact_mod_cast hell0); positivity
  set s0 := Real.sqrt (KG ell M κ c) / (ell : ℝ) ^ (j - 1) with hs0def
  have hs0 : 0 ≤ s0 := by positivity
  have hstep : ∀ w, pdist x0 w < 6 * ell ^ j → ∀ μ,
      dist (hvec (hfam ell M k κ c S) w) (hvec (hfam ell M k κ c S) (periodicLatticeShift w μ)) ≤ s0 := by
    intro w hw μ
    have hwO := hball w (by omega)
    have hwO' := hball (periodicLatticeShift w μ) (by
      have := pdist_triangle x0 w (periodicLatticeShift w μ)
      have := pdist_shift_le w μ
      omega)
    have hw0 : w ∈ S.Om 0 := AdalyFormal.StatementLaneR8.admissible_mono hS (j - 1) hwO
    have hw0' : periodicLatticeShift w μ ∈ S.Om 0 := AdalyFormal.StatementLaneR8.admissible_mono hS (j - 1) hwO'
    have hs := hpart_step hS hκ hM (by omega) hR1 hR hc hw0 μ hw0'
    have hstr : j - 1 ≤ AdalyFormal.M1.strat S k w := AdalyFormal.M1.le_strat_of_mem (by omega) hwO
    have hpowle : ((ell : ℝ) ^ (j - 1)) ^ 2 ≤ ((ell : ℝ) ^ AdalyFormal.M1.strat S k w) ^ 2 := by
      have : (ell : ℝ) ^ (j - 1) ≤ (ell : ℝ) ^ AdalyFormal.M1.strat S k w :=
        pow_le_pow_right₀ (by exact_mod_cast hell0) hstr
      exact pow_le_pow_left₀ hlr.le this 2
    have hs' : ∑ i, (hfam ell M k κ c S i w - hfam ell M k κ c S i (periodicLatticeShift w μ)) ^ 2
        ≤ KG ell M κ c / ((ell : ℝ) ^ (j - 1)) ^ 2 :=
      hs.trans (div_le_div_of_nonneg_left hK0 (by positivity) hpowle)
    have hsq := hvec_dist_sq (hfam ell M k κ c S) w (periodicLatticeShift w μ)
    have hd0 := dist_nonneg (x := hvec (hfam ell M k κ c S) w) (y := hvec (hfam ell M k κ c S) (periodicLatticeShift w μ))
    have h2 : dist (hvec (hfam ell M k κ c S) w) (hvec (hfam ell M k κ c S) (periodicLatticeShift w μ)) ^ 2 ≤ s0 ^ 2 := by
      rw [hsq, hs0def, div_pow, Real.sq_sqrt hK0]; exact hs'
    exact (pow_le_pow_iff_left₀ hd0 hs0 two_ne_zero).mp h2
  -- the two paths from `x0`
  have hRf := Rfoot_le ell hell j
  have hre : Reach (Rfoot ell j + 1) x0 (bpt S e) := by
    have h1 : Reach (Rfoot ell j) x0 e.1 := Foot_reach ell hell0 j p.2.1 e he
    have h2 : Reach 1 e.1 (bpt S e) := by
      unfold bpt
      split_ifs
      · exact Reach_mono (Nat.zero_le 1) (Reach_refl _)
      · exact ⟨[e.2], by simp, rfl⟩
    exact Reach_trans h1 h2
  have hrb : Reach (ell ^ j) x0 (rowBase (geomOf ell k S) p) := by
    unfold rowBase
    split_ifs
    · exact Reach_mono (Nat.zero_le _) (Reach_refl _)
    · exact Reach_coarseShift (ell ^ j) x0 p.2.1.2
  have hd1 := hvec_reach' (hfam ell M k κ c S) s0 hs0 hre (fun w hw μ => hstep w (by
    have : 1 ≤ ell ^ j := Nat.one_le_pow _ _ hell0
    omega) μ)
  have hd2 := hvec_reach' (hfam ell M k κ c S) s0 hs0 hrb (fun w hw μ => hstep w (by
    have : 1 ≤ ell ^ j := Nat.one_le_pow _ _ hell0
    omega) μ)
  have hdist : dist (hvec (hfam ell M k κ c S) (bpt S e)) (hvec (hfam ell M k κ c S) (rowBase (geomOf ell k S) p))
      ≤ 7 * (ell : ℝ) ^ j * s0 := by
    have ht := dist_triangle (hvec (hfam ell M k κ c S) (bpt S e)) (hvec (hfam ell M k κ c S) x0)
      (hvec (hfam ell M k κ c S) (rowBase (geomOf ell k S) p))
    rw [dist_comm] at hd1
    have hcast1 : ((Rfoot ell j + 1 : ℕ) : ℝ) ≤ 6 * (ell : ℝ) ^ j := by
      have : 1 ≤ ell ^ j := Nat.one_le_pow _ _ hell0
      have : Rfoot ell j + 1 ≤ 6 * ell ^ j := by omega
      exact_mod_cast this
    have hcast2 : ((ell ^ j : ℕ) : ℝ) = (ell : ℝ) ^ j := by push_cast; rfl
    rw [hcast2] at hd2
    have e1 := mul_le_mul_of_nonneg_right hcast1 hs0
    linarith
  have hsq := hvec_dist_sq (hfam ell M k κ c S) (bpt S e) (rowBase (geomOf ell k S) p)
  have hd0 := dist_nonneg (x := hvec (hfam ell M k κ c S) (bpt S e))
    (y := hvec (hfam ell M k κ c S) (rowBase (geomOf ell k S) p))
  have hval : 7 * (ell : ℝ) ^ j * s0 = 7 * (ell : ℝ) * Real.sqrt (KG ell M κ c) := by
    rw [hs0def]
    have hpow : (ell : ℝ) ^ j = (ell : ℝ) * (ell : ℝ) ^ (j - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hpow]; field_simp
  rw [hval] at hdist
  have hfin : ∑ i, (hfam ell M k κ c S i (bpt S e) - hfam ell M k κ c S i (rowBase (geomOf ell k S) p)) ^ 2
      ≤ 49 * (ell : ℝ) ^ 2 * KG ell M κ c := by
    rw [← hsq]
    calc dist (hvec (hfam ell M k κ c S) (bpt S e)) (hvec (hfam ell M k κ c S) (rowBase (geomOf ell k S) p)) ^ 2
        ≤ (7 * (ell : ℝ) * Real.sqrt (KG ell M κ c)) ^ 2 := pow_le_pow_left₀ hd0 hdist 2
      _ = 49 * (ell : ℝ) ^ 2 * KG ell M κ c := by rw [mul_pow, mul_pow, Real.sq_sqrt hK0]; ring
  refine Eq.trans_le ?_ hfin
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hbond_eq_bpt]
  rfl

end osc

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.pdist_of_reach
#print axioms AdalyFormal.M1IMS.hvec_reach
#print axioms AdalyFormal.M1IMS.hvec_reach'
#print axioms AdalyFormal.M1IMS.bpt
#print axioms AdalyFormal.M1IMS.hbond_eq_bpt
#print axioms AdalyFormal.M1IMS.osc_foot
