import DY1
import DQ6
import MI32

/-!
# DY2 -- ball-local rows of the composite second jet on a proper tower (M1 D-layer lane, clause 2, 2026-10-14)

`G = geomOf ℓ k S`, row `p = (n, b)`, read ball `B_p = Ball b.1 (rhoT ℓ n)` (r8 `C2CompL_congr_in`; NO regularity needed).
* `ballRes p u` : `u` restricted to the bonds with base in `B_p`;
* `C2row_congr` : the row `p` of `C2fullOf G V` reads only `B_p`;
* **`polar_row_ball`** : `Σ_q ‖C2 z q‖ ≤ K ‖wq z‖²` (all `z`) ⟹ `‖β(u,v)(p)‖ ≤ K ‖wq(ballRes p u)‖ ‖wq(ballRes p v)‖`;
* `ball_window` : a bond read by a level-`n ≥ 1` row has `n ≤ bstrat e + 1` and `bstrat e ≤ n + 1` (room `18ℓ ≤ RM`);
* **`ball_mult`** : `Σ_p ‖wq(ballRes p u)‖² ≤ 44217 ‖wq u‖²` over the rows of level `≥ 1` (3 levels, `3·17³` rows each).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DStrat

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2 (C2fullOf C2rawB_eq C2CompL TowerGeom Cfg FSp BIdx geomOf bondsLam bgTower suCoord
  suCoordInv)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist)
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle pdist_shift_le rhoT rhoT_le C2CompL_congr_in)
open AdalyFormal.DLayer (polar polar_eq)
open AdalyFormal.M1 (bstrat strat wnormSq)
open AdalyFormal.M1DStrat.DQ (row_anchor row_base_aligned bstrat_ge_prev strat_le_of_near room_prev room_next)
open AdalyFormal.BondComposite (hdvd_scaleUp sum_le_of_injective)

/-! ## 1. restriction to the read ball, row congruence -/

section ball
variable {L : PeriodicLatticeExtent} (G : TowerGeom L)

open Classical in
/-- restriction to the read ball of the row `p` -/
noncomputable def ballRes (p : BIdx G) (u : BondFnL2 L) : BondFnL2 L :=
  WithLp.toLp 2 (fun e => if e.1 ∈ Ball p.2.1.1 (rhoT G.ell p.1) then u e else 0)

theorem ballRes_apply_in (p : BIdx G) (u : BondFnL2 L) (e : Bond L) (he : e.1 ∈ Ball p.2.1.1 (rhoT G.ell p.1)) :
    ballRes G p u e = u e := by
  classical
  show (if e.1 ∈ Ball p.2.1.1 (rhoT G.ell p.1) then u e else 0) = u e
  rw [if_pos he]

theorem ballRes_add (p : BIdx G) (u v : BondFnL2 L) : ballRes G p (u + v) = ballRes G p u + ballRes G p v := by
  classical
  refine PiLp.ext (fun e => ?_)
  show (if e.1 ∈ Ball p.2.1.1 (rhoT G.ell p.1) then (u + v) e else 0)
    = (if e.1 ∈ Ball p.2.1.1 (rhoT G.ell p.1) then u e else 0) + (if e.1 ∈ Ball p.2.1.1 (rhoT G.ell p.1) then v e else 0)
  split_ifs <;> simp

theorem ballRes_sub (p : BIdx G) (u v : BondFnL2 L) : ballRes G p (u - v) = ballRes G p u - ballRes G p v := by
  classical
  refine PiLp.ext (fun e => ?_)
  show (if e.1 ∈ Ball p.2.1.1 (rhoT G.ell p.1) then (u - v) e else 0)
    = (if e.1 ∈ Ball p.2.1.1 (rhoT G.ell p.1) then u e else 0) - (if e.1 ∈ Ball p.2.1.1 (rhoT G.ell p.1) then v e else 0)
  split_ifs <;> simp

/-- **the row `p` reads only its ball** -/
theorem C2row_congr (hell : 0 < G.ell) (V : Cfg L) (p : BIdx G) (z z' : BondFnL2 L)
    (h : ∀ e : Bond L, e.1 ∈ Ball p.2.1.1 (rhoT G.ell p.1) → z e = z' e) :
    C2fullOf G V z p = C2fullOf G V z' p := by
  show (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (AdalyFormal.IngredientFamilyR2.C2rawB G V p.1 z)) p.2.1
    = (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (AdalyFormal.IngredientFamilyR2.C2rawB G V p.1 z')) p.2.1
  rw [C2rawB_eq, C2rawB_eq]
  have hc := C2CompL_congr_in G.ell hell (bgTower G V) p.1 p.2.1 (a := suCoord z) (a' := suCoord z')
    (fun e he => by
      show AdalyFormal.IngredientFamilyR2.fromM2 ((WithLp.ofLp z e : SuTwo) : AdalyFormal.Balaban.SuTwoLogExp.M2)
        = AdalyFormal.IngredientFamilyR2.fromM2 ((WithLp.ofLp z' e : SuTwo) : AdalyFormal.Balaban.SuTwoLogExp.M2)
      rw [h e he])
  show (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (⟨AdalyFormal.IngredientFamilyR2.toM2
      (C2CompL G.ell (bgTower G V) p.1 (suCoord z) p.2.1), AdalyFormal.IngredientFamilyR2.toM2_mem _⟩ : SuTwo)
    = (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (⟨AdalyFormal.IngredientFamilyR2.toM2
      (C2CompL G.ell (bgTower G V) p.1 (suCoord z') p.2.1), AdalyFormal.IngredientFamilyR2.toM2_mem _⟩ : SuTwo)
  simp only [hc]

/-- **the polarized row from the read ball** -/
theorem polar_row_ball (hell : 0 < G.ell) (V : Cfg L) (T : BondFnL2 L →L[ℝ] BondFnL2 L) (K : ℝ) (hK : 0 ≤ K)
    (hC : ∀ z : BondFnL2 L, ∑ q, ‖C2fullOf G V z q‖ ≤ K * ‖T z‖ ^ 2) (p : BIdx G) (u v : BondFnL2 L) :
    ‖polar G V u v p‖ ≤ K * ‖T (ballRes G p u)‖ * ‖T (ballRes G p v)‖ := by
  have hrow : polar G V u v p = polar G V (ballRes G p u) (ballRes G p v) p := by
    unfold polar
    rw [PiLp.smul_apply, PiLp.smul_apply, PiLp.sub_apply, PiLp.sub_apply]
    rw [C2row_congr G hell V p (u + v) (ballRes G p u + ballRes G p v) (fun e he => by
        rw [← ballRes_add, ballRes_apply_in G p _ e he]),
      C2row_congr G hell V p (u - v) (ballRes G p u - ballRes G p v) (fun e he => by
        rw [← ballRes_sub, ballRes_apply_in G p _ e he])]
  rw [hrow]
  refine le_trans ?_ (polar_l1_T G V T K hK hC _ _)
  exact Finset.single_le_sum (f := fun q => ‖polar G V (ballRes G p u) (ballRes G p v) q‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ p)

end ball

/-! ## 2. the level window and the multiplicity -/

section mult
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}
  (hA : Admissible ell M R k S) (hell2 : 2 ≤ ell) (hroom : 18 * ell ≤ R * M)
include hA hell2 hroom

/-- **the level window of a read ball** -/
theorem ball_window {n : ℕ} (hn1 : 1 ≤ n) (hnk : n ≤ k) {b : Bond (scaleUp ell k Lu)}
    (hb : b ∈ bondsLam (geomOf ell k S) n) (e : Bond (scaleUp ell k Lu)) (he : pdist b.1 e.1 ≤ rhoT ell n) :
    n ≤ bstrat S k e + 1 ∧ bstrat S k e ≤ n + 1 := by
  obtain ⟨y, hy, hy', hby, -⟩ := row_anchor ell k S hb
  have hR1 := room_prev hell2 hroom hn1 (n := n)
  have hR2 := room_next hell2 hroom n
  have hey : pdist e.1 y ≤ rhoT ell n + ell ^ n := by
    have := pdist_triangle e.1 b.1 y
    rw [pdist_comm e.1 b.1] at this
    omega
  constructor
  · have h1 : pdist e.1 y ≤ R * M * ell ^ (n - 1) := by omega
    have h2 : pdist (periodicLatticeShift e.1 e.2) y ≤ R * M * ell ^ (n - 1) := by
      have := pdist_triangle (periodicLatticeShift e.1 e.2) e.1 y
      have h3 := pdist_shift_le e.1 e.2
      rw [pdist_comm] at h3
      omega
    have := bstrat_ge_prev hA hn1 hnk hy e h1 h2
    omega
  · have hye : pdist y e.1 ≤ R * (M * ell ^ (n + 1)) := by
      rw [pdist_comm]; omega
    have := strat_le_of_near hA hnk hy hy' hye
    have hb' : bstrat S k e ≤ strat S k e.1 := by unfold bstrat; exact min_le_left _ _
    omega

omit hA hell2 hroom in
open Classical in
/-- the squared weighted norm of a restriction, as a sum over bonds -/
theorem wq_ballRes_sq (p : BIdx (geomOf ell k S)) (u : BondFnL2 (scaleUp ell k Lu)) :
    ‖wq S ell k (ballRes (geomOf ell k S) p u)‖ ^ 2
      = ∑ e, if e.1 ∈ Ball p.2.1.1 (rhoT ell p.1) then ‖wq S ell k u e‖ ^ 2 else 0 := by
  rw [PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [wq_apply, wq_apply]
  show ‖(((ell : ℝ) ^ bstrat S k e)⁻¹) • (if e.1 ∈ Ball p.2.1.1 (rhoT ell p.1) then u e else 0)‖ ^ 2 = _
  split_ifs <;> simp

open Classical in
/-- rows of level `≥ 1` whose read ball contains a given bond: at most `44217` -/
theorem ball_count (e : Bond (scaleUp ell k Lu)) :
    ((Finset.univ.filter (fun p : BIdx (geomOf ell k S) =>
      1 ≤ (p.1 : ℕ) ∧ e.1 ∈ Ball p.2.1.1 (rhoT ell p.1))).card : ℝ) ≤ 44217 := by
  have hell0 : 0 < ell := by omega
  set s := bstrat S k e with hs
  -- rows inject into (level, bond)
  set φ : BIdx (geomOf ell k S) → Fin (k + 1) × Bond (scaleUp ell k Lu) := fun p => (p.1, p.2.1) with hφ
  have hφinj : Function.Injective φ := by
    rintro ⟨j, ⟨b, hb⟩⟩ ⟨j', ⟨b', hb'⟩⟩ h
    simp only [hφ, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  set g : Fin (k + 1) × Bond (scaleUp ell k Lu) → ℝ := fun jc =>
    if jc.2.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ (jc.1 : ℕ)) ∧ pdist jc.2.1 e.1 ≤ rhoT ell jc.1
        ∧ s ≤ (jc.1 : ℕ) + 1 ∧ (jc.1 : ℕ) ≤ s + 1
    then (1 : ℝ) else 0 with hg
  have hg0 : ∀ jc, 0 ≤ g jc := fun jc => by simp only [hg]; split_ifs <;> norm_num
  rw [Finset.card_filter]
  push_cast
  have hle : ∀ p : BIdx (geomOf ell k S),
      (if 1 ≤ (p.1 : ℕ) ∧ e.1 ∈ Ball p.2.1.1 (rhoT ell p.1) then (1 : ℝ) else 0) ≤ g (φ p) := by
    intro p
    split_ifs with hp
    · have hnk : (p.1 : ℕ) ≤ k := Nat.lt_succ_iff.mp p.1.isLt
      have hw := ball_window hA hell2 hroom hp.1 hnk p.2.2 e hp.2
      have hal := row_base_aligned ell k Lu hell0 S hnk p.2.2
      simp only [hg, hφ]
      rw [if_pos ⟨hal, hp.2, hw.2, hw.1⟩]
    · exact hg0 _
  refine (Finset.sum_le_sum (fun p _ => hle p)).trans ?_
  refine (sum_le_of_injective φ hφinj g hg0).trans ?_
  rw [Fintype.sum_prod_type]
  have hlev : ∀ j : Fin (k + 1), ∑ b : Bond (scaleUp ell k Lu), g (j, b)
      ≤ (if s ≤ (j : ℕ) + 1 ∧ (j : ℕ) ≤ s + 1 then (1 : ℝ) else 0) * 14739 := by
    intro j
    have hjk : (j : ℕ) ≤ k := Nat.lt_succ_iff.mp j.isLt
    by_cases hw : s ≤ (j : ℕ) + 1 ∧ (j : ℕ) ≤ s + 1
    · rw [if_pos hw, one_mul]
      have hg' : ∀ b : Bond (scaleUp ell k Lu), g (j, b)
          = (if b.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ (j : ℕ)) ∧ pdist b.1 e.1 ≤ rhoT ell j
              then (1 : ℝ) else 0) := by
        intro b
        simp only [hg]
        by_cases hb : b.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ (j : ℕ)) ∧ pdist b.1 e.1 ≤ rhoT ell j
        · rw [if_pos ⟨hb.1, hb.2, hw.1, hw.2⟩, if_pos hb]
        · rw [if_neg (fun h => hb ⟨h.1, h.2.1⟩), if_neg hb]
      rw [Finset.sum_congr rfl (fun b _ => hg' b), Fintype.sum_prod_type_right]
      have hsite : ∑ y : PeriodicLatticeSite (scaleUp ell k Lu),
          (if y ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ (j : ℕ)) ∧ pdist y e.1 ≤ rhoT ell j then (1 : ℝ) else 0)
          ≤ 4913 := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
        have hdv : ∀ ν : Fin 3, ell ^ (j : ℕ) ∣ scaleUp ell k Lu ν + 1 := fun ν => hdvd_scaleUp ell k Lu hell0 _ hjk ν
        have h1 := card_ball_coarse_le (ell ^ (j : ℕ)) (pow_pos hell0 _) hdv (rhoT ell j) e.1
        have hset : Finset.univ.filter (fun y : PeriodicLatticeSite (scaleUp ell k Lu) =>
              y ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ (j : ℕ)) ∧ pdist y e.1 ≤ rhoT ell j)
            = Finset.univ.filter (fun y : PeriodicLatticeSite (scaleUp ell k Lu) =>
              (∀ ν, ell ^ (j : ℕ) ∣ (y ν).val) ∧ pdist y e.1 ≤ rhoT ell j) := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_CoarseLattice, Nat.dvd_iff_mod_eq_zero]
        rw [hset]
        have hT := rhoT_le ell hell2 j
        have hdiv : 2 * rhoT ell j / ell ^ (j : ℕ) ≤ 16 :=
          Nat.div_le_of_le_mul (by rw [mul_comm]; omega)
        have h2 : (2 * rhoT ell j / ell ^ (j : ℕ) + 1) ^ 3 ≤ 4913 := by
          have : 2 * rhoT ell j / ell ^ (j : ℕ) + 1 ≤ 17 := by omega
          calc (2 * rhoT ell j / ell ^ (j : ℕ) + 1) ^ 3 ≤ 17 ^ 3 := Nat.pow_le_pow_left this 3
            _ = 4913 := by norm_num
        exact_mod_cast h1.trans h2
      refine (Finset.sum_le_sum (fun μ _ => hsite)).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num
    · rw [if_neg hw, zero_mul]
      refine le_of_eq (Finset.sum_eq_zero (fun b _ => ?_))
      simp only [hg]
      rw [if_neg (fun h => hw ⟨h.2.2.1, h.2.2.2⟩)]
  refine (Finset.sum_le_sum (fun j _ => hlev j)).trans ?_
  rw [← Finset.sum_mul]
  have h3 := AdalyFormal.M1IMS.levels_le_three k s
  nlinarith

open Classical in
/-- **multiplicity of the read balls** -/
theorem ball_mult (u : BondFnL2 (scaleUp ell k Lu)) :
    ∑ p : BIdx (geomOf ell k S), (if 1 ≤ (p.1 : ℕ) then ‖wq S ell k (ballRes (geomOf ell k S) p u)‖ ^ 2 else 0)
      ≤ 44217 * ‖wq S ell k u‖ ^ 2 := by
  have e1 : ∀ p : BIdx (geomOf ell k S),
      (if 1 ≤ (p.1 : ℕ) then ‖wq S ell k (ballRes (geomOf ell k S) p u)‖ ^ 2 else 0)
        = ∑ e, if 1 ≤ (p.1 : ℕ) ∧ e.1 ∈ Ball p.2.1.1 (rhoT ell p.1) then ‖wq S ell k u e‖ ^ 2 else 0 := by
    intro p
    split_ifs with hp
    · rw [wq_ballRes_sq]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      by_cases he : e.1 ∈ Ball p.2.1.1 (rhoT ell p.1)
      · rw [if_pos he, if_pos ⟨hp, he⟩]
      · rw [if_neg he, if_neg (fun h => he h.2)]
    · exact (Finset.sum_eq_zero (fun e _ => by rw [if_neg (fun h => hp h.1)])).symm
  rw [Finset.sum_congr rfl (fun p _ => e1 p), Finset.sum_comm, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_le_sum (fun e _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (ball_count hA hell2 hroom e) (sq_nonneg _)

end mult

#print axioms ballRes
#print axioms ballRes_apply_in
#print axioms ballRes_add
#print axioms ballRes_sub
#print axioms C2row_congr
#print axioms polar_row_ball
#print axioms ball_window
#print axioms wq_ballRes_sq
#print axioms ball_count
#print axioms ball_mult

end AdalyFormal.M1DStrat
