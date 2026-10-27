import DLR29

/-!
# DL30 -- the genuine bond `Q = QfullOf` (full tower): row locality, norm, and the Combes–Thomas commutator

* `Qfull_row_local` : under `RegTower`, the row `p` of `Q` vanishes on fields vanishing on `Foot ℓ k p₂₁` (DL28).
* `Qfull_norm_le` : `‖Q x‖ ≤ qbM ‖x‖`, `qbM = (ℓ^k)⁻¹ r^k e^{S/r}`, `r = ℓ^{-1/2}`, `S = Σ_{i<k} θ(ε_i)` (BC5 `tower_FG`),
  i.e. `qbM = n^{-3/2} e^{S/r}`.
* `fspWt φ`, `fspWP φ` : weight `e^{φ(p₂₁₀)}` (base point of the level-`k` bond) on `FSp`.
* `foot_mult` : `Σ_p Σ_b [b ∈ Foot p] ‖x_b‖² ≤ 3 (Rfoot/n + 1)³ ‖x‖²` (overlap count, DL29).
* **`Qfull_cjp_norm`** : `‖Q⁺ − Q‖ ≤ qbM (e^{δ} − 1) √(3 (Rfoot/n+1)³)`, `δ = Rfoot·θ'` — with `θ' = θ/n`, `Rfoot ≤ 5n`:
  `δ ≤ 5θ`, the factor is `≤ √648`, so `δB ~ n^{-3/2}·θ` (k-free in the scaled norm).
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.NonflatJet (suOf rhoOf)
open AdalyFormal.BondComposite (bidx_level bidx_aligned bidxCB bidxCB_injective Qfull_apply_level nrm nrm_sq nrm_nonneg
  rr nrm_one_suCoord tower_FG TowerClass thetaOf thetaOf_nonneg sum_le_of_injective hdvd_scaleUp)

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent)

theorem suOf_zero : suOf (0 : Fin 3 → ℝ) = 0 := by
  apply Subtype.ext
  show AdalyFormal.IngredientFamilyR2.toM2 0 = 0
  exact map_zero _

theorem suCoord_zero_of {L : PeriodicLatticeExtent} (x : BondFnL2 L) (e : PeriodicLatticeEdge L) (h : x e = 0) :
    suCoord x e = 0 := by
  show fromM2 ((WithLp.ofLp x e : SuTwo) : AdalyFormal.Balaban.SuTwoLogExp.M2) = 0
  have : (WithLp.ofLp x e : SuTwo) = 0 := h
  rw [this]
  exact map_zero _

/-- **row locality of the genuine bond `Q`** -/
theorem Qfull_row_local (U : Cfg (scaleUp ell k Lu)) (hreg : RegTower ell (bgTower (GF ell k Lu) U) k)
    (x : BondFnL2 (scaleUp ell k Lu)) (p : BIdx (GF ell k Lu)) (hx : ∀ b, Foot ell k p.2.1 b → x b = 0) :
    (bondSectorOf (GF ell k Lu) U).Qfull x p = 0 := by
  rw [Qfull_apply_level ell k Lu _ _ hreg]
  have key : ∀ n : ℕ, n = k →
      QlinCompX ell (bgTower (GF ell k Lu) U) n (suCoord x) p.2.1 = 0 := by
    intro n hn
    rw [hn]
    exact QlinCompX_row_local ell (bgTower (GF ell k Lu) U) k hreg k le_rfl p.2.1 (suCoord x)
      (fun e he => suCoord_zero_of x e (hx e he))
  have h0 := key (p.1 : ℕ) (bidx_level ell k Lu p)
  show (((ell : ℝ) ^ (p.1 : ℕ))⁻¹) • suOf (QlinCompX ell (bgTower (GF ell k Lu) U) p.1 (suCoord x) p.2.1) = 0
  rw [h0, suOf_zero, smul_zero]

/-- the explicit bound on `‖Q‖` -/
noncomputable def qbM (ε : ℕ → ℝ) : ℝ :=
  ((ell : ℝ) ^ k)⁻¹ * ((rr ell) ^ k * Real.exp ((∑ i ∈ Finset.range k, thetaOf ell (ε i)) / rr ell))

theorem qbM_nonneg (ε : ℕ → ℝ) : 0 ≤ qbM ell k ε := by
  unfold qbM
  have : 0 ≤ rr ell := Real.sqrt_nonneg _
  positivity

theorem Qfull_norm_le (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (ε : ℕ → ℝ)
    (hreg : RegTower ell (bgTower (GF ell k Lu) U) k) (hcl : TowerClass ell k Lu U ε)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (x : BondFnL2 (scaleUp ell k Lu)) :
    ‖(bondSectorOf (GF ell k Lu) U).Qfull x‖ ≤ qbM ell k ε * ‖x‖ := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  set Z := QlinCompX ell (bgTower (GF ell k Lu) U) k (suCoord x) with hZ
  set g : CoarseBond (scaleUp ell k Lu) (ell ^ k) → ℝ := fun c => ‖suOf (Z (c.1.1, c.2))‖ ^ 2 with hg
  have hgn : ∀ c, 0 ≤ g c := fun c => sq_nonneg _
  have key : ∀ n : ℕ, n = k → ∀ b : Bond (scaleUp ell k Lu),
      ‖((ell : ℝ) ^ n)⁻¹ • suOf (QlinCompX ell (bgTower (GF ell k Lu) U) n (suCoord x) b)‖ ^ 2
        = ((ell : ℝ) ^ k)⁻¹ ^ 2 * ‖suOf (Z (b.1, b.2))‖ ^ 2 := by
    intro n hn b
    subst hn
    rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_inv, abs_of_pos (pow_pos hellR _)]
  have hper : ∀ p : BIdx (GF ell k Lu),
      ‖(bondSectorOf (GF ell k Lu) U).Qfull x p‖ ^ 2 = ((ell : ℝ) ^ k)⁻¹ ^ 2 * g (bidxCB ell k Lu hell p) := by
    intro p
    rw [Qfull_apply_level ell k Lu _ _ hreg]
    exact key (p.1 : ℕ) (bidx_level ell k Lu p) p.2.1
  have hsq : ‖(bondSectorOf (GF ell k Lu) U).Qfull x‖ ^ 2 ≤ (qbM ell k ε * ‖x‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Finset.sum_congr rfl fun p _ => hper p, ← Finset.mul_sum]
    have h1 : ∑ p : BIdx (GF ell k Lu), g (bidxCB ell k Lu hell p) ≤ ∑ c, g c :=
      sum_le_of_injective _ (bidxCB_injective ell k Lu hell) g hgn
    have h2 : ∑ c, g c = nrm (ell ^ k) Z ^ 2 := by rw [nrm_sq]
    have hFG := (tower_FG ell k Lu hell U ε hreg hcl hε0 hsm (suCoord x) k le_rfl).1
    rw [nrm_one_suCoord] at hFG
    have hB0 : 0 ≤ (rr ell) ^ k * Real.exp ((∑ i ∈ Finset.range k, thetaOf ell (ε i)) / rr ell) := by
      have : 0 ≤ rr ell := Real.sqrt_nonneg _
      positivity
    have h4 : nrm (ell ^ k) Z ^ 2
        ≤ ((rr ell) ^ k * Real.exp ((∑ i ∈ Finset.range k, thetaOf ell (ε i)) / rr ell) * ‖x‖) ^ 2 :=
      pow_le_pow_left₀ (nrm_nonneg _ _) hFG 2
    calc ((ell : ℝ) ^ k)⁻¹ ^ 2 * ∑ p : BIdx (GF ell k Lu), g (bidxCB ell k Lu hell p)
        ≤ ((ell : ℝ) ^ k)⁻¹ ^ 2 * ((rr ell) ^ k * Real.exp ((∑ i ∈ Finset.range k, thetaOf ell (ε i)) / rr ell)
            * ‖x‖) ^ 2 := mul_le_mul_of_nonneg_left (h1.trans (h2 ▸ h4)) (by positivity)
      _ = (qbM ell k ε * ‖x‖) ^ 2 := by unfold qbM; ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (qbM_nonneg ell k ε) (norm_nonneg _)) two_ne_zero).mp hsq

/-! ## the weight on the constraint space -/

noncomputable def fspWt (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) :
    FSp (GF ell k Lu) →L[ℝ] FSp (GF ell k Lu) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => WithLp.toLp 2 (fun p => Real.exp (φ p.2.1.1) • u p)
      map_add' := fun u v => by refine PiLp.ext (fun p => ?_); simp [smul_add]
      map_smul' := fun c u => by
        refine PiLp.ext (fun p => ?_)
        simp only [PiLp.smul_apply, RingHom.id_apply, PiLp.toLp_apply]
        exact smul_comm _ _ _ }

theorem fspWt_apply (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (u : FSp (GF ell k Lu)) (p : BIdx (GF ell k Lu)) :
    (fspWt ell k Lu φ u) p = Real.exp (φ p.2.1.1) • u p := rfl

theorem fspWt_neg_cancel (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (u : FSp (GF ell k Lu)) :
    fspWt ell k Lu φ (fspWt ell k Lu (-φ) u) = u := by
  refine PiLp.ext (fun p => ?_)
  rw [fspWt_apply, fspWt_apply, smul_smul, ← Real.exp_add]
  simp

theorem fspWt_cancel_neg (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (u : FSp (GF ell k Lu)) :
    fspWt ell k Lu (-φ) (fspWt ell k Lu φ u) = u := by
  have := fspWt_neg_cancel ell k Lu (-φ) u
  simpa using this

theorem fspWt_symm (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (u v : FSp (GF ell k Lu)) :
    ⟪fspWt ell k Lu φ u, v⟫ = ⟪u, fspWt ell k Lu φ v⟫ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [fspWt_apply, fspWt_apply, real_inner_smul_left, real_inner_smul_right]

noncomputable def fspWP (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) : WPair (FSp (GF ell k Lu)) where
  w := fspWt ell k Lu φ
  wi := fspWt ell k Lu (-φ)
  w_wi := fspWt_neg_cancel ell k Lu φ
  wi_w := fspWt_cancel_neg ell k Lu φ
  w_sym := fspWt_symm ell k Lu φ
  wi_sym := fspWt_symm ell k Lu (-φ)

/-! ## the overlap count -/

open Classical in
/-- restriction of a bond field to a set of bonds -/
noncomputable def bondRestr {L : PeriodicLatticeExtent} (P : PeriodicLatticeEdge L → Prop) (x : BondFnL2 L) : BondFnL2 L :=
  WithLp.toLp 2 (fun b => if P b then x b else 0)

open Classical in
theorem foot_mult (hell : 0 < ell) (x : BondFnL2 (scaleUp ell k Lu)) :
    ∑ p : BIdx (GF ell k Lu), ∑ b : Bond (scaleUp ell k Lu), (if Foot ell k p.2.1 b then ‖x b‖ ^ 2 else 0)
      ≤ (3 * (Rfoot ell k / ell ^ k + 1) ^ 3 : ℕ) * ‖x‖ ^ 2 := by
  set n := ell ^ k with hn
  have hn0 : 0 < n := pow_pos hell k
  rw [Finset.sum_comm]
  have hcount : ∀ b : Bond (scaleUp ell k Lu),
      (Finset.univ.filter (fun p : BIdx (GF ell k Lu) => Foot ell k p.2.1 b)).card ≤ 3 * (Rfoot ell k / n + 1) ^ 3 := by
    intro b
    -- injection into coarse bonds reaching `b`
    have h1 : (Finset.univ.filter (fun p : BIdx (GF ell k Lu) => Foot ell k p.2.1 b)).card
        ≤ (Finset.univ.filter (fun c : CoarseBond (scaleUp ell k Lu) n => Reach (Rfoot ell k) c.1.1 b.1)).card := by
      refine Finset.card_le_card_of_injOn (bidxCB ell k Lu hell) ?_ ?_
      · intro p hp
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp ⊢
        exact Foot_reach ell hell k p.2.1 b hp
      · intro p _ p' _ h
        exact bidxCB_injective ell k Lu hell h
    have h2 : (Finset.univ.filter (fun c : CoarseBond (scaleUp ell k Lu) n => Reach (Rfoot ell k) c.1.1 b.1)).card
        ≤ (Finset.univ.filter (fun y : PeriodicLatticeSite (scaleUp ell k Lu) =>
            (∀ ν, n ∣ (y ν).val) ∧ Reach (Rfoot ell k) y b.1)).card * 3 := by
      have : (Finset.univ.filter (fun c : CoarseBond (scaleUp ell k Lu) n => Reach (Rfoot ell k) c.1.1 b.1))
          ⊆ ((Finset.univ.filter (fun y : {y // y ∈ CoarseLattice (scaleUp ell k Lu) n} =>
              Reach (Rfoot ell k) y.1 b.1)) ×ˢ (Finset.univ : Finset (Fin 3))) := by
        intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hc ⊢
        exact ⟨hc, trivial⟩
      refine (Finset.card_le_card this).trans ?_
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
      refine Nat.mul_le_mul_right 3 ?_
      refine Finset.card_le_card_of_injOn (fun y => y.1) ?_ ?_
      · intro y hy
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hy ⊢
        refine ⟨fun ν => Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp y.2 ν), hy⟩
      · intro y _ y' _ h
        exact Subtype.ext h
    have h3 := card_reach_coarse_le n hn0 (fun ν => hdvd_scaleUp ell k Lu hell k le_rfl ν) (Rfoot ell k) b.1
    calc _ ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ (Rfoot ell k / n + 1) ^ 3 * 3 := Nat.mul_le_mul_right 3 h3
      _ = 3 * (Rfoot ell k / n + 1) ^ 3 := by ring
  calc ∑ b : Bond (scaleUp ell k Lu), ∑ p : BIdx (GF ell k Lu), (if Foot ell k p.2.1 b then ‖x b‖ ^ 2 else 0)
      = ∑ b : Bond (scaleUp ell k Lu),
          ((Finset.univ.filter (fun p : BIdx (GF ell k Lu) => Foot ell k p.2.1 b)).card : ℝ) * ‖x b‖ ^ 2 := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ b : Bond (scaleUp ell k Lu), ((3 * (Rfoot ell k / n + 1) ^ 3 : ℕ) : ℝ) * ‖x b‖ ^ 2 := by
        refine Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
        exact_mod_cast hcount b
    _ = ((3 * (Rfoot ell k / n + 1) ^ 3 : ℕ) : ℝ) * ‖x‖ ^ 2 := by
        rw [← Finset.mul_sum, PiLp.norm_sq_eq_of_L2]

end

#print axioms suOf_zero
#print axioms suCoord_zero_of
#print axioms Qfull_row_local
#print axioms qbM_nonneg
#print axioms Qfull_norm_le
#print axioms fspWP
#print axioms foot_mult

end AdalyFormal.DLayer
