import MI25

/-!
# MI26 -- the TENT right inverse of the padded constraint map: rows and energy (M1 lane E, 2026-10-13)

Proper tower `G`, `ℓ^k ∣ L_μ + 1`, lane C's gauge hypotheses `hU` (in-block links `≤ ρ/ℓ^j`) and `hT` (tower links).
`extT u = Σ_{q=(j,y)} φ_q · (a_jℓ^j)^{−1/2} u_q + Σ_{x ∉ Ω₀} u_x δ_x` with `φ_q = phiB (ℓ^j) y` (the tent, mean one).
* `Qlev_flat_tent` : at `U = 1` the level-`j` composite of `φ c` on its block is `c`;
* `extT_row` : `‖(Q' extT u)_q − u_q‖ ≤ 12ρ ‖u_q‖` (row drift on a general field, MI24);
* **`extT_energy`** : `⟪extT u, LP_U extT u⟫ ≤ ((1 + 12ρ)² + (512ρ² + 4704)/a) ‖u‖²` — the constant is `k`-, `j`- and `L`-free
  (the block-constant extension of lane C has `β_q ∝ ℓ^{j}`).
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
open AdalyFormal.SiteCoercivity
open AdalyFormal.M1Site
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.QjComposite (Qcomposite)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.PoincareBridge (coarseLattice_fits)
open AdalyFormal.DLayer (boxF mem_boxF)

variable {L : PeriodicLatticeExtent}

open Classical in
/-- the tent extension. -/
noncomputable def extT (G : TowerGeom L) (ell : ℕ) (a : ℝ) (u : YP G) : SiteL2 L :=
  WithLp.toLp 2 (fun x => (∑ q : QIdx G, if x ∈ blockOf (yq q) (ell ^ jq q)
      then phiB (ell ^ jq q) (yq q) x • cq G a u q else 0)
    + (if hx : x ∈ G.Om0 then 0 else u (Sum.inr ⟨x, hx⟩)))

open Classical in
/-- the single tent field `φ c 1_B`. -/
noncomputable def tentF (y : PeriodicLatticeSite L) (n : ℕ) (c : SuTwo) : SiteL2 L :=
  WithLp.toLp 2 (fun x => if x ∈ blockOf y n then phiB n y x • c else 0)

section ext
variable {G : TowerGeom L} {ell k : ℕ} (hP : ProperTower G ell k) (a : ℝ)
include hP

theorem extT_on (u : YP G) (q : QIdx G) {x : PeriodicLatticeSite L} (hx : x ∈ blockOf (yq q) (ell ^ jq q)) :
    extT G ell a u x = phiB (ell ^ jq q) (yq q) x • cq G a u q := by
  classical
  have hO := block_Om0 hP q hx
  show (∑ q' : QIdx G, if x ∈ blockOf (yq q') (ell ^ jq q') then phiB (ell ^ jq q') (yq q') x • cq G a u q' else 0)
    + (if hx : x ∈ G.Om0 then 0 else u (Sum.inr ⟨x, hx⟩)) = _
  rw [dif_pos hO, add_zero, Finset.sum_eq_single q]
  · rw [if_pos hx]
  · intro q' _ hne
    rw [if_neg]
    intro hx'
    exact Finset.disjoint_left.mp (disj_q hP hne) hx' hx
  · intro h; exact absurd (Finset.mem_univ q) h

theorem extT_off (u : YP G) {x : PeriodicLatticeSite L} (hx : x ∉ G.Om0) :
    extT G ell a u x = u (Sum.inr ⟨x, hx⟩) := by
  classical
  show (∑ q' : QIdx G, if x ∈ blockOf (yq q') (ell ^ jq q') then phiB (ell ^ jq q') (yq q') x • cq G a u q' else 0)
    + (if hx : x ∈ G.Om0 then 0 else u (Sum.inr ⟨x, hx⟩)) = _
  rw [dif_neg hx, Finset.sum_eq_zero, zero_add]
  intro q' _
  rw [if_neg]
  intro hx'
  exact hx (block_Om0 hP q' hx')

theorem mask_extT_on (u : YP G) (q : QIdx G) {x : PeriodicLatticeSite L} (hx : x ∈ blockOf (yq q) (ell ^ jq q)) :
    siteMask G.Om0 (extT G ell a u) x = phiB (ell ^ jq q) (yq q) x • cq G a u q := by
  rw [siteMask_on _ _ _ (block_Om0 hP q hx), extT_on hP a u q hx]

theorem mask_extT_off (u : YP G) {x : PeriodicLatticeSite L}
    (hx : ∀ q : QIdx G, x ∉ blockOf (yq q) (ell ^ jq q)) :
    siteMask G.Om0 (extT G ell a u) x = 0 := by
  have hO : x ∉ G.Om0 := by
    intro h
    obtain ⟨q, hq⟩ := Om0_block hP h
    exact hx q hq
  exact siteMask_off _ _ _ hO

theorem QpP_extT_inr (U : Cfg L) (u : YP G) (x : OffIdx G) :
    QpP G U a (extT G ell a u) (Sum.inr x) = u (Sum.inr x) := by
  rw [QpP_inr, extT_off hP a u x.2]
  rfl

end ext

/-- the flat composite of a tent is its coefficient. -/
theorem Qlev_flat_tent (G : TowerGeom L) (hell : 0 < G.ell) (j : ℕ) (y : PeriodicLatticeSite L)
    (hy : y ∈ CoarseLattice L (G.ell ^ j)) (hfit : ∀ μ, (y μ).val + G.ell ^ j ≤ L μ + 1) (c : SuTwo) :
    Qlev G (trivialU L) j y (tentF y (G.ell ^ j) c) = c := by
  classical
  rw [Qlev_apply]
  have hbg : bgTower G (trivialU L) = fun _ => trivialU L := funext (fun i => AdalyFormal.PortSlice.bgTower_trivialU G i)
  rw [hbg, Qflat_eq_blockMean G.ell hell _ j y hy]
  have hn : 1 ≤ G.ell ^ j := Nat.one_le_pow _ _ hell
  have hs : ∑ x ∈ blockOf y (G.ell ^ j), (WithLp.ofLp (tentF y (G.ell ^ j) c)) x
      = ∑ x ∈ blockOf y (G.ell ^ j), phiB (G.ell ^ j) y x • c := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    show (if x ∈ blockOf y (G.ell ^ j) then phiB (G.ell ^ j) y x • c else 0) = _
    rw [if_pos hx]
  rw [hs, ← Finset.sum_smul, phiB_sum (G.ell ^ j) hn y hfit, smul_smul]
  have : (1 / (((G.ell ^ j : ℕ)) : ℝ) ^ 3) * (((G.ell ^ j : ℕ) : ℝ) ^ 3) = 1 := by
    have hpos : (0 : ℝ) < ((G.ell ^ j : ℕ) : ℝ) := by exact_mod_cast pow_pos hell j
    field_simp
  rw [this, one_smul]

/-- `Σ_x ‖φ c‖² ≤ 4 n³ ‖c‖²`. -/
theorem tentF_sq (n : ℕ) (hn : 1 ≤ n) (y : PeriodicLatticeSite L) (hfit : ∀ μ, (y μ).val + n ≤ L μ + 1) (c : SuTwo) :
    ∑ x, ‖tentF y n c x‖ ^ 2 ≤ 4 * (n : ℝ) ^ 3 * ‖c‖ ^ 2 := by
  classical
  have h1 : ∑ x, ‖tentF y n c x‖ ^ 2 = ∑ x ∈ blockOf y n, phiB n y x ^ 2 * ‖c‖ ^ 2 := by
    rw [← Finset.sum_subset (Finset.subset_univ (blockOf y n))]
    · refine Finset.sum_congr rfl (fun x hx => ?_)
      show ‖(if x ∈ blockOf y n then phiB n y x • c else 0)‖ ^ 2 = _
      rw [if_pos hx, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    · intro x _ hx
      show ‖(if x ∈ blockOf y n then phiB n y x • c else 0)‖ ^ 2 = 0
      rw [if_neg hx, norm_zero]; ring
  rw [h1]
  have h2 : ∀ x ∈ blockOf y n, phiB n y x ^ 2 * ‖c‖ ^ 2 ≤ 4 * phiB n y x * ‖c‖ ^ 2 := by
    intro x _
    have h0 := phiB_nonneg n hn y x
    have h4 := phiB_le n hn y x
    have : phiB n y x ^ 2 ≤ 4 * phiB n y x := by nlinarith
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  refine (Finset.sum_le_sum h2).trans (le_of_eq ?_)
  rw [← Finset.sum_mul, ← Finset.mul_sum, phiB_sum n hn y hfit]

/-! ## rows and energy -/

section final
variable {G : TowerGeom L} {ell k : ℕ} (hell : 2 ≤ ell) (hP : ProperTower G ell k) (hdvd : ∀ μ, ell ^ k ∣ L μ + 1)
  (U : Cfg L) (a : ℝ) (ha : 0 < a) (ρ : ℝ) (hρ : 0 ≤ ρ)
  (hU : ∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∀ b ∈ inBlockBonds y (ell ^ j),
      frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ / (ell : ℝ) ^ j)
  (hT : ∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∀ i, i < j → ∀ z ∈ blockOf y (ell ^ j), z ∈ CoarseLattice L (ell ^ i) → ∀ μ : Fin 3,
      coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ j) →
      frobNorm ((bgTower G U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j)

include hell hP hdvd ha hρ hT in
theorem extT_row (u : YP G) (q : QIdx G) :
    ‖QpP G U a (extT G ell a u) (Sum.inl q) - u (Sum.inl q)‖ ≤ 12 * ρ * ‖u (Sum.inl q)‖ := by
  classical
  have hell0 : 0 < ell := by omega
  set j := jq q; set y := yq q
  have hj : j ≤ k := by rw [← hP.k_eq]; exact jq_le q
  have hy : y ∈ G.Lam j := yq_mem q
  have hyc : y ∈ CoarseLattice L (ell ^ j) := hP.coarse j hj y hy
  have hdvdj : ∀ μ, ell ^ j ∣ L μ + 1 := fun μ => Dvd.dvd.trans (pow_dvd_pow ell hj) (hdvd μ)
  have hfit : ∀ μ, (y μ).val + ell ^ j ≤ L μ + 1 := coarseLattice_fits hdvdj hyc
  have hn : 1 ≤ ell ^ j := Nat.one_le_pow _ _ hell0
  set c := cq G a u q with hc
  set F := tentF y (ell ^ j) c with hF
  have hloc : Qlev G U j y (siteMask G.Om0 (extT G ell a u)) = Qlev G U j y F := by
    refine Qlev_congr_box G U j y _ _ (fun x hx => ?_)
    rw [hP.ell_eq, boxF_eq_blockOf] at hx
    rw [mask_extT_on hP a u q hx]
    show _ = (if x ∈ blockOf y (ell ^ j) then phiB (ell ^ j) y x • c else 0)
    rw [if_pos hx]
  have hflat : Qlev G (trivialU L) j y F = c := by
    have := Qlev_flat_tent G (by rw [hP.ell_eq]; exact hell0) j y (by rw [hP.ell_eq]; exact hyc)
      (by rw [hP.ell_eq]; exact hfit) c
    rw [hP.ell_eq] at this; exact this
  set δ : ℕ → ℝ := fun i => ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j with hδ
  have hδ0 : ∀ i, 0 ≤ δ i := fun i => by
    show 0 ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j
    have : (0 : ℝ) < (ell : ℝ) ^ j := by positivity
    positivity
  have hdr := row_drift_gen G U ell hP.ell_eq hell0 j y hyc hdvdj δ hδ0
    (fun i hi z hz hzal μ hzs => hT j hj y hy i hi z hz hzal μ hzs) F
  rw [hflat] at hdr
  have hE : ∑ i ∈ Finset.range j, 6 * ((ell : ℝ) - 1) * δ i ≤ 6 * ρ := geom_tower_sum ell j hell ρ hρ
  have hE0 : 0 ≤ ∑ i ∈ Finset.range j, 6 * ((ell : ℝ) - 1) * δ i := Finset.sum_nonneg (fun i _ => by
    have hℓ1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell0
    have : (0 : ℝ) ≤ (ell : ℝ) - 1 := by linarith
    have := hδ0 i; positivity)
  have hsq := tentF_sq (ell ^ j) hn y hfit c
  have hn3 : (0 : ℝ) < ((ell ^ j : ℕ) : ℝ) ^ 3 := by have := pow_pos hell0 j; positivity
  have hd2 : ‖Qlev G U j y F - c‖ ^ 2 ≤ (2 * (6 * ρ) * ‖c‖) ^ 2 := by
    refine hdr.trans ?_
    have h1 : (1 / ((ell ^ j : ℕ) : ℝ) ^ 3) * ∑ x, ‖F x‖ ^ 2 ≤ 4 * ‖c‖ ^ 2 := by
      rw [one_div, inv_mul_le_iff₀ hn3]; linarith
    have h2 : (∑ i ∈ Finset.range j, 6 * ((ell : ℝ) - 1) * δ i) ^ 2 ≤ (6 * ρ) ^ 2 := pow_le_pow_left₀ hE0 hE 2
    calc (∑ i ∈ Finset.range j, 6 * ((ell : ℝ) - 1) * δ i) ^ 2 * ((1 / ((ell ^ j : ℕ) : ℝ) ^ 3) * ∑ x, ‖F x‖ ^ 2)
        ≤ (6 * ρ) ^ 2 * (4 * ‖c‖ ^ 2) := mul_le_mul h2 h1 (by positivity) (by positivity)
      _ = (2 * (6 * ρ) * ‖c‖) ^ 2 := by ring
  have h1 : ‖Qlev G U j y F - c‖ ≤ 12 * ρ * ‖c‖ := by
    have := (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hd2
    linarith
  have hwpos := wq_pos hell hP a j ha
  have hsqw : 0 < Real.sqrt (wq G a j) := Real.sqrt_pos.mpr hwpos
  have hu_eq : u (Sum.inl q) = Real.sqrt (wq G a j) • c := by
    rw [hc, cq, smul_smul, mul_inv_cancel₀ hsqw.ne', one_smul]
  rw [QpP_inl]
  show ‖Real.sqrt (wq G a j) • Qlev G U j y (siteMask G.Om0 (extT G ell a u)) - u (Sum.inl q)‖ ≤ _
  rw [hloc, hu_eq, ← smul_sub, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hsqw]
  have := mul_le_mul_of_nonneg_left h1 hsqw.le
  linarith

include hell hP hdvd ha hρ hU hT in
/-- **energy of the tent extension**. -/
theorem extT_energy (u : YP G) :
    ⟪extT G ell a u, LP G U a (extT G ell a u)⟫ ≤ ((1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a) * ‖u‖ ^ 2 := by
  classical
  have hell0 : 0 < ell := by omega
  have hw : ∀ j, 0 ≤ wq G a j := fun j => (wq_pos hell hP a j ha).le
  set g := extT G ell a u with hg
  rw [inner_LP G U a hw, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  set K := (512 * ρ ^ 2 + 4704) / a with hK
  have hK0 : 0 ≤ K := by positivity
  -- the constraint part
  have hQ : ‖QpP G U a g‖ ^ 2 ≤ ∑ q : QIdx G, (1 + 12 * ρ) ^ 2 * ‖u (Sum.inl q)‖ ^ 2
      + ∑ x : OffIdx G, ‖u (Sum.inr x)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]
    refine add_le_add (Finset.sum_le_sum (fun q _ => ?_)) (le_of_eq (Finset.sum_congr rfl (fun x _ => ?_)))
    · have h1 := extT_row hell hP hdvd U a ha ρ hρ hT u q
      have h2 : ‖QpP G U a g (Sum.inl q)‖ ≤ (1 + 12 * ρ) * ‖u (Sum.inl q)‖ := by
        have h3 := norm_add_le (QpP G U a g (Sum.inl q) - u (Sum.inl q)) (u (Sum.inl q))
        rw [sub_add_cancel] at h3
        linarith
      have := pow_le_pow_left₀ (norm_nonneg _) h2 2
      rw [mul_pow] at this; exact this
    · rw [QpP_extT_inr hP a U u x]
  -- the gradient part
  have hD : ‖Dm G U g‖ ^ 2 ≤ ∑ q : QIdx G,
      (3 * (((ell ^ jq q : ℕ) : ℝ)) ^ 3 * (8 * 4 ^ 2 * (ρ / (ell : ℝ) ^ jq q) ^ 2 + 2 * (14 / ((ell ^ jq q : ℕ) : ℝ)) ^ 2)
        + 12 * (((ell ^ jq q : ℕ) : ℝ) * ((ell ^ jq q : ℕ) : ℝ)) * (14 / ((ell ^ jq q : ℕ) : ℝ)) ^ 2) * ‖cq G a u q‖ ^ 2 := by
    have hn : ∀ q : QIdx G, 1 ≤ ell ^ jq q := fun q => Nat.one_le_pow _ _ hell0
    exact grad_tent_le U (fun q : QIdx G => yq q) (fun q => ell ^ jq q) (fun q => fit_q hP hdvd hell0 q)
      (fun q q' hne => disj_q hP hne) (cq G a u) (fun q => phiB (ell ^ jq q) (yq q)) (siteMask G.Om0 g)
      (fun q x hx => mask_extT_on hP a u q hx) (fun x hx => mask_extT_off hP a u hx)
      (fun _ => 4) (fun q => 14 / ((ell ^ jq q : ℕ) : ℝ)) (fun q => 14 / ((ell ^ jq q : ℕ) : ℝ))
      (fun q x => phiB_nonneg _ (hn q) _ x) (fun q x => phiB_le _ (hn q) _ x)
      (fun q b hb => by
        have hb' := mem_inBlockBonds.mp hb
        exact phiB_step _ (hn q) (fit_q hP hdvd hell0 q) hb'.1 b.2 hb'.2)
      (fun q x μ hx hout => phiB_out _ (hn q) (fit_q hP hdvd hell0 q) hx μ hout)
      (fun q x μ hin hx => phiB_in _ (hn q) μ hin hx)
      (fun q => ρ / (ell : ℝ) ^ jq q) (fun q => by
        have : (0:ℝ) < (ell:ℝ) ^ jq q := pow_pos (by exact_mod_cast hell0) _
        exact div_nonneg hρ this.le)
      (fun q b hb => hU (jq q) (by rw [← hP.k_eq]; exact jq_le q) (yq q) (yq_mem q) b hb)
  have hDq : ∀ q : QIdx G,
      (3 * (((ell ^ jq q : ℕ) : ℝ)) ^ 3 * (8 * 4 ^ 2 * (ρ / (ell : ℝ) ^ jq q) ^ 2 + 2 * (14 / ((ell ^ jq q : ℕ) : ℝ)) ^ 2)
        + 12 * (((ell ^ jq q : ℕ) : ℝ) * ((ell ^ jq q : ℕ) : ℝ)) * (14 / ((ell ^ jq q : ℕ) : ℝ)) ^ 2) * ‖cq G a u q‖ ^ 2
      ≤ K * ‖u (Sum.inl q)‖ ^ 2 := by
    intro q
    set n : ℝ := (ell : ℝ) ^ jq q with hn
    have hnc : (((ell ^ jq q : ℕ) : ℝ)) = n := by push_cast; rfl
    rw [hnc]
    have hn1 : 1 ≤ n := one_le_pow₀ (by exact_mod_cast (show 1 ≤ ell by omega))
    have hnpos : 0 < n := by linarith
    have hwpos := wq_pos hell hP a (jq q) ha
    have hc2 : ‖cq G a u q‖ ^ 2 = ‖u (Sum.inl q)‖ ^ 2 / wq G a (jq q) := by
      rw [cq, norm_smul, mul_pow, Real.norm_eq_abs, abs_inv, abs_of_pos (Real.sqrt_pos.mpr hwpos), inv_pow,
        Real.sq_sqrt hwpos.le]
      field_simp
    have hwdef : wq G a (jq q) = ajSeq a ell (jq q) * n := by rw [wq, hP.ell_eq]
    have hak := ajSeq_ge ell (jq q) hell ha
    have hajpos : 0 < ajSeq a ell (jq q) := by linarith
    rw [hc2, hwdef]
    have e : (3 * n ^ 3 * (8 * 4 ^ 2 * (ρ / n) ^ 2 + 2 * (14 / n) ^ 2) + 12 * (n * n) * (14 / n) ^ 2)
        * (‖u (Sum.inl q)‖ ^ 2 / (ajSeq a ell (jq q) * n))
        = (384 * ρ ^ 2 + 1176 + 2352 / n) / ajSeq a ell (jq q) * ‖u (Sum.inl q)‖ ^ 2 := by
      field_simp; ring
    rw [e]
    have hu2 : 0 ≤ ‖u (Sum.inl q)‖ ^ 2 := sq_nonneg _
    have hinv : 2352 / n ≤ 2352 := by rw [div_le_iff₀ hnpos]; nlinarith
    have h1 : (384 * ρ ^ 2 + 1176 + 2352 / n) / ajSeq a ell (jq q) ≤ K := by
      rw [hK, div_le_div_iff₀ hajpos ha]
      have hnum : 0 ≤ 384 * ρ ^ 2 + 1176 + 2352 / n := by positivity
      nlinarith
    exact mul_le_mul_of_nonneg_right h1 hu2
  have hD' : ‖Dm G U g‖ ^ 2 ≤ ∑ q : QIdx G, K * ‖u (Sum.inl q)‖ ^ 2 :=
    hD.trans (Finset.sum_le_sum (fun q _ => hDq q))
  have hun : ‖u‖ ^ 2 = ∑ q : QIdx G, ‖u (Sum.inl q)‖ ^ 2 + ∑ x : OffIdx G, ‖u (Sum.inr x)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]
  have hs1 : 0 ≤ ∑ q : QIdx G, ‖u (Sum.inl q)‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs2 : 0 ≤ ∑ x : OffIdx G, ‖u (Sum.inr x)‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [← Finset.mul_sum] at hD'
  rw [← Finset.mul_sum] at hQ
  have h12 : 1 ≤ (1 + 12 * ρ) ^ 2 := by nlinarith
  rw [hun]
  nlinarith [mul_nonneg hK0 hs2, mul_le_mul_of_nonneg_right h12 hs2]

end final

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.extT_on
#print axioms AdalyFormal.M1IMS.extT_off
#print axioms AdalyFormal.M1IMS.mask_extT_on
#print axioms AdalyFormal.M1IMS.mask_extT_off
#print axioms AdalyFormal.M1IMS.QpP_extT_inr
#print axioms AdalyFormal.M1IMS.Qlev_flat_tent
#print axioms AdalyFormal.M1IMS.tentF_sq
#print axioms AdalyFormal.M1IMS.extT_row
#print axioms AdalyFormal.M1IMS.extT_energy
#print axioms AdalyFormal.M1IMS.extT
#print axioms AdalyFormal.M1IMS.tentF
