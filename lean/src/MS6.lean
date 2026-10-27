import MS5

/-!
# MS6 -- S3 part 3: `extStrat` (block-local stratified right inverse) and **`gamma_lower_strat`**

Proper tower `G` (`ProperTower G ℓ k`, `ℓ^k ∣ L_μ + 1`).  For a row vector `u ∈ YP G`:
`extF u = Σ_{q=(j,y)} (a_jℓ^j)^{−1/2} u_q · 1_{B(y,ℓ^j)} + Σ_{x ∉ Ω₀} u_x δ_x` (block-constant on each constraint block, the
padding rows copied off `Ω₀`).
* `extF_row_flat` : at `U = 1` the map is an EXACT right inverse of the padded `QpP` (flat composite = block mean, `|B| = ℓ^{3j}`).
* `row_drift` : at general `U` with the stratum tower class on the block, `‖Q'_j(U)(c 1_B)(y) − c‖ ≤ 6ρ ‖c‖` (local telescoping
  PSiteC13 along the chain of the single row `{y}`).
* `extF_energy` : `⟪extF u, LP_U extF u⟫ ≤ Σ_q β_q ‖u_q‖² + Σ_x ‖u_x‖²`, `β_q = (1 + 6ρ)² + 16(ρ² + ℓ^{j_q})/a` (block-constant
  gradient energy MS5 + in-block links `ρ/ℓ^j` + the row drift).
* **`gamma_lower_strat`** : `(1 − 6ρ)² Σ_p ‖v_p‖²/β_p ≤ (12 + a) ‖X v‖²` for every `v ∈ YP G` (`β = 1` on padding rows), i.e.
  `Γ = X*X ≥ ((1−6ρ)²/(12+a)) · diag(β⁻¹)`: the row scale is `ℓ^{-j}` per stratum, not `ℓ^{-k}`.
* `isUnit_LP_strat` (from S1, `216ρ² < 1`) and `exists_Gami_strat` (`216ρ² < 1`) : `Γ` has a two-sided inverse.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1Site

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.QjComposite (Qcomposite)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.PoincareBridge (coarseLattice_fits)
open AdalyFormal.DLayer (boxF mem_boxF)

variable {L : PeriodicLatticeExtent}

/-! ## 0. blocks of the rows -/

/-- the level of a row -/
def jq {G : TowerGeom L} (q : QIdx G) : ℕ := q.1.1.val
/-- the base point of a row -/
def yq {G : TowerGeom L} (q : QIdx G) : PeriodicLatticeSite L := q.1.2

theorem jq_le {G : TowerGeom L} (q : QIdx G) : jq q ≤ G.k := Nat.lt_succ_iff.mp q.1.1.isLt
theorem yq_mem {G : TowerGeom L} (q : QIdx G) : yq q ∈ G.Lam (jq q) := q.2

theorem card_blockOf (y : PeriodicLatticeSite L) (n : ℕ) (hfit : ∀ μ, (y μ).val + n ≤ L μ + 1) :
    (blockOf y n).card = n ^ 3 := by
  classical
  refine le_antisymm ?_ ?_
  · rw [← boxF_eq_blockOf]; exact AdalyFormal.DLayer.card_boxF_le y n
  · set e : (Fin 3 → Fin n) → PeriodicLatticeSite L := fun t μ =>
      ⟨(y μ).val + (t μ).val, by have := (t μ).isLt; have := hfit μ; omega⟩ with he
    have h := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin 3 → Fin n))) (t := blockOf y n) e
      (by
        intro t _
        rw [Finset.mem_coe, mem_blockOf]
        intro μ
        simp only [he]
        exact ⟨Nat.le_add_right _ _, by have := (t μ).isLt; omega⟩)
      (by
        intro t _ t' _ h
        funext μ
        have := congrFun h μ
        simp only [he, Fin.mk.injEq] at this
        exact Fin.ext (by omega))
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
    exact h

section geom
variable {G : TowerGeom L} {ell k : ℕ} (hP : ProperTower G ell k) (hdvd : ∀ μ, ell ^ k ∣ L μ + 1)
include hP

include hdvd in
theorem fit_q (hell0 : 0 < ell) (q : QIdx G) : ∀ μ, (yq q μ).val + ell ^ jq q ≤ L μ + 1 := by
  have hj : jq q ≤ k := by rw [← hP.k_eq]; exact jq_le q
  have hdvdj : ∀ μ, ell ^ jq q ∣ L μ + 1 := fun μ => Dvd.dvd.trans (pow_dvd_pow ell hj) (hdvd μ)
  exact coarseLattice_fits hdvdj (hP.coarse _ hj _ (yq_mem q))

theorem disj_q {q q' : QIdx G} (hne : q ≠ q') :
    Disjoint (blockOf (yq q) (ell ^ jq q)) (blockOf (yq q') (ell ^ jq q')) := by
  have hj : jq q ≤ k := by rw [← hP.k_eq]; exact jq_le q
  have hj' : jq q' ≤ k := by rw [← hP.k_eq]; exact jq_le q'
  refine hP.disj _ _ hj hj' _ (yq_mem q) _ (yq_mem q') ?_
  by_contra hcon
  push Not at hcon
  apply hne
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.ext hcon.1
  · exact hcon.2

theorem block_Om0 (q : QIdx G) {x : PeriodicLatticeSite L} (hx : x ∈ blockOf (yq q) (ell ^ jq q)) : x ∈ G.Om0 := by
  rw [hP.cover]
  exact ⟨jq q, by rw [← hP.k_eq]; exact jq_le q, yq q, yq_mem q, hx⟩

theorem Om0_block {x : PeriodicLatticeSite L} (hx : x ∈ G.Om0) : ∃ q : QIdx G, x ∈ blockOf (yq q) (ell ^ jq q) := by
  rw [hP.cover] at hx
  obtain ⟨j, hj, y, hy, hxy⟩ := hx
  refine ⟨⟨(⟨j, by rw [hP.k_eq]; omega⟩, y), hy⟩, hxy⟩

end geom

/-! ## 1. the extension -/

noncomputable def cq (G : TowerGeom L) (a : ℝ) (u : YP G) (q : QIdx G) : SuTwo :=
  (Real.sqrt (wq G a (jq q)))⁻¹ • u (Sum.inl q)

open Classical in
noncomputable def extF (G : TowerGeom L) (ell : ℕ) (a : ℝ) (u : YP G) : SiteL2 L :=
  WithLp.toLp 2 (fun x => (∑ q : QIdx G, if x ∈ blockOf (yq q) (ell ^ jq q) then cq G a u q else 0)
    + (if hx : x ∈ G.Om0 then 0 else u (Sum.inr ⟨x, hx⟩)))

open Classical in
/-- the block-constant field `c 1_{B}` -/
noncomputable def bcF (B : Finset (PeriodicLatticeSite L)) (c : SuTwo) : SiteL2 L :=
  WithLp.toLp 2 (fun x => if x ∈ B then c else 0)

section ext
variable {G : TowerGeom L} {ell k : ℕ} (hP : ProperTower G ell k) (a : ℝ)
include hP

theorem extF_on (u : YP G) (q : QIdx G) {x : PeriodicLatticeSite L} (hx : x ∈ blockOf (yq q) (ell ^ jq q)) :
    extF G ell a u x = cq G a u q := by
  classical
  have hO := block_Om0 hP q hx
  show (∑ q' : QIdx G, if x ∈ blockOf (yq q') (ell ^ jq q') then cq G a u q' else 0)
    + (if hx : x ∈ G.Om0 then 0 else u (Sum.inr ⟨x, hx⟩)) = _
  rw [dif_pos hO, add_zero, Finset.sum_eq_single q]
  · rw [if_pos hx]
  · intro q' _ hne
    rw [if_neg]
    intro hx'
    exact Finset.disjoint_left.mp (disj_q hP hne) hx' hx
  · intro h; exact absurd (Finset.mem_univ q) h

theorem extF_off (u : YP G) {x : PeriodicLatticeSite L} (hx : x ∉ G.Om0) :
    extF G ell a u x = u (Sum.inr ⟨x, hx⟩) := by
  classical
  show (∑ q' : QIdx G, if x ∈ blockOf (yq q') (ell ^ jq q') then cq G a u q' else 0)
    + (if hx : x ∈ G.Om0 then 0 else u (Sum.inr ⟨x, hx⟩)) = _
  rw [dif_neg hx, Finset.sum_eq_zero, zero_add]
  intro q' _
  rw [if_neg]
  intro hx'
  exact hx (block_Om0 hP q' hx')

theorem mask_extF_on (u : YP G) (q : QIdx G) {x : PeriodicLatticeSite L} (hx : x ∈ blockOf (yq q) (ell ^ jq q)) :
    siteMask G.Om0 (extF G ell a u) x = cq G a u q := by
  rw [siteMask_on _ _ _ (block_Om0 hP q hx), extF_on hP a u q hx]

theorem mask_extF_off (u : YP G) {x : PeriodicLatticeSite L}
    (hx : ∀ q : QIdx G, x ∉ blockOf (yq q) (ell ^ jq q)) :
    siteMask G.Om0 (extF G ell a u) x = 0 := by
  have hO : x ∉ G.Om0 := by
    intro h
    obtain ⟨q, hq⟩ := Om0_block hP h
    exact hx q hq
  exact siteMask_off _ _ _ hO

theorem QpP_extF_inr (U : Cfg L) (u : YP G) (x : OffIdx G) :
    QpP G U a (extF G ell a u) (Sum.inr x) = u (Sum.inr x) := by
  rw [QpP_inr, extF_off hP a u x.2]
  rfl

end ext

/-! ## 2. rows: locality, flat value, drift -/

theorem Qlev_congr_box (G : TowerGeom L) (U : Cfg L) (j : ℕ) (y : PeriodicLatticeSite L) (f f' : SiteL2 L)
    (h : ∀ x ∈ boxF y (G.ell ^ j), f x = f' x) : Qlev G U j y f = Qlev G U j y f' := by
  rw [← sub_eq_zero, ← map_sub, Qlev_apply]
  have hb := AdalyFormal.DLayer.Qcomposite_norm_le (bgTower G U) G.ell j (WithLp.ofLp (f - f')) y
  have hz : ∑ x ∈ boxF y (G.ell ^ j), ‖(WithLp.ofLp (f - f')) x‖ = 0 := by
    refine Finset.sum_eq_zero (fun x hx => ?_)
    show ‖(f - f') x‖ = 0
    rw [PiLp.sub_apply, h x hx, sub_self, norm_zero]
  rw [hz, mul_zero] at hb
  exact norm_le_zero_iff.mp hb

theorem Qlev_flat_bc (G : TowerGeom L) (hell : 0 < G.ell) (j : ℕ) (y : PeriodicLatticeSite L)
    (hy : y ∈ CoarseLattice L (G.ell ^ j)) (hfit : ∀ μ, (y μ).val + G.ell ^ j ≤ L μ + 1) (c : SuTwo) :
    Qlev G (trivialU L) j y (bcF (blockOf y (G.ell ^ j)) c) = c := by
  classical
  rw [Qlev_apply]
  have hbg : bgTower G (trivialU L) = fun _ => trivialU L := funext (fun i => AdalyFormal.PortSlice.bgTower_trivialU G i)
  rw [hbg, Qflat_eq_blockMean G.ell hell _ j y hy]
  have hs : ∑ x ∈ blockOf y (G.ell ^ j), (WithLp.ofLp (bcF (blockOf y (G.ell ^ j)) c)) x
      = ∑ x ∈ blockOf y (G.ell ^ j), c := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    show (if x ∈ blockOf y (G.ell ^ j) then c else 0) = c
    rw [if_pos hx]
  rw [hs, Finset.sum_const, card_blockOf y _ hfit, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have : (1 / (((G.ell ^ j : ℕ)) : ℝ) ^ 3) * (((G.ell ^ j) ^ 3 : ℕ) : ℝ) = 1 := by
    have hpos : (0 : ℝ) < ((G.ell ^ j : ℕ) : ℝ) := by exact_mod_cast pow_pos hell j
    push_cast
    field_simp
  rw [this, one_smul]

/-- **row drift**: the level-`j` composite of a constant on its own block moves by at most `E ‖c‖`. -/
theorem row_drift (G : TowerGeom L) (U : Cfg L) (ell : ℕ) (hellG : G.ell = ell) (hell : 0 < ell) (j : ℕ)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L (ell ^ j)) (hdvdj : ∀ μ, ell ^ j ∣ L μ + 1)
    (δ : ℕ → ℝ) (hδ0 : ∀ i, 0 ≤ δ i)
    (hT : ∀ i, i < j → ∀ z ∈ blockOf y (ell ^ j), z ∈ CoarseLattice L (ell ^ i) → ∀ μ : Fin 3,
      coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ j) →
      frobNorm ((bgTower G U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ δ i)
    (c : SuTwo) :
    ‖Qlev G U j y (bcF (blockOf y (ell ^ j)) c) - Qlev G (trivialU L) j y (bcF (blockOf y (ell ^ j)) c)‖
      ≤ (∑ i ∈ Finset.range j, 6 * ((ell : ℝ) - 1) * δ i) * ‖c‖ := by
  classical
  set f : PeriodicLatticeSite L → SuTwo := WithLp.ofLp (bcF (blockOf y (ell ^ j)) c) with hf
  set Λ : Finset (PeriodicLatticeSite L) := {y} with hΛ
  have hLY : Λ ⊆ CoarseLattice L (ell ^ j) := by intro z hz; rw [Finset.mem_singleton.mp hz]; exact hy
  have hZc := chainZ_sub ell j Λ hLY
  have hchain := chainZ_step ell j Λ hLY
  have htel := NsZ_telescope_local_al ell hell (bgTower G U) δ hδ0 j (chainZ ell j Λ)
    (fun i hi ν => Dvd.dvd.trans (pow_dvd_pow ell (by omega : i ≤ j)) (hdvdj ν))
    (fun i hi => hZc i hi) (fun i hi => hchain i hi)
    (by
      intro i hi y' hy' μ
      have hy'' := hZc (i + 1) (by omega) hy'
      have hdv : ∀ ν, ell ^ (i + 1) ∣ L ν + 1 := fun ν =>
        Dvd.dvd.trans (pow_dvd_pow ell (by omega : i + 1 ≤ j)) (hdvdj ν)
      have := coarseLattice_fits hdv hy'' μ
      rwa [pow_succ] at this)
    (by
      intro i hi y' hy' z hz hzal μ hzs
      obtain ⟨y0, hy0, hsub⟩ := chainZ_block_single ell hell j Λ hLY (i + 1) (by omega) y' hy'
      rw [Finset.mem_singleton.mp hy0] at hsub
      have hz' : z ∈ blockOf y' (ell ^ (i + 1)) := by rwa [pow_succ]
      have hzs' : coarseShift z (ell ^ i) μ ∈ blockOf y' (ell ^ (i + 1)) := by rwa [pow_succ]
      exact hT i hi z (hsub hz') hzal μ (hsub hzs'))
    f j le_rfl
  rw [chainZ_top] at htel
  set E := ∑ i ∈ Finset.range j, 6 * ((ell : ℝ) - 1) * δ i with hE
  have hE0 : 0 ≤ E := Finset.sum_nonneg (fun i _ => by
    have hℓ1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
    have : (0 : ℝ) ≤ (ell : ℝ) - 1 := by linarith
    have := hδ0 i; positivity)
  -- left side: NsZ over {y}
  have hbg : bgTower G (trivialU L) = fun _ => trivialU L := funext (fun i => AdalyFormal.PortSlice.bgTower_trivialU G i)
  set d := Qlev G U j y (bcF (blockOf y (ell ^ j)) c) - Qlev G (trivialU L) j y (bcF (blockOf y (ell ^ j)) c) with hd
  have hdQ : (Qcomposite (bgTower G U) ell j f - Qcomposite (fun _ => trivialU L) ell j f) y = d := by
    rw [hd, Qlev_apply, Qlev_apply, hbg, hellG]; rfl
  have hL : NsZ (ell ^ j) Λ (Qcomposite (bgTower G U) ell j f - Qcomposite (fun _ => trivialU L) ell j f) ^ 2
      = ((ell ^ j : ℕ) : ℝ) ^ 3 * ‖d‖ ^ 2 := by
    rw [NsZ_sq, hΛ, Finset.sum_singleton, hdQ]
  -- right side
  have hR : NsZ 1 (chainZ ell j Λ 0) f ^ 2 ≤ ((ell ^ j : ℕ) : ℝ) ^ 3 * ‖c‖ ^ 2 := by
    rw [NsZ_sq]
    have h1 : ∑ x ∈ chainZ ell j Λ 0, ‖f x‖ ^ 2 ≤ ∑ x, ‖f x‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => sq_nonneg _)
    have h2 : ∑ x, ‖f x‖ ^ 2 = ∑ x ∈ blockOf y (ell ^ j), ‖c‖ ^ 2 := by
      rw [← Finset.sum_subset (Finset.subset_univ (blockOf y (ell ^ j)))]
      · refine Finset.sum_congr rfl (fun x hx => ?_)
        show ‖(if x ∈ blockOf y (ell ^ j) then c else 0)‖ ^ 2 = _
        rw [if_pos hx]
      · intro x _ hx
        show ‖(if x ∈ blockOf y (ell ^ j) then c else 0)‖ ^ 2 = 0
        rw [if_neg hx, norm_zero]; ring
    have hfit := coarseLattice_fits hdvdj hy
    rw [h2, Finset.sum_const, card_blockOf y _ hfit, nsmul_eq_mul] at h1
    push_cast at h1 ⊢
    simpa using h1
  have hN0 := NsZ_nonneg (ell ^ j) Λ (Qcomposite (bgTower G U) ell j f - Qcomposite (fun _ => trivialU L) ell j f)
  have hsq := pow_le_pow_left₀ hN0 htel 2
  rw [hL, mul_pow] at hsq
  have hn3 : (0 : ℝ) < ((ell ^ j : ℕ) : ℝ) ^ 3 := by have := pow_pos hell j; positivity
  have h3 : ((ell ^ j : ℕ) : ℝ) ^ 3 * ‖d‖ ^ 2 ≤ ((ell ^ j : ℕ) : ℝ) ^ 3 * (E ^ 2 * ‖c‖ ^ 2) := by
    have := mul_le_mul_of_nonneg_left hR (sq_nonneg E)
    nlinarith [this, hsq]
  have h4 : ‖d‖ ^ 2 ≤ (E * ‖c‖) ^ 2 := by
    rw [mul_pow]; exact le_of_mul_le_mul_left h3 hn3
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hE0 (norm_nonneg _)) two_ne_zero).mp h4

/-! ## 3. rows of the extension, energy, and the Γ lower bound -/

section final
variable {G : TowerGeom L} {ell k : ℕ} (hell : 2 ≤ ell) (hP : ProperTower G ell k) (hdvd : ∀ μ, ell ^ k ∣ L μ + 1)
  (U : Cfg L) (a : ℝ) (ha : 0 < a) (ρ : ℝ) (hρ : 0 ≤ ρ)
  (hU : ∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∀ b ∈ inBlockBonds y (ell ^ j),
      frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ / (ell : ℝ) ^ j)
  (hT : ∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∀ i, i < j → ∀ z ∈ blockOf y (ell ^ j), z ∈ CoarseLattice L (ell ^ i) → ∀ μ : Fin 3,
      coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ j) →
      frobNorm ((bgTower G U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j)

include hell hP in
theorem wq_pos (j : ℕ) (ha : 0 < a) : 0 < wq G a j := by
  unfold wq
  have := ajSeq_ge G.ell j (by rw [hP.ell_eq]; exact hell) ha
  have h0 : 0 < ajSeq a G.ell j := by linarith
  have h1 : (0 : ℝ) < (G.ell : ℝ) ^ j := by
    rw [hP.ell_eq]; have : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
    exact pow_pos this j
  exact mul_pos h0 h1

include hell hP hdvd ha hρ hT in
theorem extF_row (u : YP G) (q : QIdx G) :
    ‖QpP G U a (extF G ell a u) (Sum.inl q) - u (Sum.inl q)‖ ≤ 6 * ρ * ‖u (Sum.inl q)‖ := by
  classical
  have hell0 : 0 < ell := by omega
  set j := jq q; set y := yq q
  have hj : j ≤ k := by rw [← hP.k_eq]; exact jq_le q
  have hy : y ∈ G.Lam j := yq_mem q
  have hyc : y ∈ CoarseLattice L (ell ^ j) := hP.coarse j hj y hy
  have hdvdj : ∀ μ, ell ^ j ∣ L μ + 1 := fun μ => Dvd.dvd.trans (pow_dvd_pow ell hj) (hdvd μ)
  have hfit : ∀ μ, (y μ).val + ell ^ j ≤ L μ + 1 := coarseLattice_fits hdvdj hyc
  set c := cq G a u q with hc
  set B := blockOf y (ell ^ j) with hB
  have hloc : Qlev G U j y (siteMask G.Om0 (extF G ell a u)) = Qlev G U j y (bcF B c) := by
    refine Qlev_congr_box G U j y _ _ (fun x hx => ?_)
    rw [hP.ell_eq, boxF_eq_blockOf] at hx
    rw [mask_extF_on hP a u q hx]
    show c = (if x ∈ B then c else 0)
    rw [if_pos hx]
  have hflat : Qlev G (trivialU L) j y (bcF B c) = c := by
    have := Qlev_flat_bc G (by rw [hP.ell_eq]; exact hell0) j y (by rw [hP.ell_eq]; exact hyc)
      (by rw [hP.ell_eq]; exact hfit) c
    rw [hP.ell_eq] at this; exact this
  set δ : ℕ → ℝ := fun i => ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j with hδ
  have hδ0 : ∀ i, 0 ≤ δ i := fun i => by
    show 0 ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j
    have : (0 : ℝ) < (ell : ℝ) ^ j := by positivity
    positivity
  have hdr := row_drift G U ell hP.ell_eq hell0 j y hyc hdvdj δ hδ0
    (fun i hi z hz hzal μ hzs => hT j hj y hy i hi z hz hzal μ hzs) c
  rw [← hB, hflat] at hdr
  have hE : ∑ i ∈ Finset.range j, 6 * ((ell : ℝ) - 1) * δ i ≤ 6 * ρ := geom_tower_sum ell j hell ρ hρ
  have hwpos := wq_pos hell hP a j ha
  have hsq : 0 < Real.sqrt (wq G a j) := Real.sqrt_pos.mpr hwpos
  have hu_eq : u (Sum.inl q) = Real.sqrt (wq G a j) • c := by
    rw [hc, cq, smul_smul, mul_inv_cancel₀ hsq.ne', one_smul]
  rw [QpP_inl]
  show ‖Real.sqrt (wq G a j) • Qlev G U j y (siteMask G.Om0 (extF G ell a u)) - u (Sum.inl q)‖ ≤ _
  rw [hloc, hu_eq, ← smul_sub, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hsq]
  have h1 : ‖Qlev G U j y (bcF B c) - c‖ ≤ 6 * ρ * ‖c‖ :=
    hdr.trans (mul_le_mul_of_nonneg_right hE (norm_nonneg _))
  have := mul_le_mul_of_nonneg_left h1 hsq.le
  linarith

/-- the row weights of the stratified extension -/
noncomputable def betaS (G : TowerGeom L) (ell : ℕ) (a ρ : ℝ) : PIdx G → ℝ :=
  Sum.elim (fun q => (1 + 6 * ρ) ^ 2 + 16 * (ρ ^ 2 + (ell : ℝ) ^ jq q) / a) (fun _ => 1)

include hell hP hdvd ha hρ hU hT in
theorem extF_energy (u : YP G) :
    ⟪extF G ell a u, LP G U a (extF G ell a u)⟫ ≤ ∑ p, betaS G ell a ρ p * ‖u p‖ ^ 2 := by
  classical
  have hell0 : 0 < ell := by omega
  have hw : ∀ j, 0 ≤ wq G a j := fun j => (wq_pos hell hP a j ha).le
  set g := extF G ell a u with hg
  rw [inner_LP G U a hw, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  -- the constraint part
  have hQ : ‖QpP G U a g‖ ^ 2 ≤ ∑ q : QIdx G, (1 + 6 * ρ) ^ 2 * ‖u (Sum.inl q)‖ ^ 2
      + ∑ x : OffIdx G, ‖u (Sum.inr x)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]
    refine add_le_add (Finset.sum_le_sum (fun q _ => ?_)) (le_of_eq (Finset.sum_congr rfl (fun x _ => ?_)))
    · have h1 := extF_row hell hP hdvd U a ha ρ hρ hT u q
      have h2 : ‖QpP G U a g (Sum.inl q)‖ ≤ (1 + 6 * ρ) * ‖u (Sum.inl q)‖ := by
        have h3 := norm_add_le (QpP G U a g (Sum.inl q) - u (Sum.inl q)) (u (Sum.inl q))
        rw [sub_add_cancel] at h3
        linarith
      have := pow_le_pow_left₀ (norm_nonneg _) h2 2
      rw [mul_pow] at this; exact this
    · rw [QpP_extF_inr hP a U u x]
  -- the gradient part
  have hD : ‖Dm G U g‖ ^ 2 ≤ ∑ q : QIdx G,
      (12 * (ρ / (ell : ℝ) ^ jq q) ^ 2 * (((ell ^ jq q : ℕ) : ℝ)) ^ 3
        + 12 * (((ell ^ jq q : ℕ) : ℝ) * ((ell ^ jq q : ℕ) : ℝ))) * ‖cq G a u q‖ ^ 2 := by
    have := grad_blockconst_le U (fun q : QIdx G => yq q) (fun q => ell ^ jq q) (fun q => fit_q hP hdvd hell0 q)
      (fun q q' hne => disj_q hP hne) (cq G a u) (siteMask G.Om0 g)
      (fun q x hx => mask_extF_on hP a u q hx) (fun x hx => mask_extF_off hP a u hx)
      (fun q => ρ / (ell : ℝ) ^ jq q) (fun q => by
        have : (0:ℝ) < (ell:ℝ) ^ jq q := pow_pos (by exact_mod_cast hell0) _
        exact div_nonneg hρ this.le)
      (fun q b hb => hU (jq q) (by rw [← hP.k_eq]; exact jq_le q) (yq q) (yq_mem q) b hb)
    exact this
  have hDq : ∀ q : QIdx G, (12 * (ρ / (ell : ℝ) ^ jq q) ^ 2 * (((ell ^ jq q : ℕ) : ℝ)) ^ 3
        + 12 * (((ell ^ jq q : ℕ) : ℝ) * ((ell ^ jq q : ℕ) : ℝ))) * ‖cq G a u q‖ ^ 2
      ≤ 16 * (ρ ^ 2 + (ell : ℝ) ^ jq q) / a * ‖u (Sum.inl q)‖ ^ 2 := by
    intro q
    set n : ℝ := (ell : ℝ) ^ jq q with hn
    have hnc : (((ell ^ jq q : ℕ) : ℝ)) = n := by push_cast; rfl
    rw [hnc]
    have hnpos : 0 < n := by positivity
    have hwpos := wq_pos hell hP a (jq q) ha
    have hc2 : ‖cq G a u q‖ ^ 2 = ‖u (Sum.inl q)‖ ^ 2 / wq G a (jq q) := by
      rw [cq, norm_smul, mul_pow, Real.norm_eq_abs, abs_inv, abs_of_pos (Real.sqrt_pos.mpr hwpos), inv_pow,
        Real.sq_sqrt hwpos.le]
      field_simp
    have hwdef : wq G a (jq q) = ajSeq a ell (jq q) * n := by rw [wq, hP.ell_eq]
    have hak := ajSeq_ge ell (jq q) hell ha
    have hajpos : 0 < ajSeq a ell (jq q) := by linarith
    rw [hc2, hwdef]
    have e : (12 * (ρ / n) ^ 2 * n ^ 3 + 12 * (n * n)) * (‖u (Sum.inl q)‖ ^ 2 / (ajSeq a ell (jq q) * n))
        = 12 * (ρ ^ 2 + n) / ajSeq a ell (jq q) * ‖u (Sum.inl q)‖ ^ 2 := by
      field_simp
    rw [e]
    have hu2 : 0 ≤ ‖u (Sum.inl q)‖ ^ 2 := sq_nonneg _
    have hnum : 0 ≤ ρ ^ 2 + n := by positivity
    have h1 : 12 * (ρ ^ 2 + n) / ajSeq a ell (jq q) ≤ 16 * (ρ ^ 2 + n) / a := by
      rw [div_le_div_iff₀ hajpos ha]
      nlinarith
    exact mul_le_mul_of_nonneg_right h1 hu2
  have hD' : ‖Dm G U g‖ ^ 2 ≤ ∑ q : QIdx G, 16 * (ρ ^ 2 + (ell : ℝ) ^ jq q) / a * ‖u (Sum.inl q)‖ ^ 2 :=
    hD.trans (Finset.sum_le_sum (fun q _ => hDq q))
  have hβ : ∑ p, betaS G ell a ρ p * ‖u p‖ ^ 2
      = ∑ q : QIdx G, ((1 + 6 * ρ) ^ 2 + 16 * (ρ ^ 2 + (ell : ℝ) ^ jq q) / a) * ‖u (Sum.inl q)‖ ^ 2
        + ∑ x : OffIdx G, ‖u (Sum.inr x)‖ ^ 2 := by
    rw [Fintype.sum_sum_type]
    simp only [betaS, Sum.elim_inl, Sum.elim_inr, one_mul]
  rw [hβ]
  have hsplit : ∑ q : QIdx G, ((1 + 6 * ρ) ^ 2 + 16 * (ρ ^ 2 + (ell : ℝ) ^ jq q) / a) * ‖u (Sum.inl q)‖ ^ 2
      = ∑ q : QIdx G, (1 + 6 * ρ) ^ 2 * ‖u (Sum.inl q)‖ ^ 2
        + ∑ q : QIdx G, 16 * (ρ ^ 2 + (ell : ℝ) ^ jq q) / a * ‖u (Sum.inl q)‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun q _ => by ring)
  rw [hsplit]
  linarith [hQ, hD']

include hell hP hdvd ha hρ hU hT in
/-- **S3 `gamma_lower_strat`**: `(1−6ρ)² Σ_p ‖v_p‖²/β_p ≤ (12+a)‖Xv‖²`, `β_q = (1+6ρ)² + 16(ρ² + ℓ^{j_q})/a`, `β = 1` on
padding rows. -/
theorem gamma_lower_strat (h6 : 6 * ρ ≤ 1) (hu : IsUnit (LP G U a)) (v : YP G) :
    (1 - 6 * ρ) ^ 2 * ∑ p, ‖v p‖ ^ 2 / betaS G ell a ρ p ≤ (12 + a) * ‖Xop G U a v‖ ^ 2 := by
  classical
  have hell0 : 0 < ell := by omega
  have hw : ∀ j, 0 ≤ wq G a j := fun j => (wq_pos hell hP a j ha).le
  have hβpos : ∀ p, 0 < betaS G ell a ρ p := by
    intro p
    cases p with
    | inl q =>
      simp only [betaS, Sum.elim_inl]
      have : 0 ≤ 16 * (ρ ^ 2 + (ell : ℝ) ^ jq q) / a := by positivity
      nlinarith [sq_nonneg (1 + 6 * ρ)]
    | inr x => simp [betaS]
  set β := betaS G ell a ρ with hβdef
  set u : YP G := WithLp.toLp 2 (fun p => (β p)⁻¹ • v p) with hu_def
  have hup : ∀ p, u p = (β p)⁻¹ • v p := fun p => rfl
  set g := extF G ell a u with hg
  set S := ∑ p, ‖v p‖ ^ 2 / β p with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun p _ => div_nonneg (sq_nonneg _) (hβpos p).le)
  have hgE : ⟪g, LP G U a g⟫ ≤ S := by
    refine (extF_energy hell hP hdvd U a ha ρ hρ hU hT u).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [hup, norm_smul, mul_pow, Real.norm_eq_abs, abs_inv, abs_of_pos (hβpos p), inv_pow]
    have := (hβpos p).ne'
    field_simp
    all_goals rfl
  have hr : |⟪v, QpP G U a g⟫ - S| ≤ 6 * ρ * S := by
    have hdiff : ⟪v, QpP G U a g⟫ - S = ∑ q : QIdx G, ⟪v (Sum.inl q), QpP G U a g (Sum.inl q) - u (Sum.inl q)⟫ := by
      have hvu : ∀ p, ⟪v p, u p⟫ = ‖v p‖ ^ 2 / β p := by
        intro p; rw [hup, real_inner_smul_right, real_inner_self_eq_norm_sq]; field_simp
      have h1 : S = ∑ p, ⟪v p, u p⟫ := Finset.sum_congr rfl (fun p _ => (hvu p).symm)
      rw [h1, PiLp.inner_apply, ← Finset.sum_sub_distrib, Fintype.sum_sum_type]
      have hz : ∑ x : OffIdx G, (⟪v (Sum.inr x), QpP G U a g (Sum.inr x)⟫ - ⟪v (Sum.inr x), u (Sum.inr x)⟫) = 0 := by
        refine Finset.sum_eq_zero (fun x _ => ?_)
        rw [QpP_extF_inr hP a U u x, sub_self]
      rw [hz, add_zero]
      exact Finset.sum_congr rfl (fun q _ => by rw [inner_sub_right])
    rw [hdiff]
    have hpt : ∀ q : QIdx G, |⟪v (Sum.inl q), QpP G U a g (Sum.inl q) - u (Sum.inl q)⟫|
        ≤ 6 * ρ * (‖v (Sum.inl q)‖ ^ 2 / β (Sum.inl q)) := by
      intro q
      have h1 := abs_real_inner_le_norm (v (Sum.inl q)) (QpP G U a g (Sum.inl q) - u (Sum.inl q))
      have h2 := extF_row hell hP hdvd U a ha ρ hρ hT u q
      have h3 : ‖u (Sum.inl q)‖ = ‖v (Sum.inl q)‖ / β (Sum.inl q) := by
        rw [hup, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hβpos _)]; field_simp
      rw [h3] at h2
      have h4 := mul_le_mul_of_nonneg_left h2 (norm_nonneg (v (Sum.inl q)))
      have e : ‖v (Sum.inl q)‖ * (6 * ρ * (‖v (Sum.inl q)‖ / β (Sum.inl q)))
          = 6 * ρ * (‖v (Sum.inl q)‖ ^ 2 / β (Sum.inl q)) := by ring
      linarith
    have hsum : |∑ q : QIdx G, ⟪v (Sum.inl q), QpP G U a g (Sum.inl q) - u (Sum.inl q)⟫|
        ≤ 6 * ρ * ∑ q : QIdx G, ‖v (Sum.inl q)‖ ^ 2 / β (Sum.inl q) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun q _ => hpt q)
    have hpart : ∑ q : QIdx G, ‖v (Sum.inl q)‖ ^ 2 / β (Sum.inl q) ≤ S := by
      rw [hS, Fintype.sum_sum_type]
      have : 0 ≤ ∑ x : OffIdx G, ‖v (Sum.inr x)‖ ^ 2 / β (Sum.inr x) :=
        Finset.sum_nonneg (fun x _ => div_nonneg (sq_nonneg _) (hβpos _).le)
      linarith
    have h6ρ : 0 ≤ 6 * ρ := by linarith
    exact hsum.trans (mul_le_mul_of_nonneg_left hpart h6ρ)
  exact gamma_lower_approx G U a hw hu (12 + a) (by linarith) (LP_form_le ell k hell hP U a ha)
    β (6 * ρ) h6 v g hgE hr hS0

end final

theorem stratG_le (G : TowerGeom L) (x : PeriodicLatticeSite L) : stratG G x ≤ G.k := by
  unfold stratG
  rcases Set.eq_empty_or_nonempty {j | j ≤ G.k ∧ OmGe G j x} with h | h
  · rw [h, csSup_empty]; exact bot_le
  · exact csSup_le h (fun j hj => hj.1)

/-- `wNormSq ≥ ℓ^{-2k} ‖Ω₀ f‖²` -/
theorem wNormSq_ge (G : TowerGeom L) (hell : 1 ≤ G.ell) (f : SiteL2 L) :
    ‖siteMask G.Om0 f‖ ^ 2 / ((G.ell : ℝ) ^ G.k) ^ 2 ≤ wNormSq G f := by
  rw [norm_sq_site, Finset.sum_div]
  refine Finset.sum_le_sum (fun x _ => ?_)
  have h1 : (1 : ℝ) ≤ G.ell := by exact_mod_cast hell
  have hp : (0 : ℝ) < ((G.ell : ℝ) ^ stratG G x) ^ 2 := by positivity
  have hle : ((G.ell : ℝ) ^ stratG G x) ^ 2 ≤ ((G.ell : ℝ) ^ G.k) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ h1 (stratG_le G x)) 2
  exact div_le_div_of_nonneg_left (sq_nonneg _) hp hle

/-- `IsUnit LP` from S1 -/
theorem isUnit_LP_strat (ell k : ℕ) (hell : 2 ≤ ell) (hdvd : ∀ μ, ell ^ k ∣ L μ + 1)
    {G : TowerGeom L} (hP : ProperTower G ell k) (U : Cfg L) (a : ℝ) (ha : 0 < a) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (h216 : 216 * ρ ^ 2 < 1)
    (hU : ∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∀ b ∈ inBlockBonds y (ell ^ j),
      frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ / (ell : ℝ) ^ j)
    (hT : ∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∀ i, i < j → ∀ z ∈ blockOf y (ell ^ j), z ∈ CoarseLattice L (ell ^ i) → ∀ μ : Fin 3,
      coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ j) →
      frobNorm ((bgTower G U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j) :
    IsUnit (LP G U a) := by
  have hell0 : 0 < ell := by omega
  set M6 := max 6 (16 / (3 * a))
  have hM6 : 0 < M6 := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  set N := ((G.ell : ℝ) ^ G.k) ^ 2
  have hN : 0 < N := by have : (0 : ℝ) < G.ell := by rw [hP.ell_eq]; exact_mod_cast hell0
                        positivity
  set c := min (((1 - 216 * ρ ^ 2) / M6) / N) 1 with hc
  have hc0 : 0 < c := lt_min (by apply div_pos (div_pos (by linarith) hM6) hN) one_pos
  have hcoer : ∀ f : SiteL2 L, c * ‖siteMask G.Om0 f‖ ^ 2 ≤ ⟪f, DelpA G U a f⟫ := by
    intro f
    have hS1 := site_coercive_weighted ell k hell hdvd hP U a ha ρ hρ hU hT f
    have hwg := wNormSq_ge G (by rw [hP.ell_eq]; omega) f
    have h1 : c * ‖siteMask G.Om0 f‖ ^ 2 ≤ ((1 - 216 * ρ ^ 2) / M6) * (‖siteMask G.Om0 f‖ ^ 2 / N) := by
      have := min_le_left (((1 - 216 * ρ ^ 2) / M6) / N) 1
      have e : ((1 - 216 * ρ ^ 2) / M6) * (‖siteMask G.Om0 f‖ ^ 2 / N)
          = (((1 - 216 * ρ ^ 2) / M6) / N) * ‖siteMask G.Om0 f‖ ^ 2 := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    have h2 : ((1 - 216 * ρ ^ 2) / M6) * (‖siteMask G.Om0 f‖ ^ 2 / N) ≤ ((1 - 216 * ρ ^ 2) / M6) * wNormSq G f :=
      mul_le_mul_of_nonneg_left hwg (div_nonneg (by linarith) hM6.le)
    have h3 : ((1 - 216 * ρ ^ 2) / M6) * wNormSq G f ≤ ⟪f, DelpA G U a f⟫ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hM6]; linarith
    linarith
  exact (AdalyFormal.SiteCoercivity.unit_Gp_of_masked_coercive G U a hc0 (min_le_right _ _) hcoer).1

/-- `Γ` has a two-sided inverse at a proper tower, stratum-class `U`, `ρ < 1/6`. -/
theorem exists_Gami_strat (ell k : ℕ) (hell : 2 ≤ ell) (hdvd : ∀ μ, ell ^ k ∣ L μ + 1)
    {G : TowerGeom L} (hP : ProperTower G ell k) (U : Cfg L) (a : ℝ) (ha : 0 < a) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (h216 : 216 * ρ ^ 2 < 1)
    (hU : ∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∀ b ∈ inBlockBonds y (ell ^ j),
      frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ / (ell : ℝ) ^ j)
    (hT : ∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∀ i, i < j → ∀ z ∈ blockOf y (ell ^ j), z ∈ CoarseLattice L (ell ^ i) → ∀ μ : Fin 3,
      coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ j) →
      frobNorm ((bgTower G U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j) :
    ∃ Gi : YP G →L[ℝ] YP G,
      (∀ u, (ContinuousLinearMap.adjoint (Xop G U a) ∘L Xop G U a) (Gi u) = u) ∧
      (∀ u, Gi ((ContinuousLinearMap.adjoint (Xop G U a) ∘L Xop G U a) u) = u) := by
  have h6 : 6 * ρ < 1 := by nlinarith
  have hu := isUnit_LP_strat ell k hell hdvd hP U a ha ρ hρ h216 hU hT
  have hβpos : ∀ p, 0 < betaS G ell a ρ p := by
    intro p
    cases p with
    | inl q =>
      simp only [betaS, Sum.elim_inl]
      have : 0 ≤ 16 * (ρ ^ 2 + (ell : ℝ) ^ jq q) / a := by positivity
      nlinarith [sq_nonneg (1 + 6 * ρ)]
    | inr x => simp [betaS]
  have hc : 0 < (1 - 6 * ρ) ^ 2 / (12 + a) := div_pos (by nlinarith) (by linarith)
  refine exists_Gami_of_lower G U a (betaS G ell a ρ) hβpos _ hc (fun v => ?_)
  have := gamma_lower_strat hell hP hdvd U a ha ρ hρ hU hT h6.le hu v
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  linarith

#print axioms card_blockOf
#print axioms fit_q
#print axioms disj_q
#print axioms extF_on
#print axioms extF_off
#print axioms Qlev_congr_box
#print axioms Qlev_flat_bc
#print axioms row_drift
#print axioms extF_row
#print axioms extF_energy
#print axioms gamma_lower_strat
#print axioms stratG_le
#print axioms wNormSq_ge
#print axioms isUnit_LP_strat
#print axioms exists_Gami_strat

#print axioms jq_le
#print axioms yq_mem
#print axioms block_Om0
#print axioms Om0_block
#print axioms mask_extF_on
#print axioms mask_extF_off
#print axioms QpP_extF_inr
#print axioms wq_pos

end AdalyFormal.M1Site
