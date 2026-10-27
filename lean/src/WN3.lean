import WN1

/-!
# WN3 (renamed from NF3: module-name collision with deps/base/NF4) -- the all-rows constraint map `Qrow` of a proper tower: kernel, norm, drift

For `G : TowerGeom L` and the row index `QIdx G` of lane C (rows `(j, y)`, `j ≤ k`, `y ∈ Λ_j`):
`Qrow G U f = (Q'_j(U) f (y))_{(j,y)}` (unweighted), valued in `CRow G = L²(rows; su(2))`.
* `mem_NQp_of_Qrow` (`Ω₀ = univ`): `Qrow G U f = 0 → f ∈ N(Q'(U))`;  `Qrow_of_NQp`: the converse.
* `sum_blocks_q` : the constraint blocks of a proper tower are pairwise disjoint, so `Σ_q Σ_{B_q} h ≤ Σ h` (`h ≥ 0`).
* `Qrow_norm_sq` : every row at level `≥ j0` ⇒ `‖Qrow G U f‖² ≤ (ℓ⁻³)^{j0} ‖f‖²` (any `U`).
* `Qrow_drift_sq` : aligned background links `‖Ū^{(i)} − 1‖ ≤ a_i` (`i < k`) and `dsum ℓ a (j_q) ≤ D` on every row ⇒
  `‖Qrow G U f − Qrow G 1 f‖² ≤ D² (ℓ⁻³)^{j0} ‖f‖²`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.W3NF

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.QjComposite (Qcomposite)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.M1Site (QIdx jq yq jq_le yq_mem fit_q disj_q card_blockOf)
open AdalyFormal.SiteCoercivity (ProperTower)

variable {L : PeriodicLatticeExtent}

/-- the row space -/
abbrev CRow (G : TowerGeom L) : Type := PiLp 2 (fun _ : QIdx G => SuTwo)

/-- the all-rows constraint map -/
noncomputable def Qrow (G : TowerGeom L) (U : Cfg L) : SiteL2 L →L[ℝ] CRow G :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 (fun q : QIdx G => Qlev G U (jq q) (yq q) f)
      map_add' := fun f g => by refine PiLp.ext (fun q => ?_); simp
      map_smul' := fun c f => by refine PiLp.ext (fun q => ?_); simp }

theorem Qrow_apply (G : TowerGeom L) (U : Cfg L) (f : SiteL2 L) (q : QIdx G) :
    Qrow G U f q = Qlev G U (jq q) (yq q) f := rfl

theorem mem_NQp_of_Qrow (G : TowerGeom L) (hOm : G.Om0 = Set.univ) (U : Cfg L) (f : SiteL2 L)
    (hf : Qrow G U f = 0) : f ∈ NQp G U := by
  refine ⟨fun x hx => absurd (by rw [hOm]; trivial) hx, fun j hj y hy => ?_⟩
  have := congrArg (fun g : CRow G => g ⟨(⟨j, Nat.lt_succ_of_le hj⟩, y), hy⟩) hf
  simpa [Qrow_apply, jq, yq] using this

theorem Qrow_of_NQp (G : TowerGeom L) (U : Cfg L) (f : SiteL2 L) (hf : f ∈ NQp G U) : Qrow G U f = 0 := by
  refine PiLp.ext (fun q => ?_)
  rw [Qrow_apply]
  exact hf.2 (jq q) (jq_le q) (yq q) (yq_mem q)

theorem cpow_aux (ell : ℝ) (hl : 0 < ell) (j : ℕ) :
    ((1 / ell ^ 3) ^ j) ^ 2 * ((ell ^ j) ^ 3) = (1 / ell ^ 3) ^ j := by
  have hx : 0 < ell ^ j := pow_pos hl j
  have e : (1 / ell ^ 3) ^ j = 1 / (ell ^ j) ^ 3 := by rw [one_div_pow, ← pow_mul, ← pow_mul, mul_comm]
  rw [e]; field_simp

section proper
variable {G : TowerGeom L} {ell k : ℕ} (hP : ProperTower G ell k)
include hP

theorem sum_blocks_q (h : PeriodicLatticeSite L → ℝ) (hh : ∀ x, 0 ≤ h x) :
    ∑ q : QIdx G, ∑ x ∈ blockOf (yq q) (ell ^ jq q), h x ≤ ∑ x, h x := by
  classical
  rw [← Finset.sum_biUnion (s := (Finset.univ : Finset (QIdx G)))
    (t := fun q => blockOf (yq q) (ell ^ jq q))]
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hh x)
  · intro q _ q' _ hne
    exact disj_q hP hne

variable (hdvd : ∀ μ, ell ^ k ∣ L μ + 1)
include hdvd

/-- one row: `‖Q'_j(U) f(y)‖² ≤ (ℓ⁻³)^j Σ_{B(y,ℓ^j)} ‖f‖²`. -/
theorem row_sq_le (hell : 0 < ell) (U : Cfg L) (f : SiteL2 L) (q : QIdx G) :
    ‖Qlev G U (jq q) (yq q) f‖ ^ 2 ≤ (1 / (ell : ℝ) ^ 3) ^ jq q * ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ ^ 2 := by
  rw [Qlev_apply, hP.ell_eq]
  have h1 := AdalyFormal.BondComposite.norm_Qcomposite_le (bgTower G U) ell hell (WithLp.ofLp f) (jq q) (yq q)
  have hcard := card_blockOf (yq q) (ell ^ jq q) (fit_q hP hdvd hell q)
  have hcs := sq_sum_le_card_mul_sum_sq (s := blockOf (yq q) (ell ^ jq q)) (f := fun x => ‖f x‖)
  rw [hcard] at hcs
  have hc : (0 : ℝ) ≤ (1 / (ell : ℝ) ^ 3) ^ jq q := by positivity
  have hS : 0 ≤ ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ := Finset.sum_nonneg (fun x _ => norm_nonneg _)
  have h2 : ‖Qcomposite (bgTower G U) ell (jq q) (WithLp.ofLp f) (yq q)‖ ^ 2
      ≤ ((1 / (ell : ℝ) ^ 3) ^ jq q * ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hpow : ((1 / (ell : ℝ) ^ 3) ^ jq q) ^ 2 * (((ell ^ jq q) ^ 3 : ℕ) : ℝ) = (1 / (ell : ℝ) ^ 3) ^ jq q := by
    push_cast
    exact cpow_aux (ell : ℝ) hellR (jq q)
  calc ‖Qcomposite (bgTower G U) ell (jq q) (WithLp.ofLp f) (yq q)‖ ^ 2
      ≤ ((1 / (ell : ℝ) ^ 3) ^ jq q) ^ 2 * (∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖) ^ 2 := by
        rw [← mul_pow]; exact h2
    _ ≤ ((1 / (ell : ℝ) ^ 3) ^ jq q) ^ 2 * ((((ell ^ jq q) ^ 3 : ℕ) : ℝ) *
          ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = _ := by rw [← mul_assoc, hpow]

/-- **norm of `Qrow`**. -/
theorem Qrow_norm_sq (hell : 0 < ell) (j0 : ℕ) (hlev : ∀ q : QIdx G, j0 ≤ jq q) (U : Cfg L) (f : SiteL2 L) :
    ‖Qrow G U f‖ ^ 2 ≤ (1 / (ell : ℝ) ^ 3) ^ j0 * ‖f‖ ^ 2 := by
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hc0 : (0 : ℝ) ≤ 1 / (ell : ℝ) ^ 3 := by positivity
  have hc1 : 1 / (ell : ℝ) ^ 3 ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ hellR
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  calc ∑ q : QIdx G, ‖Qrow G U f q‖ ^ 2
      ≤ ∑ q : QIdx G, (1 / (ell : ℝ) ^ 3) ^ j0 * ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ ^ 2 := by
        refine Finset.sum_le_sum (fun q _ => ?_)
        rw [Qrow_apply]
        refine (row_sq_le hP hdvd hell U f q).trans ?_
        refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg (fun x _ => sq_nonneg _))
        exact pow_le_pow_of_le_one hc0 hc1 (hlev q)
    _ = (1 / (ell : ℝ) ^ 3) ^ j0 * ∑ q : QIdx G, ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ (1 / (ell : ℝ) ^ 3) ^ j0 * ∑ x, ‖f x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_blocks_q hP _ (fun x => sq_nonneg _)) (by positivity)

/-- **drift of `Qrow`**. -/
theorem Qrow_drift_sq (hell : 0 < ell) (j0 : ℕ) (hlev : ∀ q : QIdx G, j0 ≤ jq q) (U : Cfg L)
    (a : ℕ → ℝ) (hbg : ∀ i, i < k → ∀ y ∈ CoarseLattice L (ell ^ i), ∀ μ : Fin 3,
      frobNorm (((bgTower G U i (y, μ) : _) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ a i)
    (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ q : QIdx G, |AdalyFormal.BondComposite.dsum ell a (jq q)| ≤ D)
    (f : SiteL2 L) :
    ‖Qrow G U f - Qrow G (trivialU L) f‖ ^ 2 ≤ D ^ 2 * ((1 / (ell : ℝ) ^ 3) ^ j0 * ‖f‖ ^ 2) := by
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hc0 : (0 : ℝ) ≤ 1 / (ell : ℝ) ^ 3 := by positivity
  have hc1 : 1 / (ell : ℝ) ^ 3 ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ hellR
  have hbg1 : bgTower G (trivialU L) = fun _ => trivialU L :=
    funext (fun i => AdalyFormal.PortSlice.bgTower_trivialU G i)
  have hrow : ∀ q : QIdx G, ‖(Qrow G U f - Qrow G (trivialU L) f) q‖ ^ 2
      ≤ D ^ 2 * ((1 / (ell : ℝ) ^ 3) ^ j0 * ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ ^ 2) := by
    intro q
    have hj : jq q ≤ k := by rw [← hP.k_eq]; exact jq_le q
    have hyc : yq q ∈ CoarseLattice L (ell ^ jq q) := hP.coarse _ hj _ (yq_mem q)
    have hpd := AdalyFormal.BondComposite.Qcomposite_drift_pointwise (bgTower G U) ell hell a k
      (fun i hi μ => Dvd.dvd.trans (pow_dvd_pow ell hi) (hdvd μ)) hbg (WithLp.ofLp f) (jq q) hj (yq q) hyc
    have hflat := AdalyFormal.FlatExt.Qcomposite_flat (L := L) ell hell (jq q) (WithLp.ofLp f) (yq q)
    have he : (Qrow G U f - Qrow G (trivialU L) f) q
        = Qcomposite (bgTower G U) ell (jq q) (WithLp.ofLp f) (yq q)
          - (1 / (ell : ℝ) ^ 3) ^ jq q • ∑ x ∈ blockOf (yq q) (ell ^ jq q), (WithLp.ofLp f) x := by
      rw [← hflat]
      show Qrow G U f q - Qrow G (trivialU L) f q = _
      rw [Qrow_apply, Qrow_apply, Qlev_apply, Qlev_apply, hbg1, hP.ell_eq]
    rw [he]
    have hcard := card_blockOf (yq q) (ell ^ jq q) (fit_q hP hdvd hell q)
    have hcs := sq_sum_le_card_mul_sum_sq (s := blockOf (yq q) (ell ^ jq q)) (f := fun x => ‖f x‖)
    rw [hcard] at hcs
    have hS : 0 ≤ ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ := Finset.sum_nonneg (fun x _ => norm_nonneg _)
    set S := ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ with hSdef
    set S2 := ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ ^ 2 with hS2def
    set c := (1 / (ell : ℝ) ^ 3) ^ jq q with hcdef
    have hc : 0 ≤ c := by positivity
    have hdq : AdalyFormal.BondComposite.dsum ell a (jq q) ≤ D := (le_abs_self _).trans (hD q)
    have hdq' : -D ≤ AdalyFormal.BondComposite.dsum ell a (jq q) := by
      have := neg_abs_le (AdalyFormal.BondComposite.dsum ell a (jq q)); linarith [hD q]
    have h1 : ‖Qcomposite (bgTower G U) ell (jq q) (WithLp.ofLp f) (yq q) - c • ∑ x ∈ blockOf (yq q) (ell ^ jq q),
        (WithLp.ofLp f) x‖ ≤ D * (c * S) := by
      refine hpd.trans ?_
      exact mul_le_mul_of_nonneg_right hdq (mul_nonneg hc hS)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have hellR0 : (0 : ℝ) < ell := by linarith
    have hpow : c ^ 2 * (((ell ^ jq q) ^ 3 : ℕ) : ℝ) = c := by
      rw [hcdef]; push_cast
      exact cpow_aux (ell : ℝ) hellR0 (jq q)
    have h3 : (D * (c * S)) ^ 2 ≤ D ^ 2 * (c * S2) := by
      have : (c * S) ^ 2 ≤ c * S2 := by
        calc (c * S) ^ 2 = c ^ 2 * S ^ 2 := by ring
          _ ≤ c ^ 2 * ((((ell ^ jq q) ^ 3 : ℕ) : ℝ) * S2) := mul_le_mul_of_nonneg_left hcs (by positivity)
          _ = c * S2 := by rw [← mul_assoc, hpow]
      calc (D * (c * S)) ^ 2 = D ^ 2 * (c * S) ^ 2 := by ring
        _ ≤ D ^ 2 * (c * S2) := mul_le_mul_of_nonneg_left this (sq_nonneg _)
    have h4 : c ≤ (1 / (ell : ℝ) ^ 3) ^ j0 := pow_le_pow_of_le_one hc0 hc1 (hlev q)
    have hS20 : 0 ≤ S2 := Finset.sum_nonneg (fun x _ => sq_nonneg _)
    calc _ ≤ (D * (c * S)) ^ 2 := h2
      _ ≤ D ^ 2 * (c * S2) := h3
      _ ≤ D ^ 2 * ((1 / (ell : ℝ) ^ 3) ^ j0 * S2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 hS20) (sq_nonneg _)
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  calc ∑ q : QIdx G, ‖(Qrow G U f - Qrow G (trivialU L) f) q‖ ^ 2
      ≤ ∑ q : QIdx G, D ^ 2 * ((1 / (ell : ℝ) ^ 3) ^ j0 * ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ ^ 2) :=
        Finset.sum_le_sum (fun q _ => hrow q)
    _ = D ^ 2 * ((1 / (ell : ℝ) ^ 3) ^ j0 * ∑ q : QIdx G, ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ D ^ 2 * ((1 / (ell : ℝ) ^ 3) ^ j0 * ∑ x, ‖f x‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (sq_nonneg _)
        exact sum_blocks_q hP _ (fun x => sq_nonneg _)

end proper

#print axioms cpow_aux
#print axioms Qrow_apply
#print axioms mem_NQp_of_Qrow
#print axioms Qrow_of_NQp
#print axioms sum_blocks_q
#print axioms row_sq_le
#print axioms Qrow_norm_sq
#print axioms Qrow_drift_sq

end AdalyFormal.W3NF
