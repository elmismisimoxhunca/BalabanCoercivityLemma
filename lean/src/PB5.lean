import PSiteC8
import PB2
import AdalyFormal.Balaban.BlockedBackground

/-!
# PB5 -- item (2c): the `Q'` norm and `Q'`-drift inputs `hQq`, `hQdrift` of the slice chain, from the ported `Ns` contraction/drift
(`PSiteC5` `Ns_stepAverage_le`, `PSiteC6` `Ns_telescope`).

For the top-level constraint map `Qtop (GF ell k Lu) U f = (Q'_k(U) f)|_{Λ_k}` (`Λ_k` = all stride-`ell^k` centres):
* `Qtop_norm_sq`        : `(ell^k)^3 ‖Qtop U f‖² = Ns(ell^k)(Q_k(bg) f)²`   (`Ns s g² = s³ Σ_{y ∈ CL(s)} ‖g y‖²`),
* `hQq_ported`          : `‖Qtop U f‖ ≤ q ‖f‖`,  `q = sqrt(1/(ell^k)^3) = n^{-3/2}`   (no smallness; any `U`),
* `hQdrift_ported`      : `‖Qtop U f - Qtop 1 f‖ ≤ q · (Σ_{i<k} 6(ell-1) δ_i) ‖f‖`   from `frobSupBond (bgTower U i) ≤ δ i`.
Standard axioms only (each declaration's printed axiom line).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
namespace AdalyFormal.PortSlice

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.QjComposite (Qcomposite Qcomposite_zero Qcomposite_succ)
open AdalyFormal.SiteCoercivity (Ns Ns_sq Ns_one Ns_nonneg Ns_telescope Ns_stepAverage_le norm_sq_site le_of_sq_le_sq')
open AdalyFormal.SliceCoerc (GF Qtop coarseC)

variable {L : PeriodicLatticeExtent}

/-- the nested composite (any background) is an `Ns`-contraction. -/
theorem Ns_Qcomposite_le (ell : ℕ) (hell : 0 < ell)
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (f : PeriodicLatticeSite L → AdalyFormal.Balaban.CovariantOperators.SuTwo) :
    ∀ j : ℕ, Ns (ell ^ j) (Qcomposite bg ell j f) ≤ Ns 1 f := by
  intro j
  induction j with
  | zero => simp [Qcomposite_zero]
  | succ j ih =>
    rw [Qcomposite_succ, pow_succ]
    exact le_trans (Ns_stepAverage_le (ell ^ j) ell (pow_pos hell j) hell _ _) ih

theorem bgTower_trivialU {L : PeriodicLatticeExtent} (G : TowerGeom L) (j : ℕ) :
    bgTower G (trivialU L) j = trivialU L := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have e : bgTower G (trivialU L) (j + 1)
        = AdalyFormal.Balaban.BlockedBackground.ubarSU2 (G.ell ^ j) G.ell (bgTower G (trivialU L) j) := rfl
    rw [e, ih, AdalyFormal.Balaban.BlockedBackground.ubarSU2_trivialU]

theorem mem_Lam_k_iff (ell k : ℕ) (Lu : PeriodicLatticeExtent) (x : PeriodicLatticeSite (scaleUp ell k Lu)) :
    x ∈ (GF ell k Lu).Lam (GF ell k Lu).k ↔ x ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ k) := by
  have h := fullTower_lam_k ell k Lu x
  show x ∈ (geomOf ell k (fullTower ell k Lu)).Lam k ↔ _
  rw [h, mem_CoarseLattice]
  constructor
  · intro hh μ; exact Nat.mod_eq_zero_of_dvd (hh μ)
  · intro hh μ; exact Nat.dvd_of_mod_eq_zero (hh μ)

/-- the `L²(Λ_k)` norm of a site function restricted to `Λ_k` is the `CL(ell^k)` sum. -/
theorem coarseC_norm_sq (ell k : ℕ) (Lu : PeriodicLatticeExtent)
    (g : PeriodicLatticeSite (scaleUp ell k Lu) → AdalyFormal.Balaban.CovariantOperators.SuTwo) :
    ‖(WithLp.toLp 2 (fun y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k} => g y.1) : coarseC (GF ell k Lu))‖ ^ 2
      = ∑ y ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ k), ‖g y‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact (Finset.sum_subtype (CoarseLattice (scaleUp ell k Lu) (ell ^ k)) (fun x => (mem_Lam_k_iff ell k Lu x).symm)
    (fun y => ‖g y‖ ^ 2)).symm

theorem Ns_sq_coarse (ell k : ℕ) (Lu : PeriodicLatticeExtent)
    (g : PeriodicLatticeSite (scaleUp ell k Lu) → AdalyFormal.Balaban.CovariantOperators.SuTwo) :
    Ns (ell ^ k) g ^ 2 = ((ell : ℝ) ^ k) ^ 3 *
      ‖(WithLp.toLp 2 (fun y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k} => g y.1) : coarseC (GF ell k Lu))‖ ^ 2 := by
  rw [coarseC_norm_sq, Ns_sq]
  push_cast
  rfl

theorem Qtop_eq (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (f : SiteL2 (scaleUp ell k Lu)) :
    Qtop (GF ell k Lu) U f
      = WithLp.toLp 2 (fun y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k} =>
          Qcomposite (bgTower (GF ell k Lu) U) ell k (WithLp.ofLp f) y.1) := rfl

/-- the `Q'` norm: `‖Qtop U f‖ ≤ n^{-3/2} ‖f‖`. -/
theorem hQq_ported (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu))
    (f : SiteL2 (scaleUp ell k Lu)) :
    ‖Qtop (GF ell k Lu) U f‖ ≤ Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3) * ‖f‖ := by
  have hn : 0 < ((ell : ℝ) ^ k) ^ 3 := by positivity
  have h1 := Ns_Qcomposite_le ell hell (bgTower (GF ell k Lu) U) (WithLp.ofLp f) k
  have h2 : Ns 1 (WithLp.ofLp f) = ‖f‖ := by
    refine le_antisymm ?_ ?_
    · refine le_of_sq_le_sq' (norm_nonneg _) ?_
      rw [Ns_one, ← norm_sq_site]
    · refine le_of_sq_le_sq' (Ns_nonneg _ _) ?_
      rw [Ns_one, ← norm_sq_site]
  rw [h2] at h1
  have h3 := Ns_sq_coarse ell k Lu (Qcomposite (bgTower (GF ell k Lu) U) ell k (WithLp.ofLp f))
  rw [← Qtop_eq] at h3
  have h4 : ((ell : ℝ) ^ k) ^ 3 * ‖Qtop (GF ell k Lu) U f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [← h3]; exact pow_le_pow_left₀ (Ns_nonneg _ _) h1 2
  have h5 : ‖Qtop (GF ell k Lu) U f‖ ^ 2 ≤ (1 / ((ell : ℝ) ^ k) ^ 3) * ‖f‖ ^ 2 := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hn]; linarith
  calc ‖Qtop (GF ell k Lu) U f‖ = Real.sqrt (‖Qtop (GF ell k Lu) U f‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((1 / ((ell : ℝ) ^ k) ^ 3) * ‖f‖ ^ 2) := Real.sqrt_le_sqrt h5
    _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

/-- the `Q'` drift: `‖Qtop U f - Qtop 1 f‖ ≤ n^{-3/2} (Σ_{i<k} 6(ell-1)δ_i) ‖f‖`. -/
theorem hQdrift_ported (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu))
    (δ : ℕ → ℝ) (hδ : ∀ i, i < k → frobSupBond (bgTower (GF ell k Lu) U i) ≤ δ i)
    (f : SiteL2 (scaleUp ell k Lu)) :
    ‖Qtop (GF ell k Lu) U f - Qtop (GF ell k Lu) (trivialU (scaleUp ell k Lu)) f‖
      ≤ (Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3) * ∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * δ i) * ‖f‖ := by
  have hn : 0 < ((ell : ℝ) ^ k) ^ 3 := by positivity
  have hS : 0 ≤ ∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * δ i := by
    refine Finset.sum_nonneg (fun i hi => ?_)
    have hd : 0 ≤ δ i := le_trans (by
      unfold frobSupBond
      exact (Finset.le_sup'_iff _).mpr ⟨(0, 0), Finset.mem_univ _, AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _⟩)
      (hδ i (Finset.mem_range.mp hi))
    have : (1 : ℝ) ≤ ell := by exact_mod_cast hell
    have : 0 ≤ (ell : ℝ) - 1 := by linarith
    positivity
  have hT := Ns_telescope ell hell (bgTower (GF ell k Lu) U) δ k hδ (WithLp.ofLp f) k le_rfl
  have hbg : Qcomposite (fun _ => trivialU (scaleUp ell k Lu)) ell k (WithLp.ofLp f)
      = Qcomposite (bgTower (GF ell k Lu) (trivialU (scaleUp ell k Lu))) ell k (WithLp.ofLp f) := by
    congr 1
    funext j
    exact (bgTower_trivialU (GF ell k Lu) j).symm
  rw [hbg] at hT
  have hdiff : Qtop (GF ell k Lu) U f - Qtop (GF ell k Lu) (trivialU (scaleUp ell k Lu)) f
      = WithLp.toLp 2 (fun y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k} =>
          (Qcomposite (bgTower (GF ell k Lu) U) ell k (WithLp.ofLp f)
            - Qcomposite (bgTower (GF ell k Lu) (trivialU (scaleUp ell k Lu))) ell k (WithLp.ofLp f)) y.1) := rfl
  have h3 := Ns_sq_coarse ell k Lu (Qcomposite (bgTower (GF ell k Lu) U) ell k (WithLp.ofLp f)
            - Qcomposite (bgTower (GF ell k Lu) (trivialU (scaleUp ell k Lu))) ell k (WithLp.ofLp f))
  rw [← hdiff] at h3
  have h2 : Ns 1 (WithLp.ofLp f) = ‖f‖ := by
    refine le_antisymm ?_ ?_
    · refine le_of_sq_le_sq' (norm_nonneg _) ?_
      rw [Ns_one, ← norm_sq_site]
    · refine le_of_sq_le_sq' (Ns_nonneg _ _) ?_
      rw [Ns_one, ← norm_sq_site]
  rw [h2] at hT
  have h4 : ((ell : ℝ) ^ k) ^ 3 * ‖Qtop (GF ell k Lu) U f - Qtop (GF ell k Lu) (trivialU (scaleUp ell k Lu)) f‖ ^ 2
      ≤ ((∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * δ i) * ‖f‖) ^ 2 := by
    rw [← h3]; exact pow_le_pow_left₀ (Ns_nonneg _ _) hT 2
  have h5 : ‖Qtop (GF ell k Lu) U f - Qtop (GF ell k Lu) (trivialU (scaleUp ell k Lu)) f‖ ^ 2
      ≤ (1 / ((ell : ℝ) ^ k) ^ 3) * ((∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * δ i) * ‖f‖) ^ 2 := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hn]; linarith
  calc _ = Real.sqrt (‖Qtop (GF ell k Lu) U f - Qtop (GF ell k Lu) (trivialU (scaleUp ell k Lu)) f‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((1 / ((ell : ℝ) ^ k) ^ 3) * ((∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * δ i) * ‖f‖) ^ 2) :=
        Real.sqrt_le_sqrt h5
    _ = _ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (mul_nonneg hS (norm_nonneg _))]; ring

#print axioms Ns_Qcomposite_le
#print axioms bgTower_trivialU
#print axioms hQq_ported
#print axioms hQdrift_ported

end AdalyFormal.PortSlice
