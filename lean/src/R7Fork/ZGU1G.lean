import R7Fork.ZGU1F
import R7Fork.ZHodgeFinal

/-!
# GU1G -- flat block-average calculus used by the positivity argument:
(a) the SITE composite `Q'_j` (tree `Qcomposite`) at the flat tower is the `ell^j`-block mean;
(b) the `ell^j`-block line average intertwines with the gradient: `Q_n D φ = n⁻⁴ (Φ(z+n e_μ) − Φ(z))`
    with `Φ(z) = Σ_{x∈B_n(z)} φ x`;
(c) the `n`-block line average of a constant-per-direction field is that constant.
Standard axioms only (see the #print axioms lines).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.GenuineU1

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_CoarseLattice
  card_blockOf_of_coarse)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf Qcomposite stepAverage_trivialU)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf unit_block_sum)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CoarseShiftCovariance (coarseShift_blockOf_eq_image coarseShift_injective)

variable {L : PeriodicLatticeExtent}

/-- (a) the flat site composite is the `n`-block mean -/
theorem Qcomposite_closed (ell : ℕ) (hell : 0 < ell)
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hbg : ∀ j, bg j = trivialU L) (J : ℕ) (hdvdJ : ∀ ν, ell ^ J ∣ L ν + 1)
    (lam : PeriodicLatticeSite L → SuTwo) :
    ∀ j, j ≤ J → ∀ n : ℕ, n = ell ^ j → ∀ y ∈ CoarseLattice L n,
      Qcomposite bg ell j lam y = (1 / (n : ℝ) ^ 3) • ∑ x ∈ blockOf y n, lam x := by
  intro j
  induction j with
  | zero =>
      intro _ n hn y _
      have hn1 : n = 1 := by simpa using hn
      subst hn1
      rw [AdalyFormal.Balaban.QjComposite.blockOf_one_eq_singleton y]
      simp [Qcomposite]
  | succ j ih =>
      intro hj n' hn' y hy
      have hn'' : n' = ell ^ j * ell := by rw [hn', pow_succ]
      subst hn''
      have hs : 0 < ell ^ j := pow_pos hell j
      have hdvd1 : ∀ ν, ell ^ j * ell ∣ L ν + 1 := fun ν =>
        dvd_trans (by rw [← pow_succ]; exact pow_dvd_pow ell hj) (hdvdJ ν)
      have hdn : ∀ ν, ell ^ j ∣ L ν + 1 := fun ν => dvd_trans (dvd_mul_right _ _) (hdvd1 ν)
      have hys : y ∈ CoarseLattice L (ell ^ j) := by
        rw [mem_CoarseLattice] at hy ⊢
        intro ν
        exact Nat.mod_eq_zero_of_dvd (dvd_trans (dvd_mul_right _ _) (Nat.dvd_of_mod_eq_zero (hy ν)))
      show AdalyFormal.Balaban.QjComposite.stepAverage (ell ^ j) (bg j) ell (Qcomposite bg ell j lam) y = _
      rw [hbg j, stepAverage_trivialU]
      have hstep : ∀ x ∈ stepBlockOf y (ell ^ j) ell,
          Qcomposite bg ell j lam x = (1 / ((ell ^ j : ℕ) : ℝ) ^ 3) • ∑ x' ∈ blockOf x (ell ^ j), lam x' := by
        intro x hx
        rw [stepBlock_eq_filter hys, Finset.mem_filter] at hx
        exact ih (by omega) (ell ^ j) rfl x hx.2
      rw [Finset.sum_congr rfl hstep, ← Finset.smul_sum, smul_smul]
      have hsum := unit_block_sum (L := L) hs hdn hy 0 0 (fun z => lam z)
      simp only [Nat.zero_mul, pathSite_zero] at hsum
      have e1 := sum_unitSites (L := L) (ell ^ j) ell hys (fun x => ∑ x' ∈ blockOf x (ell ^ j), lam x')
      rw [← e1, hsum]
      congr 1
      have : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
      have h2 : (ell : ℝ) ^ j ≠ 0 := pow_ne_zero j this
      push_cast
      field_simp

#print axioms Qcomposite_closed

/-- (b) the `n`-block line average of a gradient -/
theorem LCR_grad (n : ℕ) (hn : 0 < n) (hdvd : ∀ ν, n ∣ L ν + 1) (φ : PeriodicLatticeSite L → SuTwo)
    (z : PeriodicLatticeSite L) (hz : z ∈ CoarseLattice L n) (μ : Fin 3) :
    lineCoarseRestrictSuTwo n (fun b : Bond L => φ (periodicLatticeShift b.1 b.2) - φ b.1) (⟨z, hz⟩, μ)
      = (1 / (n : ℝ) ^ 4) • (∑ x ∈ blockOf (coarseShift z n μ) n, φ x - ∑ x ∈ blockOf z n, φ x) := by
  unfold lineCoarseRestrictSuTwo
  congr 1
  have htel : ∀ x : PeriodicLatticeSite L,
      ∑ i ∈ Finset.range n, (φ (periodicLatticeShift (pathSite x μ i) μ) - φ (pathSite x μ i))
        = φ (coarseShift x n μ) - φ x := by
    intro x
    have := Finset.sum_range_sub (fun i => φ (pathSite x μ i)) n
    simp only [pathSite_succ, pathSite_zero] at this
    exact this
  have hs : ∀ x ∈ blockOf z n,
      ∑ i ∈ Finset.range n, (fun b : Bond L => φ (periodicLatticeShift b.1 b.2) - φ b.1) (pathSite x μ i, μ)
        = φ (coarseShift x n μ) - φ x := fun x _ => htel x
  rw [Finset.sum_congr rfl hs, Finset.sum_sub_distrib,
    coarseShift_blockOf_eq_image hn (hdvd μ) hz,
    Finset.sum_image (fun x _ x' _ h => coarseShift_injective n μ h)]

/-- (c) the `n`-block line average of a constant-per-direction field -/
theorem LCR_const (n : ℕ) (hn : 0 < n) (hdvd : ∀ ν, n ∣ L ν + 1) (c : Fin 3 → SuTwo)
    (z : PeriodicLatticeSite L) (hz : z ∈ CoarseLattice L n) (μ : Fin 3) :
    lineCoarseRestrictSuTwo n (fun b : Bond L => c b.2) (⟨z, hz⟩, μ) = c μ := by
  unfold lineCoarseRestrictSuTwo
  simp only [Finset.sum_const, Finset.card_range, card_blockOf_of_coarse hdvd hz]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← Nat.cast_smul_eq_nsmul ℝ (n ^ 3), smul_smul, ← Nat.cast_smul_eq_nsmul ℝ n, smul_smul]
  have h1 : 1 / (n : ℝ) ^ 4 * ((n ^ 3 : ℕ) : ℝ) * (n : ℝ) = 1 := by
    push_cast; field_simp
  rw [h1, one_smul]

#print axioms LCR_grad
#print axioms LCR_const

end AdalyFormal.GenuineU1
