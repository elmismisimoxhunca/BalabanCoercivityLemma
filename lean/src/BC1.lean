import FE5

/-!
# BC1 -- the SITE-composite drift `eps0` (the `hQdrift` premise of `ginv_coercive_FE_named2`) from the tower class

Pointwise telescoping of the genuine composite `Q'_{j+1}(U) = Q'(Ubar^j) Q'_j(U)` (`Qcomposite`, CMP99b (3.19) first line)
against its flat closed form `c^j Σ_{x ∈ B^j(y)} f x` (`c = ell^-3`, FE3 `Qcomposite_flat` shape):

  `‖Q'_j(U) f (y) - c^j Σ_{x∈B^j(y)} f x‖ ≤ d_j c^j Σ_{x∈B^j(y)} ‖f x‖`,   `d_{j+1} = d_j + 6 (ell-1) a_j`,
  where `a_j` bounds `‖Ubar^j(b) - 1‖_F` on the `ell^j`-aligned bonds (the tower class / `link_tower_na` shape).

Top level: `‖Qtop U f - Qtop 1 f‖ ≤ d_k · sqrt(1/n³) · ‖f‖`, `n = ell^k` (Schur / Cauchy-Schwarz over disjoint corner blocks).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.BondComposite

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SliceCoerc (coarseC Qtop GF)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf stepAverage Qcomposite Qcomposite_succ)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_mem_coarseLattice)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)
open AdalyFormal.Balaban.ClassPropagationUbar (card_stepBlockOf_le gammaPath_length_le)
open AdalyFormal.StatementLane (scaleUp)

theorem le_of_sq_le' {x B : ℝ} (hB : 0 ≤ B) (h : x ^ 2 ≤ B ^ 2) : x ≤ B := by
  by_contra hx
  push_neg at hx
  nlinarith [mul_pos (sub_pos.2 hx) (by linarith : 0 < x + B)]

section path
variable {L : PeriodicLatticeExtent}

/-- Displacement of an ALIGNED strided path holonomy: only the links the path visits (base points in the
`s`-aligned lattice, which the path never leaves) are assumed close to `1`. -/
theorem norm_RMap_coarseHol_sub_self_aligned {s : ℕ} (hdvd : ∀ μ : Fin 3, s ∣ (L μ + 1))
    (V : Cfg L) (X : SuTwo) (α : ℝ)
    (hV : ∀ y ∈ CoarseLattice L s, ∀ μ : Fin 3, ‖RMap (V (y, μ)) X - X‖ ≤ α) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L), y ∈ CoarseLattice L s →
      ‖RMap (coarsePathHolonomy s V y p) X - X‖ ≤ (p.length : ℝ) * α := by
  intro p
  induction p with
  | nil =>
    intro y _
    show ‖RMap 1 X - X‖ ≤ _
    rw [AdalyFormal.Balaban.CovariantOperators.RMap_one]
    simp
  | cons μ rest ih =>
    intro y hy
    have hrest := ih (coarseShift y s μ) (coarseShift_mem_coarseLattice hdvd hy μ)
    show ‖RMap (V (y, μ) * coarsePathHolonomy s V (coarseShift y s μ) rest) X - X‖ ≤ _
    refine le_trans (AdalyFormal.Balaban.TowerLawCov.norm_RMap_mul_sub_self_le _ _ X) ?_
    have h1 := hV y hy μ
    simp only [List.length_cons]
    push_cast
    linarith

end path

section composite
variable {L : PeriodicLatticeExtent}

/-- the isometry bound on the composite (no alignment, no smallness). -/
theorem norm_Qcomposite_le (bg : ℕ → Cfg L) (ell : ℕ) (hell : 0 < ell) (f : PeriodicLatticeSite L → SuTwo) :
    ∀ (j : ℕ) (y : PeriodicLatticeSite L),
      ‖Qcomposite bg ell j f y‖ ≤ ((1 / (ell : ℝ) ^ 3) ^ j) * ∑ x ∈ blockOf y (ell ^ j), ‖f x‖ := by
  intro j
  induction j with
  | zero =>
    intro y
    rw [pow_zero, pow_zero, one_mul, AdalyFormal.Balaban.QjComposite.blockOf_one_eq_singleton,
      Finset.sum_singleton]
    exact le_rfl
  | succ j ih =>
    intro y
    have hs : 0 < ell ^ j := pow_pos hell j
    have hc : (0 : ℝ) ≤ 1 / (ell : ℝ) ^ 3 := by positivity
    show ‖stepAverage (ell ^ j) (bg j) ell (Qcomposite bg ell j f) y‖ ≤ _
    unfold stepAverage
    rw [norm_smul, Real.norm_of_nonneg hc]
    have h1 : ‖∑ x ∈ stepBlockOf y (ell ^ j) ell,
        RMap (coarsePathHolonomy (ell ^ j) (bg j) y (coarseGammaPath (ell ^ j) y x)) (Qcomposite bg ell j f x)‖
        ≤ ∑ x ∈ stepBlockOf y (ell ^ j) ell, ((1 / (ell : ℝ) ^ 3) ^ j) * ∑ x' ∈ blockOf x (ell ^ j), ‖f x'‖ := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun x _ => ?_)
      rw [AdalyFormal.Balaban.TowerLawCov.norm_RMap]
      exact ih x
    have h2 : ∑ x ∈ stepBlockOf y (ell ^ j) ell, ((1 / (ell : ℝ) ^ 3) ^ j) * ∑ x' ∈ blockOf x (ell ^ j), ‖f x'‖
        = ((1 / (ell : ℝ) ^ 3) ^ j) * ∑ x' ∈ blockOf y (ell ^ (j + 1)), ‖f x'‖ := by
      rw [← Finset.mul_sum, AdalyFormal.FlatExt.sum_stepBlock_blockOf (ell ^ j) ell hs y (fun x' => ‖f x'‖), pow_succ ell j]
    calc 1 / (ell : ℝ) ^ 3 * ‖∑ x ∈ stepBlockOf y (ell ^ j) ell, _‖
        ≤ 1 / (ell : ℝ) ^ 3 * (((1 / (ell : ℝ) ^ 3) ^ j) * ∑ x' ∈ blockOf y (ell ^ (j + 1)), ‖f x'‖) :=
          mul_le_mul_of_nonneg_left (h2 ▸ h1) hc
      _ = _ := by rw [pow_succ (1 / (ell : ℝ) ^ 3) j]; ring

/-- **Pointwise telescoping.**  `d j = Σ_{i<j} 6 (ell-1) a i`. -/
def dsum (ell : ℕ) (a : ℕ → ℝ) (j : ℕ) : ℝ := ∑ i ∈ Finset.range j, 6 * ((ell : ℝ) - 1) * a i

theorem Qcomposite_drift_pointwise (bg : ℕ → Cfg L) (ell : ℕ) (hell : 0 < ell) (a : ℕ → ℝ) (K : ℕ)
    (hdvd : ∀ j, j ≤ K → ∀ μ : Fin 3, ell ^ j ∣ (L μ + 1))
    (hbg : ∀ j, j < K → ∀ y ∈ CoarseLattice L (ell ^ j), ∀ μ : Fin 3, frobNorm (((bg j (y, μ) : _) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ a j)
    (f : PeriodicLatticeSite L → SuTwo) :
    ∀ (j : ℕ), j ≤ K → ∀ y ∈ CoarseLattice L (ell ^ j),
      ‖Qcomposite bg ell j f y - ((1 / (ell : ℝ) ^ 3) ^ j) • ∑ x ∈ blockOf y (ell ^ j), f x‖
        ≤ dsum ell a j * (((1 / (ell : ℝ) ^ 3) ^ j) * ∑ x ∈ blockOf y (ell ^ j), ‖f x‖) := by
  intro j
  induction j with
  | zero =>
    intro _ y _
    rw [pow_zero, pow_zero, one_smul, one_mul, AdalyFormal.Balaban.QjComposite.blockOf_one_eq_singleton,
      Finset.sum_singleton, Finset.sum_singleton]
    show ‖f y - f y‖ ≤ _
    simp [dsum]
  | succ j ih =>
    intro hj y hy
    have hjK : j < K := hj
    have hs : 0 < ell ^ j := pow_pos hell j
    have hc : (0 : ℝ) ≤ 1 / (ell : ℝ) ^ 3 := by positivity
    have hell1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
    -- aligned: y ∈ Λ_j too
    have hyj : y ∈ CoarseLattice L (ell ^ j) := by
      rw [mem_CoarseLattice] at hy ⊢
      intro ν
      have := hy ν
      have hd : ell ^ j ∣ ell ^ (j + 1) := pow_dvd_pow ell (Nat.le_succ j)
      exact Nat.mod_eq_zero_of_dvd (dvd_trans hd (Nat.dvd_of_mod_eq_zero this))
    -- block sum bookkeeping
    set c : ℝ := 1 / (ell : ℝ) ^ 3 with hcdef
    set Q := Qcomposite bg ell j f with hQ
    set SB := stepBlockOf y (ell ^ j) ell with hSB
    set T : PeriodicLatticeSite L → SuTwo := fun x => c ^ j • ∑ x' ∈ blockOf x (ell ^ j), f x' with hT
    have hsum : ∑ x ∈ SB, T x = c ^ j • ∑ x' ∈ blockOf y (ell ^ (j + 1)), f x' := by
      rw [pow_succ ell j, ← AdalyFormal.FlatExt.sum_stepBlock_blockOf (ell ^ j) ell hs y (fun x' => f x'), Finset.smul_sum] <;> rfl
    have hdiff : Qcomposite bg ell (j + 1) f y - c ^ (j + 1) • ∑ x ∈ blockOf y (ell ^ (j + 1)), f x
        = c • ∑ x ∈ SB, ((RMap (coarsePathHolonomy (ell ^ j) (bg j) y (coarseGammaPath (ell ^ j) y x)) (Q x) - Q x)
              + (Q x - T x)) := by
      show stepAverage (ell ^ j) (bg j) ell Q y - _ = _
      unfold stepAverage
      rw [← hcdef]
      have : ∑ x ∈ SB, ((RMap (coarsePathHolonomy (ell ^ j) (bg j) y (coarseGammaPath (ell ^ j) y x)) (Q x) - Q x)
              + (Q x - T x))
            = ∑ x ∈ SB, RMap (coarsePathHolonomy (ell ^ j) (bg j) y (coarseGammaPath (ell ^ j) y x)) (Q x)
              - ∑ x ∈ SB, T x := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun x _ => by abel
      have e : c ^ (j + 1) = c * c ^ j := by ring
      rw [this, smul_sub, hsum, e, mul_smul]
    rw [hdiff, norm_smul, Real.norm_of_nonneg hc]
    have hterm : ∀ x ∈ SB,
        ‖(RMap (coarsePathHolonomy (ell ^ j) (bg j) y (coarseGammaPath (ell ^ j) y x)) (Q x) - Q x) + (Q x - T x)‖
          ≤ (6 * ((ell : ℝ) - 1) * a j + dsum ell a j) * (c ^ j * ∑ x' ∈ blockOf x (ell ^ j), ‖f x'‖) := by
      intro x hx
      have hxal : x ∈ CoarseLattice L (ell ^ j) := by
        rw [mem_CoarseLattice]
        intro ν
        have h := (mem_stepBlockOf.mp hx) ν
        have hy' := Nat.dvd_of_mod_eq_zero ((mem_CoarseLattice.mp hyj) ν)
        have h3 := h.2.2
        have hxy : (x ν).val = (y ν).val + ((x ν).val - (y ν).val) := by omega
        have : ell ^ j ∣ (x ν).val := by
          rw [hxy]
          exact dvd_add hy' h3
        exact Nat.mod_eq_zero_of_dvd this
      -- path displacement
      have hlen := gammaPath_length_le y x hs hx
      have hvis : ∀ z ∈ CoarseLattice L (ell ^ j), ∀ μ : Fin 3,
          ‖RMap (bg j (z, μ)) (Q x) - Q x‖ ≤ 2 * a j * ‖Q x‖ := by
        intro z hz μ
        refine le_trans (AdalyFormal.Balaban.RMapLipschitz.norm_RMap_sub_self_le (bg j (z, μ)) (Q x)) ?_
        have := hbg j hjK z hz μ
        nlinarith [norm_nonneg (Q x)]
      have hpath := norm_RMap_coarseHol_sub_self_aligned (hdvd j hjK.le) (bg j) (Q x) (2 * a j * ‖Q x‖) hvis
        (coarseGammaPath (ell ^ j) y x) y hyj
      have haj : 0 ≤ a j := by
        have := hbg j hjK y hyj 0
        exact le_trans (AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _) this
      have hlenR : ((coarseGammaPath (ell ^ j) y x).length : ℝ) ≤ 3 * ((ell : ℝ) - 1) := by
        have : ((coarseGammaPath (ell ^ j) y x).length : ℝ) ≤ ((3 * (ell - 1) : ℕ) : ℝ) := by exact_mod_cast hlen
        rw [Nat.cast_mul, Nat.cast_sub hell] at this
        simpa using this
      have hQx := norm_Qcomposite_le bg ell hell f j x
      have hd0 : 0 ≤ dsum ell a j := by
        unfold dsum
        exact Finset.sum_nonneg fun i hi => by
          have hiK : i < K := lt_of_lt_of_le (Finset.mem_range.mp hi) hjK.le
          have hh : 0 ≤ a i := le_trans (AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _)
            (hbg i hiK 0 (by rw [mem_CoarseLattice]; intro ν; simp) 0)
          have : (0 : ℝ) ≤ (ell : ℝ) - 1 := by linarith
          positivity
      have hih := ih hjK.le x hxal
      have hA : ‖RMap (coarsePathHolonomy (ell ^ j) (bg j) y (coarseGammaPath (ell ^ j) y x)) (Q x) - Q x‖
          ≤ 6 * ((ell : ℝ) - 1) * a j * (c ^ j * ∑ x' ∈ blockOf x (ell ^ j), ‖f x'‖) := by
        refine le_trans hpath ?_
        have h2a : 0 ≤ 2 * a j * ‖Q x‖ := by positivity
        calc ((coarseGammaPath (ell ^ j) y x).length : ℝ) * (2 * a j * ‖Q x‖)
            ≤ (3 * ((ell : ℝ) - 1)) * (2 * a j * ‖Q x‖) := mul_le_mul_of_nonneg_right hlenR h2a
          _ = 6 * ((ell : ℝ) - 1) * a j * ‖Q x‖ := by ring
          _ ≤ 6 * ((ell : ℝ) - 1) * a j * (c ^ j * ∑ x' ∈ blockOf x (ell ^ j), ‖f x'‖) := by
              refine mul_le_mul_of_nonneg_left hQx ?_
              have : (0 : ℝ) ≤ (ell : ℝ) - 1 := by linarith
              positivity
      refine le_trans (norm_add_le _ _) ?_
      have hB : ‖Q x - T x‖ ≤ dsum ell a j * (c ^ j * ∑ x' ∈ blockOf x (ell ^ j), ‖f x'‖) := hih
      linarith
    have hsumle : ‖∑ x ∈ SB, ((RMap (coarsePathHolonomy (ell ^ j) (bg j) y (coarseGammaPath (ell ^ j) y x)) (Q x) - Q x)
              + (Q x - T x))‖
        ≤ (6 * ((ell : ℝ) - 1) * a j + dsum ell a j) * (c ^ j * ∑ x' ∈ blockOf y (ell ^ (j + 1)), ‖f x'‖) := by
      refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum hterm) ?_)
      rw [← Finset.mul_sum, ← Finset.mul_sum,
        AdalyFormal.FlatExt.sum_stepBlock_blockOf (ell ^ j) ell hs y (fun x' => ‖f x'‖), pow_succ ell j]
    have hd : dsum ell a (j + 1) = 6 * ((ell : ℝ) - 1) * a j + dsum ell a j := by
      unfold dsum; rw [Finset.sum_range_succ]; ring
    rw [hd]
    calc c * ‖∑ x ∈ SB, _‖
        ≤ c * ((6 * ((ell : ℝ) - 1) * a j + dsum ell a j) * (c ^ j * ∑ x' ∈ blockOf y (ell ^ (j + 1)), ‖f x'‖)) :=
          mul_le_mul_of_nonneg_left hsumle hc
      _ = _ := by rw [pow_succ c j]; ring

end composite

#print axioms norm_RMap_coarseHol_sub_self_aligned
#print axioms norm_Qcomposite_le
#print axioms Qcomposite_drift_pointwise

end AdalyFormal.BondComposite
