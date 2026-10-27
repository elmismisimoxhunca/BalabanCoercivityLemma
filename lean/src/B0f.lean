import B0e

/-!
# B0f -- the level-gauge jets ARE the composite averaging `Q'_j λ` at lattice points

`OnLat m y`: every coordinate of `y` is a multiple of `m`.
`dG_eq_Qcomposite`: if `0 < ell`, `ell^J ∣ L μ + 1` for all `μ`, `j ≤ J` and `y` is on the `ell^j`-lattice, then
`dG ell bg λ j y = (Qcomposite bg ell j λ y : M2)` (CMP99b (3.19), tree `QjComposite.Qcomposite`).
The only geometric inputs: `card (stepBlockOf y (ell^j) ell) = ell^3` (`QjComposite.card_stepBlockOf`, needs the box
to fit, i.e. no wrap) and that block sites of a lattice point are lattice points one level down.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.SliceCoerc

open scoped Matrix Matrix.Norms.Frobenius
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp (M2 SU2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwo mem_suTwo_iff RMap RMap_coe_apply)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf card_stepBlockOf Qcomposite stepAverage)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)

variable {L : PeriodicLatticeExtent}

/-- `y` lies on the `m`-strided sublattice. -/
def OnLat (m : ℕ) (y : PeriodicLatticeSite L) : Prop := ∀ μ : Fin 3, m ∣ (y μ).val

theorem nat_fit {a y M : ℕ} (ha : a ∣ y) (hM : a ∣ M) (hy : y < M) : y + a ≤ M := by
  obtain ⟨p, rfl⟩ := ha
  obtain ⟨q, rfl⟩ := hM
  have hpq : p + 1 ≤ q := Nat.lt_of_mul_lt_mul_left hy
  have h2 := Nat.mul_le_mul_left a hpq
  rw [Nat.mul_succ] at h2
  exact h2

theorem block_onLat (ell j : ℕ) {y x : PeriodicLatticeSite L} (hy : OnLat (ell ^ (j + 1)) y)
    (hx : x ∈ stepBlockOf y (ell ^ j) ell) : OnLat (ell ^ j) x ∧ OnLat (ell ^ j) y := by
  have hy' : OnLat (ell ^ j) y := fun μ => (pow_dvd_pow ell (Nat.le_succ j)).trans (hy μ)
  refine ⟨fun μ => ?_, hy'⟩
  have h := (mem_stepBlockOf.mp hx) μ
  have : (x μ).val = (y μ).val + ((x μ).val - (y μ).val) := by omega
  rw [this]
  exact Nat.dvd_add (hy' μ) h.2.2

theorem avg_identity {ι : Type*} (B : Finset ι) (c : ℝ) (hc : (B.card : ℝ) * c = 1) (v : M2)
    (hv : vᴴ = -v) (H w : ι → M2) (hw : ∀ x ∈ B, (w x)ᴴ = -w x) :
    (∑ x ∈ B, c • (v - H x * w x * (H x)ᴴ))ᴴ + v = c • ∑ x ∈ B, H x * w x * (H x)ᴴ := by
  rw [Matrix.conjTranspose_sum]
  have hterm : ∀ x ∈ B, (c • (v - H x * w x * (H x)ᴴ))ᴴ = c • (H x * w x * (H x)ᴴ) - c • v := by
    intro x hx
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hw x hx, hv, ← smul_sub]
    congr 1
    noncomm_ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, ← Finset.smul_sum,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hc, one_smul]
  abel

theorem dG_eq_Qcomposite (ell : ℕ) (hell : 0 < ell) (bg : ℕ → PeriodicLinkConfiguration SU2 L)
    (lam : PeriodicLatticeSite L → SuTwo) (J : ℕ) (hdiv : ∀ μ : Fin 3, ell ^ J ∣ L μ + 1) :
    ∀ j, j ≤ J → ∀ y : PeriodicLatticeSite L, OnLat (ell ^ j) y →
      dG ell bg lam j y = ((Qcomposite bg ell j lam y : SuTwo) : M2) := by
  intro j
  induction j with
  | zero => intro _ y _; rfl
  | succ j ih =>
      intro hj y hy
      have hB : ∀ x ∈ stepBlockOf y (ell ^ j) ell,
          dG ell bg lam j x = ((Qcomposite bg ell j lam x : SuTwo) : M2) :=
        fun x hx => ih (by omega) x (block_onLat ell j hy hx).1
      have hyj : dG ell bg lam j y = ((Qcomposite bg ell j lam y : SuTwo) : M2) :=
        ih (by omega) y (fun μ => (pow_dvd_pow ell (Nat.le_succ j)).trans (hy μ))
      have hfit : ∀ μ, (y μ).val + ell ^ j * ell ≤ L μ + 1 := by
        intro μ
        rw [← pow_succ]
        exact nat_fit (hy μ) ((pow_dvd_pow ell hj).trans (hdiv μ)) (y μ).isLt
      have hcard := card_stepBlockOf y (ell ^ j) ell (pow_pos hell j) hfit
      have hah : ∀ z : SuTwo, ((z : M2))ᴴ = -(z : M2) := fun z => ((mem_suTwo_iff _).mp z.2).1
      have hc : ((stepBlockOf y (ell ^ j) ell).card : ℝ) * ((ell : ℝ) ^ 3)⁻¹ = 1 := by
        rw [hcard]; push_cast
        have hne : ((ell : ℝ) ^ 3) ≠ 0 := by positivity
        exact mul_inv_cancel₀ hne
      show (∑ x ∈ stepBlockOf y (ell ^ j) ell, ((ell : ℝ) ^ 3)⁻¹ •
          (dG ell bg lam j y - ((coarsePathHolonomy (ell ^ j) (bg j) y (coarseGammaPath (ell ^ j) y x) : SU2) : M2)
            * dG ell bg lam j x
            * ((coarsePathHolonomy (ell ^ j) (bg j) y (coarseGammaPath (ell ^ j) y x) : SU2) : M2)ᴴ))ᴴ
          + dG ell bg lam j y = ((stepAverage (ell ^ j) (bg j) ell (Qcomposite bg ell j lam) y : SuTwo) : M2)
      rw [Finset.sum_congr rfl (fun x hx => by rw [hB x hx]), hyj]
      rw [avg_identity _ _ hc _ (hah _) (fun x => ((coarsePathHolonomy (ell ^ j) (bg j) y
        (coarseGammaPath (ell ^ j) y x) : SU2) : M2)) (fun x => ((Qcomposite bg ell j lam x : SuTwo) : M2))
        (fun x _ => hah _)]
      unfold stepAverage
      rw [Submodule.coe_smul, Submodule.coe_sum, one_div]
      simp only [RMap_coe_apply]

#print axioms nat_fit
#print axioms block_onLat
#print axioms avg_identity
#print axioms dG_eq_Qcomposite

end AdalyFormal.SliceCoerc
