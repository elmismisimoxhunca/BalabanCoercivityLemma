import MX_Base

/-!
# MX_Orig -- the ORIGINAL-bound mixed class (lane mixed_20261017)

`PerCubeRegularΦ ell M Φ k S α η U := ∀ f ∈ Φ, PerCubeRegular2 ell M f k S α η U` : every class cube of factor `f ∈ Φ` is regular with ITS OWN printed bound `f M α (ell^j η)^{-n}`
(the r8 definition `PerCubeRegular2`, verbatim, at each admitted factor).  `ClassCoupledΦ := CoversOmΦ ∧ PerCubeRegularΦ`.
`classCoupledΦ_single` : `Φ = {c}` is `ClassCoupled ell M c`.  `ClassCoupledΦ.toHΦ` : under per-cube smallness `f M α ≤ 12 M α'` it is the hybrid class of bound factor 12 at `α'`.
-/
set_option autoImplicit false

namespace MXP.AllC

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2

def PerCubeRegularΦ {L : PeriodicLatticeExtent} (ell M : ℕ) (Φ : Set ℕ) (k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  ∀ f ∈ Φ, PerCubeRegular2 ell M f k S α₀ η U

def ClassCoupledΦ {L : PeriodicLatticeExtent} (ell M : ℕ) (Φ : Set ℕ) (k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  CoversOmΦ ell M Φ k S ∧ PerCubeRegularΦ ell M Φ k S α₀ η U

theorem coversΦ_single {L : PeriodicLatticeExtent} {ell M c k : ℕ} {S : Tower L} :
    CoversOmΦ ell M ({c} : Set ℕ) k S ↔ CoversOm0p ell M c k S := by
  unfold CoversOmΦ CoversOmcΦ CoversPlaqΦ
    AdalyFormal.StatementLane2.CoversOm0p AdalyFormal.StatementLane2.CoversOm0c AdalyFormal.StatementLane2.CoversPlaqOm0c
  simp only [isClassCubeΦ_single]

theorem classCoupledΦ_single {L : PeriodicLatticeExtent} {ell M c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L} :
    ClassCoupledΦ ell M ({c} : Set ℕ) k S α₀ η U ↔ ClassCoupled ell M c k S α₀ η U := by
  unfold ClassCoupledΦ PerCubeRegularΦ ClassCoupled
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨coversΦ_single.1 h1, h2 c rfl⟩
  · rintro ⟨h1, h2⟩
    exact ⟨coversΦ_single.2 h1, fun f hf => by rw [Set.mem_singleton_iff] at hf; subst hf; exact h2⟩

theorem ClassCoupledΦ.toHΦ {L : PeriodicLatticeExtent} {ell M k : ℕ} {Φ : Set ℕ} [CubeFactorSet Φ] {S : Tower L} {α₀ α' η : ℝ} {U : LinkCfg L}
    (hM : 0 < M) (hη : 0 ≤ η) (hsm : ∀ f ∈ Φ, (f : ℝ) * M * α₀ ≤ ((12 : ℕ) : ℝ) * M * α')
    (h : ClassCoupledΦ ell M Φ k S α₀ η U) : ClassCoupledHΦ ell M Φ 12 k S α' η U := by
  refine ⟨h.1, fun f hf => ?_⟩
  have h1 := AdalyFormal.AllC.PerCubeRegular2.toH' (b := 12) (by norm_num) (h.2 f hf)
  refine AdalyFormal.AllC.PerCubeRegular2H.mono hη ?_ h1
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have := hsm f hf
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < ((12 : ℕ) : ℝ))]
  have h2 : (f : ℝ) * α₀ * M ≤ α' * ((12 : ℕ) : ℝ) * M := by nlinarith
  exact le_of_mul_le_mul_right h2 hMr

end MXP.AllC

#print axioms MXP.AllC.classCoupledΦ_single
#print axioms MXP.AllC.ClassCoupledΦ.toHΦ
