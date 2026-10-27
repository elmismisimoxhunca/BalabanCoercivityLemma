import UW5

/-!
# UW6 -- the clause-2 stacking step, part 2: velocity field, profile, final gauge (lane unif_20261016)

`vf_*` : `|Vf| ≤ VB = o1 + n1`, plane differences `≤ Dv = 2 (o2 + g02)`; `clampP` (projection of `ℤ³` onto the plane box,
1-Lipschitz in each coordinate) and `fh = Vf ∘ clampP` (globally defined, plane differences `≤ Dv`); `Fz p = Φ(t(p), bp p)` with
`Φ` the profile of `UW3` built from the plane averages of `fh`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.UnifLane.Z

open Matrix
open AdalyFormal.M2Glue3 (Z3 ev)
open AdalyFormal.M2Glue2 (frobNorm_sub_le' frobNorm_sub_comm frobNorm_su2_mul frobNorm_mul_su2 gauge_step_one
  gauge_step_two icay cay acos2 acos2_nonneg cay_icay frobNorm_icay_sub_le frobNorm_icay_le isSu2_icay frobNorm_mul_le)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 coe_mul coe_inv coe_one)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.Bch2 (frobNorm_add_le frobNorm_nonneg frobNorm_smul IsSu2)
open AdalyFormal.Balaban.RegularityGap (frobNorm_neg)

/-- the projection of `ℤ³` onto the plane box. -/
def clampP (σ : Fin 3) (c : ℤ) (lo hi : Z3) (y : Z3) : Z3 :=
  fun ν => if ν = σ then c else max (lo ν) (min (hi ν) (y ν))

theorem clampP_mem (σ : Fin 3) (c ch : ℤ) (hch : c < ch) (lo hi : Z3) (hlh : ∀ ν, ν ≠ σ → lo ν ≤ hi ν) (y : Z3) :
    clampP σ c lo hi y ∈ SlabS σ lo hi c ch ∧ (clampP σ c lo hi y) σ = c := by
  refine ⟨⟨fun ν hν => ?_, by simp [clampP], by simp [clampP]; exact hch⟩, by simp [clampP]⟩
  simp only [clampP, if_neg hν]
  have := hlh ν hν
  constructor <;> omega

theorem clampP_of_mem {σ : Fin 3} {c : ℤ} {lo hi : Z3} {x : Z3} (hx : TrB σ lo hi x) (hxc : x σ = c) :
    clampP σ c lo hi x = x := by
  funext ν
  by_cases hν : ν = σ
  · subst hν; simp [clampP, hxc]
  · simp only [clampP, if_neg hν]; have := hx ν hν; omega

theorem clampP_add_self (σ : Fin 3) (c : ℤ) (lo hi : Z3) (y : Z3) : clampP σ c lo hi (y + ev σ) = clampP σ c lo hi y := by
  funext ν
  by_cases hν : ν = σ
  · subst hν; simp [clampP]
  · simp [clampP, hν, ev_apply_ne hν]

theorem clampP_add_ne (σ : Fin 3) (c : ℤ) (lo hi : Z3) (y : Z3) {τ : Fin 3} (hτ : τ ≠ σ) :
    clampP σ c lo hi (y + ev τ) = clampP σ c lo hi y ∨ clampP σ c lo hi (y + ev τ) = clampP σ c lo hi y + ev τ := by
  by_cases h : max (lo τ) (min (hi τ) (y τ + 1)) = max (lo τ) (min (hi τ) (y τ))
  · left; funext ν
    by_cases hν : ν = σ
    · subst hν; simp [clampP]
    · by_cases hντ : ν = τ
      · subst hντ; simp only [clampP, if_neg hν, Pi.add_apply, ev_apply_self]; exact h
      · simp [clampP, hν, ev_apply_ne hντ]
  · right; funext ν
    by_cases hν : ν = σ
    · subst hν; simp [clampP, ev_apply_ne (Ne.symm hτ)]
    · by_cases hντ : ν = τ
      · subst hντ; simp only [clampP, if_neg hν, Pi.add_apply, ev_apply_self]; omega
      · simp [clampP, hν, ev_apply_ne hντ]

theorem isSu2_finsum {ι : Type*} (s : Finset ι) (g : ι → M2) (h : ∀ i, IsSu2 (g i)) : IsSu2 (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using AdalyFormal.Balaban.Bch2.IsSu2.zero
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih

theorem isSu2_av {τ : Fin 3} {n : ℕ} {f : Z3 → M2} (h : ∀ y, IsSu2 (f y)) (x : Z3) : IsSu2 (Av τ n f x) :=
  (isSu2_finsum _ _ (fun k => h _)).smul _

theorem av_zero_radius (τ : Fin 3) (f : Z3 → M2) (x : Z3) : Av τ 0 f x = f x := by
  simp [Av]

end AdalyFormal.UnifLane.Z
