import NuK1

/-!
# SoK1 -- the pattern competitor for general `ell`: definition, Z-average and transverse sums (lane sites_only_20261019)

`betaPat ell uE`: `-1/ell^2` on the whole slice `u₀ = uE + 1` and `+1` on the sites of the slice `u₀ = uE` with `u₁ ≡ u₂ ≡ ell - 1 (mod ell)` (`uE ≡ 0 mod ell`).
`Bpat ell uE`: the direction-`1` sigma_3 field with these coefficients; its transverse average is `zfield (gbar ell uE)`, `gbar ell uE = (1/ell^2)(δ_{uE} - δ_{uE+1})`.
(`ell = 2`: `NuK1.betaPat` with `% 2 = 1` and `-1/4`.)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.SitesOnly

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverOmega
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.SuTwoLogExp
open scoped Matrix RealInnerProductSpace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.NcwdhTwo

section
variable [CfData]
variable {L : PeriodicLatticeExtent}

/-- the coefficients of the pattern competitor. -/
noncomputable def betaPat (ell uE : ℕ) (u : PeriodicLatticeSite L) : ℝ :=
  (if (u 0).val = uE + 1 then (-1 / ((ell : ℝ) * ell) : ℝ) else 0) +
    (if (u 0).val = uE then (if (u 1).val % ell = ell - 1 ∧ (u 2).val % ell = ell - 1 then (1 : ℝ) else 0) else 0)

/-- the pattern competitor as a bond function. -/
noncomputable def Bpatf (ell uE : ℕ) : Bond L → SuTwo := fun b => if b.2 = 1 then dgS (betaPat ell uE b.1) else 0

/-- the pattern competitor: direction-1 sigma_3 field. -/
noncomputable def Bpat (ell uE : ℕ) : BondFnL2 L := WithLp.toLp 2 (Bpatf ell uE)

/-- its transverse average. -/
noncomputable def gbar (ell uE : ℕ) : ℕ → ℝ :=
  fun v => (if v = uE then (1 / ((ell : ℝ) * ell) : ℝ) else 0) - (if v = uE + 1 then (1 / ((ell : ℝ) * ell) : ℝ) else 0)

theorem Bpatf_sig (ell uE : ℕ) : SigB (Bpatf (L := L) ell uE) := by
  intro b
  unfold Bpatf
  split_ifs
  · exact diagP_dgS _
  · exact map_zero _

theorem Bpat_sig (ell uE : ℕ) : SigB (WithLp.ofLp (Bpat ell uE : BondFnL2 L)) := Bpatf_sig ell uE

theorem thetaOf_Bpatf (ell uE : ℕ) (x : PeriodicLatticeSite L) : thetaOf (Bpatf (L := L) ell uE) (x, 1) = betaPat ell uE x := by
  unfold thetaOf Bpatf
  simp only [if_true]
  rw [dgS_coe, fromM2_dg]
  rfl

theorem thetaOf_Bpat (ell uE : ℕ) (x : PeriodicLatticeSite L) :
    thetaOf (WithLp.ofLp (Bpat ell uE : BondFnL2 L)) (x, 1) = betaPat ell uE x :=
  thetaOf_Bpatf ell uE x

/-- `m` full residue classes mod `ell` contain `m` elements `≡ ell - 1`. -/
theorem sum_range_mod (ell : ℕ) (hell : 0 < ell) (m : ℕ) :
    ∑ v ∈ range (ell * m), (if v % ell = ell - 1 then (1 : ℝ) else 0) = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show ell * (m + 1) = ell * m + ell by ring, Finset.sum_range_add, ih]
    have : ∑ i ∈ range ell, (if (ell * m + i) % ell = ell - 1 then (1 : ℝ) else 0) = 1 := by
      rw [Finset.sum_eq_single (ell - 1)]
      · have h1 : (ell * m + (ell - 1)) % ell = ell - 1 := by
          rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)
        rw [if_pos h1]
      · intro i hi hne
        have hi' : i < ell := Finset.mem_range.mp hi
        have h1 : (ell * m + i) % ell = i := by rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hi'
        rw [if_neg (by rw [h1]; exact hne)]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    rw [this]; push_cast; ring

/-- the transverse sums of the pattern against a function of `u₀`:
`Σ_x β(x) g(x₀) = T Σ_v gbar v g v`, `T = (N₁)(N₂)`, for transverse sides divisible by `ell`. -/
theorem sum_betaPat (ell : ℕ) (hell : 0 < ell) (uE : ℕ) (huE : uE + 1 < L 0 + 1) (h1 : ell ∣ L 1 + 1) (h2 : ell ∣ L 2 + 1) (g : ℕ → ℝ) :
    ∑ x : PeriodicLatticeSite L, betaPat ell uE x * g (x 0).val =
      (((L 1 + 1) * (L 2 + 1) : ℕ) : ℝ) * ∑ v ∈ range (L 0 + 1), gbar ell uE v * g v := by
  obtain ⟨m1, hm1⟩ := h1
  obtain ⟨m2, hm2⟩ := h2
  have hsplit : ∀ x : PeriodicLatticeSite L, betaPat ell uE x * g (x 0).val =
      ((if (x 0).val = uE + 1 then (-1 / ((ell : ℝ) * ell) : ℝ) * g (x 0).val else 0) * 1 * 1) +
      (((if (x 0).val = uE then g (x 0).val else 0) * (if (x 1).val % ell = ell - 1 then (1 : ℝ) else 0)) *
        (if (x 2).val % ell = ell - 1 then (1 : ℝ) else 0)) := by
    intro x
    unfold betaPat
    by_cases a1 : (x 0).val = uE + 1
    · have a2 : (x 0).val ≠ uE := by omega
      simp [a1, a2]
    · by_cases a2 : (x 0).val = uE
      · simp only [a1, a2, if_false, if_true]
        by_cases b1 : (x 1).val % ell = ell - 1 <;> by_cases b2 : (x 2).val % ell = ell - 1 <;> simp [b1, b2]
      · simp [a1, a2]
  rw [Finset.sum_congr rfl (fun x _ => hsplit x), Finset.sum_add_distrib]
  have s1 := sum_site_prod L (fun v => if v = uE + 1 then (-1 / ((ell : ℝ) * ell) : ℝ) * g v else 0) (fun _ => 1) (fun _ => 1)
  have s2 := sum_site_prod L (fun v => if v = uE then g v else 0) (fun v => if v % ell = ell - 1 then (1 : ℝ) else 0)
    (fun v => if v % ell = ell - 1 then (1 : ℝ) else 0)
  rw [s1, s2]
  have c1 : ∑ v ∈ range (L 1 + 1), (if v % ell = ell - 1 then (1 : ℝ) else 0) = m1 := by rw [hm1]; exact sum_range_mod ell hell m1
  have c2 : ∑ v ∈ range (L 2 + 1), (if v % ell = ell - 1 then (1 : ℝ) else 0) = m2 := by rw [hm2]; exact sum_range_mod ell hell m2
  rw [c1, c2]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hT : (((L 1 + 1) * (L 2 + 1) : ℕ) : ℝ) = ((ell : ℝ) * m1) * ((ell : ℝ) * m2) := by
    rw [hm1, hm2]; push_cast; ring
  rw [hT]
  have gb : ∀ v, gbar ell uE v * g v = (if v = uE then (1 / ((ell : ℝ) * ell) : ℝ) * g v else 0) -
      (if v = uE + 1 then (1 / ((ell : ℝ) * ell) : ℝ) * g v else 0) := by
    intro v; unfold gbar; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun v _ => gb v), Finset.sum_sub_distrib]
  have sA : ∑ v ∈ range (L 0 + 1), (if v = uE + 1 then (-1 / ((ell : ℝ) * ell) : ℝ) * g v else 0) =
      if uE + 1 < L 0 + 1 then (-1 / ((ell : ℝ) * ell) : ℝ) * g (uE + 1) else 0 := by
    rw [Finset.sum_ite_eq']; simp [Finset.mem_range]
  have sB : ∑ v ∈ range (L 0 + 1), (if v = uE then g v else 0) = if uE < L 0 + 1 then g uE else 0 := by
    rw [Finset.sum_ite_eq']; simp [Finset.mem_range]
  have sC : ∑ v ∈ range (L 0 + 1), (if v = uE then (1 / ((ell : ℝ) * ell) : ℝ) * g v else 0) =
      if uE < L 0 + 1 then (1 / ((ell : ℝ) * ell) : ℝ) * g uE else 0 := by
    rw [Finset.sum_ite_eq']; simp [Finset.mem_range]
  have sD : ∑ v ∈ range (L 0 + 1), (if v = uE + 1 then (1 / ((ell : ℝ) * ell) : ℝ) * g v else 0) =
      if uE + 1 < L 0 + 1 then (1 / ((ell : ℝ) * ell) : ℝ) * g (uE + 1) else 0 := by
    rw [Finset.sum_ite_eq']; simp [Finset.mem_range]
  rw [sA, sB, sC, sD, if_pos huE, if_pos (show uE < L 0 + 1 by omega), if_pos (show uE < L 0 + 1 by omega), if_pos huE]
  rw [hm1, hm2]
  have hne : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  push_cast
  field_simp
  ring

end

#print axioms sum_betaPat

end AdalyFormal.SitesOnly
