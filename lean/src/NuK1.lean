import NuG3
import NtCvO43

/-!
# NuK1 -- the pattern competitor on the unit lattice: definition, Z-average and transverse sums (lane ncwdh_ell2_20261018)

`betaPat uE`: `-1/4` on the whole slice `u₀ = uE + 1` and `+1` on the sites of the slice `u₀ = uE` with `u₁, u₂` both odd (`uE` even).
`Bpat uE`: the direction-1 sigma_3 field with these coefficients; its transverse average is `zfield (gbar uE)`, `gbar uE = (1/4)(δ_{uE} - δ_{uE+1})`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverOmega
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.SuTwoLogExp
open scoped Matrix RealInnerProductSpace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

section
variable [CfData]
variable {L : PeriodicLatticeExtent}

theorem sum_site_prod (L : PeriodicLatticeExtent) (φ0 φ1 φ2 : ℕ → ℝ) :
    ∑ x : PeriodicLatticeSite L, φ0 (x 0).val * φ1 (x 1).val * φ2 (x 2).val =
      (∑ v ∈ range (L 0 + 1), φ0 v) * (∑ v ∈ range (L 1 + 1), φ1 v) * (∑ v ∈ range (L 2 + 1), φ2 v) := by
  let F : (i : Fin 3) → Fin (L i + 1) → ℝ := fun i a =>
    if i = 0 then φ0 a.val else if i = 1 then φ1 a.val else φ2 a.val
  have hpt : ∀ x : PeriodicLatticeSite L, φ0 (x 0).val * φ1 (x 1).val * φ2 (x 2).val = ∏ i : Fin 3, F i (x i) := by
    intro x
    rw [Fin.prod_univ_three]
    simp [F]
  rw [Finset.sum_congr rfl (fun x _ => hpt x), ← Fintype.prod_sum F, Fin.prod_univ_three]
  have e0 : ∑ a : Fin (L 0 + 1), F 0 a = ∑ v ∈ range (L 0 + 1), φ0 v := by
    simp only [F, if_true]; exact Fin.sum_univ_eq_sum_range φ0 _
  have e1 : ∑ a : Fin (L 1 + 1), F 1 a = ∑ v ∈ range (L 1 + 1), φ1 v := by
    simp only [F, if_neg (show ¬ ((1 : Fin 3) = 0) by decide), if_true]; exact Fin.sum_univ_eq_sum_range φ1 _
  have e2 : ∑ a : Fin (L 2 + 1), F 2 a = ∑ v ∈ range (L 2 + 1), φ2 v := by
    simp only [F, if_neg (show ¬ ((2 : Fin 3) = 0) by decide), if_neg (show ¬ ((2 : Fin 3) = 1) by decide)]
    exact Fin.sum_univ_eq_sum_range φ2 _
  rw [e0, e1, e2]

theorem sum_range_odd (m : ℕ) : ∑ v ∈ range (2 * m), (if v % 2 = 1 then (1 : ℝ) else 0) = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h1 : (2 * m) % 2 = 0 := by omega
    have h2 : (2 * m + 1) % 2 = 1 := by omega
    rw [if_neg (by omega), if_pos h2]; push_cast; ring

/-- the coefficients of the pattern competitor. -/
noncomputable def betaPat (uE : ℕ) (u : PeriodicLatticeSite L) : ℝ :=
  (if (u 0).val = uE + 1 then (-1 / 4 : ℝ) else 0) +
    (if (u 0).val = uE then (if (u 1).val % 2 = 1 ∧ (u 2).val % 2 = 1 then (1 : ℝ) else 0) else 0)

/-- the pattern competitor as a bond function. -/
noncomputable def Bpatf (uE : ℕ) : Bond L → SuTwo := fun b => if b.2 = 1 then dgS (betaPat uE b.1) else 0

/-- the pattern competitor: direction-1 sigma_3 field. -/
noncomputable def Bpat (uE : ℕ) : BondFnL2 L := WithLp.toLp 2 (Bpatf uE)

/-- its transverse average. -/
noncomputable def gbar (uE : ℕ) : ℕ → ℝ := fun v => (if v = uE then (1 / 4 : ℝ) else 0) - (if v = uE + 1 then (1 / 4 : ℝ) else 0)

theorem Bpatf_sig (uE : ℕ) : SigB (Bpatf (L := L) uE) := by
  intro b
  unfold Bpatf
  split_ifs
  · exact diagP_dgS _
  · exact map_zero _

theorem Bpat_sig (uE : ℕ) : SigB (WithLp.ofLp (Bpat uE : BondFnL2 L)) := Bpatf_sig uE

theorem thetaOf_Bpatf (uE : ℕ) (x : PeriodicLatticeSite L) : thetaOf (Bpatf (L := L) uE) (x, 1) = betaPat uE x := by
  unfold thetaOf Bpatf
  simp only [if_true]
  rw [dgS_coe, fromM2_dg]
  rfl

theorem thetaOf_Bpat (uE : ℕ) (x : PeriodicLatticeSite L) : thetaOf (WithLp.ofLp (Bpat uE : BondFnL2 L)) (x, 1) = betaPat uE x :=
  thetaOf_Bpatf uE x

/-- the transverse sums of the pattern against a function of `u₀`:
`Σ_x β(x) g(x₀) = T Σ_v gbar v g v`, `T = (N₁)(N₂)`, for even transverse sides. -/
theorem sum_betaPat (uE : ℕ) (huE : uE + 1 < L 0 + 1) (h1 : 2 ∣ L 1 + 1) (h2 : 2 ∣ L 2 + 1) (g : ℕ → ℝ) :
    ∑ x : PeriodicLatticeSite L, betaPat uE x * g (x 0).val =
      (((L 1 + 1) * (L 2 + 1) : ℕ) : ℝ) * ∑ v ∈ range (L 0 + 1), gbar uE v * g v := by
  obtain ⟨m1, hm1⟩ := h1
  obtain ⟨m2, hm2⟩ := h2
  have hsplit : ∀ x : PeriodicLatticeSite L, betaPat uE x * g (x 0).val =
      ((if (x 0).val = uE + 1 then (-1 / 4 : ℝ) * g (x 0).val else 0) * 1 * 1) +
      (((if (x 0).val = uE then g (x 0).val else 0) * (if (x 1).val % 2 = 1 then (1 : ℝ) else 0)) *
        (if (x 2).val % 2 = 1 then (1 : ℝ) else 0)) := by
    intro x
    unfold betaPat
    by_cases a1 : (x 0).val = uE + 1
    · have a2 : (x 0).val ≠ uE := by omega
      simp [a1, a2]
    · by_cases a2 : (x 0).val = uE
      · simp only [a1, a2, if_false, if_true]
        by_cases b1 : (x 1).val % 2 = 1 <;> by_cases b2 : (x 2).val % 2 = 1 <;> simp [b1, b2]
      · simp [a1, a2]
  rw [Finset.sum_congr rfl (fun x _ => hsplit x), Finset.sum_add_distrib]
  have s1 := sum_site_prod L (fun v => if v = uE + 1 then (-1 / 4 : ℝ) * g v else 0) (fun _ => 1) (fun _ => 1)
  have s2 := sum_site_prod L (fun v => if v = uE then g v else 0) (fun v => if v % 2 = 1 then (1 : ℝ) else 0)
    (fun v => if v % 2 = 1 then (1 : ℝ) else 0)
  rw [s1, s2]
  have c1 : ∑ v ∈ range (L 1 + 1), (if v % 2 = 1 then (1 : ℝ) else 0) = m1 := by rw [hm1]; exact sum_range_odd m1
  have c2 : ∑ v ∈ range (L 2 + 1), (if v % 2 = 1 then (1 : ℝ) else 0) = m2 := by rw [hm2]; exact sum_range_odd m2
  rw [c1, c2]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hT : (((L 1 + 1) * (L 2 + 1) : ℕ) : ℝ) = (2 * m1 : ℝ) * (2 * m2 : ℝ) := by
    rw [hm1, hm2]; push_cast; ring
  rw [hT]
  have gb : ∀ v, gbar uE v * g v = (if v = uE then (1 / 4 : ℝ) * g v else 0) - (if v = uE + 1 then (1 / 4 : ℝ) * g v else 0) := by
    intro v; unfold gbar; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun v _ => gb v), Finset.sum_sub_distrib]
  have sA : ∑ v ∈ range (L 0 + 1), (if v = uE + 1 then (-1 / 4 : ℝ) * g v else 0) =
      if uE + 1 < L 0 + 1 then (-1 / 4 : ℝ) * g (uE + 1) else 0 := by
    rw [Finset.sum_ite_eq']; simp [Finset.mem_range]
  have sB : ∑ v ∈ range (L 0 + 1), (if v = uE then g v else 0) = if uE < L 0 + 1 then g uE else 0 := by
    rw [Finset.sum_ite_eq']; simp [Finset.mem_range]
  have sC : ∑ v ∈ range (L 0 + 1), (if v = uE then (1 / 4 : ℝ) * g v else 0) = if uE < L 0 + 1 then (1 / 4 : ℝ) * g uE else 0 := by
    rw [Finset.sum_ite_eq']; simp [Finset.mem_range]
  have sD : ∑ v ∈ range (L 0 + 1), (if v = uE + 1 then (1 / 4 : ℝ) * g v else 0) =
      if uE + 1 < L 0 + 1 then (1 / 4 : ℝ) * g (uE + 1) else 0 := by
    rw [Finset.sum_ite_eq']; simp [Finset.mem_range]
  rw [sA, sB, sC, sD, if_pos huE, if_pos (show uE < L 0 + 1 by omega), if_pos (show uE < L 0 + 1 by omega), if_pos huE]
  rw [hm1, hm2]
  push_cast
  ring

end

end AdalyFormal.NcwdhTwo
