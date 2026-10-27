import NsCvO7

/-!
# CvO10 -- truncated stride-1 blocks (lane omega)

`stepBlockOf z 1 ell` is NOT cut to size at the torus end: it is `{x | z ≤ x < z + ell}` as natural numbers, so it is truncated near the
end of the torus.  Sums over it of functions of the `1`-coordinate offset factorise:
`Σ_{x ∈ B(z)} g((x₁) - z₁) = cnt₀ · cnt₂ · Σ_{n < min ell (N₁ - z₁)} g n` with `cnt_μ = min ell (N_μ - z_μ)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)

variable {L : PeriodicLatticeExtent}

theorem sum_fin_window (N y ell : ℕ) (g : ℕ → ℝ) :
    ∑ a : Fin N, (if y ≤ a.val ∧ a.val < y + ell then g (a.val - y) else 0) =
      ∑ n ∈ Finset.range (min ell (N - y)), g n := by
  rw [Fin.sum_univ_eq_sum_range (fun a => if y ≤ a ∧ a < y + ell then g (a - y) else 0) N]
  rw [← Finset.sum_filter]
  have hset : (Finset.range N).filter (fun a => y ≤ a ∧ a < y + ell) = Finset.Ico y (min (y + ell) N) := by
    ext a; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, lt_min_iff]; omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  have : min (y + ell) N - y = min ell (N - y) := by omega
  rw [this]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  congr 1; omega

theorem sum_block_one (z : PeriodicLatticeSite L) (ell : ℕ) (g : ℕ → ℝ) :
    ∑ x ∈ stepBlockOf z 1 ell, g ((x 1).val - (z 1).val) =
      ((min ell (L 0 + 1 - (z 0).val) : ℕ) : ℝ) * ((min ell (L 2 + 1 - (z 2).val) : ℕ) : ℝ) *
        ∑ n ∈ Finset.range (min ell (L 1 + 1 - (z 1).val)), g n := by
  classical
  have hmem : ∀ x : PeriodicLatticeSite L, x ∈ stepBlockOf z 1 ell ↔
      ∀ μ : Fin 3, (z μ).val ≤ (x μ).val ∧ (x μ).val < (z μ).val + ell := by
    intro x
    rw [mem_stepBlockOf]
    constructor
    · intro h μ; have := h μ; exact ⟨this.1, by simpa using this.2.1⟩
    · intro h μ; have := h μ; exact ⟨this.1, by simpa using this.2, one_dvd _⟩
  let F : (i : Fin 3) → Fin (L i + 1) → ℝ := fun i a =>
    if i = 1 then (if (z i).val ≤ a.val ∧ a.val < (z i).val + ell then g (a.val - (z i).val) else 0)
    else (if (z i).val ≤ a.val ∧ a.val < (z i).val + ell then 1 else 0)
  have hpt : ∀ x : PeriodicLatticeSite L, (if x ∈ stepBlockOf z 1 ell then g ((x 1).val - (z 1).val) else 0) =
      ∏ i : Fin 3, F i (x i) := by
    intro x
    rw [Fin.prod_univ_three]
    simp only [F]
    by_cases h : x ∈ stepBlockOf z 1 ell
    · have h' := (hmem x).mp h
      rw [if_pos h]
      simp [h' 0, h' 1, h' 2]
    · rw [if_neg h]
      have : ¬ (∀ μ : Fin 3, (z μ).val ≤ (x μ).val ∧ (x μ).val < (z μ).val + ell) := fun h2 => h ((hmem x).mpr h2)
      push Not at this
      obtain ⟨μ, hμ⟩ := this
      have hnot : ¬ ((z μ).val ≤ (x μ).val ∧ (x μ).val < (z μ).val + ell) := fun h3 => by
        have := hμ h3.1; omega
      fin_cases μ <;> simp_all
  have h1 : ∑ x ∈ stepBlockOf z 1 ell, g ((x 1).val - (z 1).val) =
      ∑ x : PeriodicLatticeSite L, ∏ i : Fin 3, F i (x i) := by
    rw [← Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_ite_mem, Finset.univ_inter]
  rw [h1, ← Fintype.prod_sum F, Fin.prod_univ_three]
  have e0 : ∑ a : Fin (L 0 + 1), F 0 a = ((min ell (L 0 + 1 - (z 0).val) : ℕ) : ℝ) := by
    have := sum_fin_window (L 0 + 1) (z 0).val ell (fun _ => (1 : ℝ))
    simp only [F, if_neg (show ¬ ((0 : Fin 3) = 1) by decide)]
    rw [this]; simp
  have e1 : ∑ a : Fin (L 1 + 1), F 1 a = ∑ n ∈ Finset.range (min ell (L 1 + 1 - (z 1).val)), g n := by
    have := sum_fin_window (L 1 + 1) (z 1).val ell g
    simp only [F, if_true]
    exact this
  have e2 : ∑ a : Fin (L 2 + 1), F 2 a = ((min ell (L 2 + 1 - (z 2).val) : ℕ) : ℝ) := by
    have := sum_fin_window (L 2 + 1) (z 2).val ell (fun _ => (1 : ℝ))
    simp only [F, if_neg (show ¬ ((2 : Fin 3) = 1) by decide)]
    rw [this]; simp
  rw [e0, e1, e2]; ring



open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge loopVar coarseBondVar gammaVarStrided cPlusS cPlusS_eq)

theorem sum_odd_even' (m : ℕ) (a : ℝ) : ∑ n ∈ Finset.range m, (if n % 2 = 0 then (0 : ℝ) else a) = ((m / 2 : ℕ) : ℝ) * a := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · rw [sum_odd_even]; congr 2; omega
  · rw [Finset.sum_range_succ, sum_odd_even]
    have : (2 * k) % 2 = 0 := by omega
    rw [if_pos this, add_zero]; congr 2; omega

/-- the profile `D(v) = [v = c] - [(v + ell) mod N₀ = c]`. -/
def Dfun (c ell N0 : ℕ) (v : ℕ) : ℝ := (if v = c then 1 else 0) - (if (v + ell) % N0 = c then 1 else 0)

/-- the transverse profile of the first blocked level. -/
noncomputable def Ubg (ell : ℕ) (t : ℝ) (z : PeriodicLatticeSite L) : ℝ :=
  (((ell : ℝ) ^ 3)⁻¹ * t * (((min ell (L 0 + 1 - (z 0).val) : ℕ) : ℝ) * ((min ell (L 2 + 1 - (z 2).val) : ℕ) : ℝ))) *
    (((min ell (L 1 + 1 - (z 1).val)) / 2 : ℕ) * sgnNat (z 1).val)

/-- **the first blocked level of the staggered layer at EVERY base `z`** (also truncated blocks near the torus end):
direction `0`: `cartan (D(z₀) · Ubg(z))`; directions `1, 2`: trivial. -/
theorem bg1_stag_all (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : 2 ∣ ell) (hell : 0 < ell) (c : ℕ) (t : ℝ) (htπ : |t| < Real.pi)
    (z : PeriodicLatticeSite L) (μ : Fin 3) :
    stridedBlockedGauge su2LogExp 1 ell (stagCfg c t) (z, μ) =
      cartan (if μ = 0 then Dfun c ell (L 0 + 1) (z 0).val * Ubg ell t z else 0) := by
  have hE' : ell % 2 = 0 := Nat.mod_eq_zero_of_dvd hE
  have hcb : coarseBondVar 1 ell (stagCfg c t) (z, μ) = cartan 0 := by
    unfold coarseBondVar
    rw [hol_stag]
    congr 1
    have key : μ = 0 ∨ μ = 1 ∨ μ = 2 := by fin_cases μ <;> simp
    rcases key with rfl | rfl | rfl
    · exact pathAng_rep_ne c t 1 0 (by decide) ell z
    · rw [pathAng_rep_one hN]; simp only [one_mul]; rw [altsum, if_pos hE']; simp
    · exact pathAng_rep_ne c t 1 2 (by decide) ell z
  have hloop : ∀ x ∈ stepBlockOf (z, μ).1 1 ell, loopVar 1 ell (stagCfg c t) (z, μ) x = cartan (stagPhi c t μ ell z x) ∧
      |stagPhi c t μ ell z x| < Real.pi :=
    fun x _ => ⟨loopVar_stag hN hE c t z x μ, stagPhi_abs_lt c t htπ μ ell z x⟩
  rw [blocked_cartan 1 ell (stagCfg c t) (z, μ) (fun x => stagPhi c t μ ell z x) 0 hloop hcb]
  congr 1
  rw [add_zero]
  by_cases hμ : μ = 0
  · subst hμ
    simp only [stagPhi, if_true]
    have hn1 : ∀ x ∈ stepBlockOf z 1 ell, ((x 1 - (Function.update z 2 (x 2)) 1).val) / 1 = ((x 1).val - (z 1).val) := by
      intro x hx
      have e1 : (Function.update z 2 (x 2)) 1 = z 1 := by simp [Function.update_of_ne]
      have h := mem_stepBlockOf.mp hx 1
      have hle : z 1 ≤ x 1 := by rw [Fin.le_def]; exact h.1
      rw [e1, Fin.coe_sub_iff_le.mpr hle, Nat.div_one]
    have h1 : ∀ x ∈ stepBlockOf z 1 ell,
        t * (∑ j ∈ Finset.range (((x 1 - (Function.update z 2 (x 2)) 1).val) / 1), sgnNat ((z 1).val + j)) *
          ((if (z 0).val = c then 1 else 0) - (if ((z 0).val + ell) % (L 0 + 1) = c then 1 else 0))
        = t * Dfun c ell (L 0 + 1) (z 0).val *
          (fun n => if n % 2 = 0 then (0 : ℝ) else sgnNat (z 1).val) (((x 1).val - (z 1).val)) := by
      intro x hx
      rw [hn1 x hx, altsum]
      simp only [Dfun]; ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, sum_block_one z ell (fun n => if n % 2 = 0 then (0 : ℝ) else sgnNat (z 1).val),
      sum_odd_even']
    unfold Ubg
    ring
  · simp [stagPhi, hμ]

#print axioms sum_odd_even'
#print axioms bg1_stag_all

end AdalyFormal.CoverOmega
