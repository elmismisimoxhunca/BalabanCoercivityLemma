import NsCvO37

/-!
# CvO38 -- one-step conservation law of the abelian raw step (lane omega)

`Σ_{y : Crs (s ell)} h(y₀) Rsig s ell θ (y,1) = ell⁻² Σ_{x : Crs s} h(s ell ⌊x₀/(s ell)⌋) θ(x,1)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.UbarTowerCov (cPlusS cPlusS_eq)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)

variable {L : PeriodicLatticeExtent}

theorem fit_of_crs {m : ℕ} (hdiv : ∀ μ, m ∣ L μ + 1) {y : PeriodicLatticeSite L} (hy : Crs m y) (μ : Fin 3) :
    (y μ).val + m ≤ L μ + 1 := by
  obtain ⟨a, ha⟩ := hy μ
  obtain ⟨b, hb⟩ := hdiv μ
  have hlt := (y μ).isLt
  rw [ha] at hlt ⊢
  rw [hb] at hlt ⊢
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hlt
    · exact h
  have : a < b := by
    by_contra hh
    push_neg at hh
    have := Nat.mul_le_mul_left m hh
    omega
  have := Nat.mul_le_mul_left m (show a + 1 ≤ b from this)
  rw [mul_add, mul_one] at this
  omega

open Classical in
theorem cons1 {s ell : ℕ} (hs : 0 < s) (hell : 0 < ell) (hdiv : ∀ μ, s * ell ∣ L μ + 1)
    (θ : PeriodicLatticeEdge L → ℝ) (h : ℕ → ℝ) :
    ∑ y : PeriodicLatticeSite L, (if Crs (s * ell) y then h (y 0).val * Rsig s ell θ (y, 1) else 0) =
      (((ell : ℝ) ^ 2)⁻¹) * ∑ x : PeriodicLatticeSite L,
        (if Crs s x then h ((s * ell) * ((x 0).val / (s * ell))) * θ (x, 1) else 0) := by
  have hm : 0 < s * ell := Nat.mul_pos hs hell
  have hdivs : ∀ μ, s ∣ L μ + 1 := fun μ => Dvd.dvd.trans (Dvd.intro ell rfl) (hdiv μ)
  -- Rsig as block sums
  have step1 : ∀ y : PeriodicLatticeSite L, Crs (s * ell) y →
      Rsig s ell θ (y, 1) = (((ell : ℝ) ^ 3)⁻¹) * ∑ x ∈ stepBlockOf y s ell, ∑ i ∈ Finset.range ell, θ (((sPerm 1 s) ^ i) x, 1) := by
    intro y hy
    have hfit := fit_of_crs hdiv hy
    have hfit' : ∀ ν, ((cPlusS s ell (y, 1)) ν).val + s * ell ≤ L ν + 1 := by
      intro ν
      rw [cPlusS_eq]
      exact fit_of_crs hdiv (Crs_shift hdiv hy 1 (s * ell) dvd_rfl) ν
    rw [Rsig_closed hs hell y 1 hfit hfit' θ]
    congr 1
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [pathAngG_rep_sum]
  set G : PeriodicLatticeSite L → ℝ := fun x => ∑ i ∈ Finset.range ell, θ (((sPerm 1 s) ^ i) x, 1) with hGdef
  have pA : ∀ y : PeriodicLatticeSite L, (if Crs (s * ell) y then h (y 0).val * Rsig s ell θ (y, 1) else 0) =
      (((ell : ℝ) ^ 3)⁻¹) * ∑ x : PeriodicLatticeSite L, (if Crs (s * ell) y ∧ x ∈ stepBlockOf y s ell then h (y 0).val * G x else 0) := by
    intro y
    by_cases hy : Crs (s * ell) y
    · rw [if_pos hy, step1 y hy]
      have e : ∀ x : PeriodicLatticeSite L, (if Crs (s * ell) y ∧ x ∈ stepBlockOf y s ell then h (y 0).val * G x else 0) =
          if x ∈ stepBlockOf y s ell then h (y 0).val * G x else 0 := by
        intro x; simp [hy]
      simp only [e]
      rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum, hGdef]
      ring
    · simp [hy]
  have pB : ∀ x : PeriodicLatticeSite L, ∑ y : PeriodicLatticeSite L, (if Crs (s * ell) y ∧ x ∈ stepBlockOf y s ell then h (y 0).val * G x else 0) =
      if Crs s x then h ((s * ell) * ((x 0).val / (s * ell))) * G x else 0 := by
    intro x
    rw [← Finset.sum_filter]
    by_cases hx : Crs s x
    · rw [owner_filter hs hell x hx, Finset.sum_singleton, if_pos hx, alignDown_val]
    · rw [owner_filter_empty x hx, Finset.sum_empty, if_neg hx]
  have hA : ∑ y : PeriodicLatticeSite L, (if Crs (s * ell) y then h (y 0).val * Rsig s ell θ (y, 1) else 0) =
      (((ell : ℝ) ^ 3)⁻¹) * ∑ x : PeriodicLatticeSite L, (if Crs s x then h ((s * ell) * ((x 0).val / (s * ell))) * G x else 0) := by
    simp only [pA]
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl (fun x _ => pB x)
  rw [hA]
  -- translation invariance
  set hh : PeriodicLatticeSite L → ℝ := fun x => h ((s * ell) * ((x 0).val / (s * ell))) with hhdef
  have hinv : ∀ i : ℕ, ∑ x : PeriodicLatticeSite L, (if Crs s x then hh x * θ (((sPerm 1 s) ^ i) x, 1) else 0) =
      ∑ x : PeriodicLatticeSite L, (if Crs s x then hh x * θ (x, 1) else 0) := by
    intro i
    have := Equiv.sum_comp ((sPerm 1 s) ^ i) (fun z : PeriodicLatticeSite L => if Crs s z then hh z * θ (z, 1) else 0)
    rw [← this]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have hc : Crs s (((sPerm 1 s) ^ i) x) ↔ Crs s x := sPerm_crs_iff hdivs 1 i x
    have h0 : (((sPerm 1 s) ^ i) x) 0 = x 0 := sPerm_coord_ne 1 s i x 0 (by decide)
    simp only [hhdef, h0]
    by_cases hx : Crs s x
    · rw [if_pos hx, if_pos (hc.mpr hx)]
    · rw [if_neg hx, if_neg (fun hh' => hx (hc.mp hh'))]
  have hG : ∑ x : PeriodicLatticeSite L, (if Crs s x then hh x * G x else 0) =
      (ell : ℝ) * ∑ x : PeriodicLatticeSite L, (if Crs s x then hh x * θ (x, 1) else 0) := by
    have : ∀ x : PeriodicLatticeSite L, (if Crs s x then hh x * G x else 0) =
        ∑ i ∈ Finset.range ell, (if Crs s x then hh x * θ (((sPerm 1 s) ^ i) x, 1) else 0) := by
      intro x
      by_cases hx : Crs s x
      · simp only [if_pos hx, hGdef, Finset.mul_sum]
      · simp [hx]
    simp only [this]
    rw [Finset.sum_comm]
    simp only [hinv, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have e2 : (((ell : ℝ) ^ 3)⁻¹) * (ell : ℝ) = ((ell : ℝ) ^ 2)⁻¹ := by
    have : (ell : ℝ) ≠ 0 := by positivity
    field_simp
  rw [show (∑ x : PeriodicLatticeSite L, (if Crs s x then h ((s * ell) * ((x 0).val / (s * ell))) * G x else 0)) =
      ∑ x : PeriodicLatticeSite L, (if Crs s x then hh x * G x else 0) from rfl, hG, ← mul_assoc, e2]

#print axioms cons1

end AdalyFormal.CoverOmega
