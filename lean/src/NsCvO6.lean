import NsCvO5

/-!
# CvO6 -- sums over strided blocks (lane omega): `Σ_{x ∈ B_s(y)} g((x_μ - y_μ)/s) = ell² Σ_{n<ell} g n` (the block fits the torus)
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

/-- the site `y + s f` -/
def siteOfF (y : PeriodicLatticeSite L) (s ell : ℕ) (hfit : ∀ μ, (y μ).val + s * ell ≤ L μ + 1) (hs : 0 < s)
    (f : Fin 3 → Fin ell) : PeriodicLatticeSite L :=
  fun μ => ⟨(y μ).val + s * (f μ).val, by
    have h1 : s * ((f μ).val + 1) ≤ s * ell := Nat.mul_le_mul_left s (f μ).isLt
    have h2 := hfit μ
    rw [Nat.mul_add, Nat.mul_one] at h1
    omega⟩

theorem stepBlockOf_eq_image (y : PeriodicLatticeSite L) (s ell : ℕ) (hs : 0 < s)
    (hfit : ∀ μ, (y μ).val + s * ell ≤ L μ + 1) :
    stepBlockOf y s ell = Finset.image (siteOfF y s ell hfit hs) Finset.univ := by
  ext x
  simp only [mem_stepBlockOf, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hx
    refine ⟨fun μ => ⟨((x μ).val - (y μ).val) / s, ?_⟩, ?_⟩
    · have h := hx μ
      have hlt : (x μ).val - (y μ).val < ell * s := by
        have := h.2.1; rw [Nat.mul_comm] at this ⊢; omega
      exact (Nat.div_lt_iff_lt_mul hs).mpr hlt
    · funext μ
      have h := hx μ
      apply Fin.ext
      show (y μ).val + s * (((x μ).val - (y μ).val) / s) = (x μ).val
      rw [Nat.mul_div_cancel' h.2.2]
      have := h.1; omega
  · rintro ⟨f, rfl⟩
    intro μ
    refine ⟨by simp [siteOfF], ?_, ?_⟩
    · show (y μ).val + s * (f μ).val < (y μ).val + s * ell
      have : s * (f μ).val < s * ell := by
        have h1 : s * ((f μ).val + 1) ≤ s * ell := Nat.mul_le_mul_left s (f μ).isLt
        rw [Nat.mul_add, Nat.mul_one] at h1
        omega
      omega
    · show s ∣ ((y μ).val + s * (f μ).val - (y μ).val)
      rw [Nat.add_sub_cancel_left]
      exact dvd_mul_right s _

theorem siteOfF_injective (y : PeriodicLatticeSite L) (s ell : ℕ) (hs : 0 < s)
    (hfit : ∀ μ, (y μ).val + s * ell ≤ L μ + 1) : Function.Injective (siteOfF y s ell hfit hs) := by
  intro f g h
  funext μ
  have := congrFun h μ
  have h2 := congrArg Fin.val this
  simp only [siteOfF] at h2
  apply Fin.ext
  have := Nat.eq_of_mul_eq_mul_left hs (by omega : s * (f μ).val = s * (g μ).val)
  exact this

theorem sum_pi_coord {ell : ℕ} (μ : Fin 3) (h : Fin ell → ℝ) :
    ∑ f : Fin 3 → Fin ell, h (f μ) = (ell : ℝ) ^ 2 * ∑ n : Fin ell, h n := by
  rw [← Fintype.sum_equiv (Equiv.piSplitAt μ (fun _ => Fin ell)).symm
    (fun p : Fin ell × ({j : Fin 3 // j ≠ μ} → Fin ell) => h p.1) _ ?_]
  · rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    have hc : Fintype.card {j : Fin 3 // j ≠ μ} = 2 := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin]; simp
    rw [hc, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [nsmul_eq_mul]; push_cast; ring
  · intro p
    simp [Equiv.piSplitAt]

theorem sum_block_dir (y : PeriodicLatticeSite L) (s ell : ℕ) (hs : 0 < s)
    (hfit : ∀ μ, (y μ).val + s * ell ≤ L μ + 1) (μ : Fin 3) (g : ℕ → ℝ) :
    ∑ x ∈ stepBlockOf y s ell, g (((x μ).val - (y μ).val) / s) = (ell : ℝ) ^ 2 * ∑ n ∈ Finset.range ell, g n := by
  rw [stepBlockOf_eq_image y s ell hs hfit, Finset.sum_image (fun f _ g' _ h => siteOfF_injective y s ell hs hfit h)]
  have : ∀ f : Fin 3 → Fin ell, g ((((siteOfF y s ell hfit hs f) μ).val - (y μ).val) / s) = g (f μ).val := by
    intro f
    simp only [siteOfF, Nat.add_sub_cancel_left]
    rw [Nat.mul_div_cancel_left _ hs]
  simp only [this]
  rw [sum_pi_coord μ (fun n => g n.val), Fin.sum_univ_eq_sum_range (fun n => g n) ell]

#print axioms stepBlockOf_eq_image
#print axioms siteOfF_injective
#print axioms sum_pi_coord
#print axioms sum_block_dir

end AdalyFormal.CoverOmega
