import NsCvO36

/-!
# CvO37 -- block ownership count and the one-step conservation law (lane omega)
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

open Classical

variable {L : PeriodicLatticeExtent}

/-- the aligned site below `x`. -/
def alignDown (m : ℕ) (x : PeriodicLatticeSite L) : PeriodicLatticeSite L :=
  fun μ => ⟨m * ((x μ).val / m), by
    have h1 := Nat.mul_div_le (x μ).val m
    have h2 := (x μ).isLt
    omega⟩

theorem alignDown_val (m : ℕ) (x : PeriodicLatticeSite L) (μ : Fin 3) : (alignDown m x μ).val = m * ((x μ).val / m) := rfl

theorem owner_filter {s ell : ℕ} (hs : 0 < s) (hell : 0 < ell) (x : PeriodicLatticeSite L) (hx : Crs s x) :
    Finset.univ.filter (fun y : PeriodicLatticeSite L => Crs (s * ell) y ∧ x ∈ stepBlockOf y s ell) = {alignDown (s * ell) x} := by
  have hm : 0 < s * ell := Nat.mul_pos hs hell
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, mem_stepBlockOf]
  constructor
  · rintro ⟨hcy, hb⟩
    funext μ
    apply Fin.ext
    rw [alignDown_val]
    obtain ⟨q, hq⟩ := hcy μ
    obtain ⟨h1, h2, -⟩ := hb μ
    rw [hq] at h1 h2 ⊢
    have : (x μ).val / (s * ell) = q := by
      apply Nat.div_eq_of_lt_le
      · rw [mul_comm]; exact h1
      · rw [add_mul, one_mul, mul_comm q]; omega
    rw [this]
  · rintro rfl
    refine ⟨fun μ => ⟨(x μ).val / (s * ell), by rw [alignDown_val]⟩, fun μ => ?_⟩
    rw [alignDown_val]
    refine ⟨Nat.mul_div_le _ _, ?_, ?_⟩
    · have := Nat.lt_mul_div_succ (x μ).val hm
      rw [mul_add, mul_one] at this
      omega
    · have h1 := hx μ
      have h2 : s ∣ (s * ell) * ((x μ).val / (s * ell)) := Dvd.dvd.mul_right (Dvd.intro ell rfl) _
      exact Nat.dvd_sub h1 h2

theorem owner_filter_empty {s ell : ℕ} (x : PeriodicLatticeSite L) (hx : ¬ Crs s x) :
    Finset.univ.filter (fun y : PeriodicLatticeSite L => Crs (s * ell) y ∧ x ∈ stepBlockOf y s ell) = ∅ := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and, mem_stepBlockOf]
  intro hcy hb
  apply hx
  intro μ
  obtain ⟨-, -, h3⟩ := hb μ
  have h2 : s ∣ (y μ).val := Dvd.dvd.trans (Dvd.intro ell rfl) (hcy μ)
  have h4 : (y μ).val ≤ (x μ).val := (hb μ).1
  have e : (x μ).val = ((x μ).val - (y μ).val) + (y μ).val := by omega
  rw [e]; exact dvd_add h3 h2

#print axioms owner_filter
#print axioms owner_filter_empty

end AdalyFormal.CoverOmega
