import NJE2

/-!
# NJE3 -- staircase, `cPlusS`, and the strided block commute with the sublattice embedding.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.NonflatJet

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath coarseCoordSteps
  coarseStraightSegment)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS cPlusS_eq)

variable {L Lq : PeriodicLatticeExtent} {s : ℕ}

theorem coarseGammaPath_emb (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (a b : PeriodicLatticeSite Lq) :
    coarseGammaPath s (embS hs a) (embS hs b) = coarseGammaPath 1 a b := by
  unfold coarseGammaPath coarseStraightSegment
  rw [embS_update, embS_update, coarseCoordSteps_emb, coarseCoordSteps_emb, coarseCoordSteps_emb]

theorem cPlusS_emb (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (ell : ℕ) (c : PeriodicLatticeEdge Lq) :
    cPlusS s ell (embE hs c) = embS hs (cPlusS 1 ell c) := by
  rw [cPlusS_eq, cPlusS_eq, Nat.one_mul]
  exact embS_shift_gen hs c.1 ell c.2

theorem stepBlockOf_emb (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (ell : ℕ) (y : PeriodicLatticeSite Lq) :
    stepBlockOf (embS hs y) s ell = (stepBlockOf y 1 ell).image (embS hs) := by
  have hspos := s_pos_of hs
  ext x
  rw [Finset.mem_image, mem_stepBlockOf]
  constructor
  · intro hx
    have hdiv : ∀ μ, s ∣ (x μ).val := by
      intro μ
      obtain ⟨h1, h2, h3⟩ := hx μ
      have h3' : s ∣ (x μ).val - s * (y μ).val := by rw [embS_val] at h3; exact h3
      have h1' : s * (y μ).val ≤ (x μ).val := by rw [embS_val] at h1; exact h1
      have hx2 : (x μ).val = ((x μ).val - s * (y μ).val) + s * (y μ).val := (Nat.sub_add_cancel h1').symm
      rw [hx2]
      exact dvd_add h3' (dvd_mul_right s _)
    refine ⟨fun μ => ⟨(x μ).val / s, ?_⟩, ?_, ?_⟩
    · have h1 : (x μ).val < s * (Lq μ + 1) := lt_of_lt_of_eq (x μ).isLt (hs μ)
      exact Nat.div_lt_of_lt_mul h1
    · rw [mem_stepBlockOf]
      intro μ
      obtain ⟨h1, h2, _⟩ := hx μ
      rw [embS_val] at h1 h2
      refine ⟨?_, ?_, one_dvd _⟩
      · show (y μ).val ≤ (x μ).val / s
        rw [Nat.le_div_iff_mul_le hspos]; linarith
      · show (x μ).val / s < (y μ).val + 1 * ell
        rw [Nat.div_lt_iff_lt_mul hspos]; nlinarith
    · funext μ
      apply Fin.ext
      rw [embS_val]
      exact Nat.mul_div_cancel' (hdiv μ)
  · rintro ⟨x', hx', rfl⟩
    intro μ
    have := (mem_stepBlockOf.mp hx') μ
    obtain ⟨h1, h2, _⟩ := this
    refine ⟨?_, ?_, ?_⟩
    · rw [embS_val, embS_val]; exact Nat.mul_le_mul_left _ h1
    · rw [embS_val, embS_val]; nlinarith
    · rw [embS_val, embS_val, ← Nat.mul_sub]; exact Dvd.intro _ rfl

#print axioms coarseGammaPath_emb
#print axioms cPlusS_emb
#print axioms stepBlockOf_emb

end AdalyFormal.NonflatJet
