import SectBFlat
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HConstruction.SectBBase
open HConstruction.GenK
open AdalyFormal.Target.ClayStatement
variable (M : PeriodicLatticeExtent) {n : ℕ} (hn : 0 < n)
include hn

/-- Qualitative invertibility for the *actual* flat single-stratum site
auxiliary operator. Finite-dimensional surjectivity is not a uniform bound. -/
theorem flatDeltaPrime_injective (k : ℕ) : Function.Injective
    (flatDeltaPrime M (n := n) k) := by
  intro f g h
  apply sub_eq_zero.mp
  apply flatDeltaPrime_kernel M k (f - g) hn
  rw [map_sub, h, sub_self]

theorem flatDeltaPrime_surjective (k : ℕ) : Function.Surjective
    (flatDeltaPrime M (n := n) k) := by
  exact LinearMap.injective_iff_surjective.mp
    (flatDeltaPrime_injective M hn k)

/-- CMP99b's G'(1)=(Δ'_1(1))^{-1} restricted to the periodic
single-stratum specialization, rather than a postulated inverse. -/
def flatGPrime (k : ℕ) : GenK.Site M (n := n) →L[ℝ] GenK.Site M (n := n) :=
  ((LinearEquiv.ofBijective (flatDeltaPrime M (n := n) k).toLinearMap
      ⟨flatDeltaPrime_injective M hn k, flatDeltaPrime_surjective M hn k⟩).symm.toLinearMap).toContinuousLinearMap

theorem flatDeltaPrime_flatGPrime (k : ℕ) (f : GenK.Site M (n := n)) :
    flatDeltaPrime M k (flatGPrime M hn k f) = f := by
  exact (LinearEquiv.ofBijective (flatDeltaPrime M (n := n) k).toLinearMap
      ⟨flatDeltaPrime_injective M hn k, flatDeltaPrime_surjective M hn k⟩).apply_symm_apply f

theorem flatGPrime_flatDeltaPrime (k : ℕ) (f : GenK.Site M (n := n)) :
    flatGPrime M hn k (flatDeltaPrime M k f) = f := by
  exact (LinearEquiv.ofBijective (flatDeltaPrime M (n := n) k).toLinearMap
      ⟨flatDeltaPrime_injective M hn k, flatDeltaPrime_surjective M hn k⟩).symm_apply_apply f

end HConstruction.SectBBase
