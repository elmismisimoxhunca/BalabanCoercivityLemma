import B0h
import ZXR2Wire3

/-!
# B0i -- B0 on the full tower (the whole-torus case of milestone M0)

`B0_fullTower`: `G = geomOf ell k (fullTower ell k Lu)` (`Ω_j` = whole fine torus for `j ≤ k`), any `U` whose
background tower is regular (`RegTower ell (bgTower G U) k`: the composite jet exists), every `ν ∈ N(Q'(U))`:
`Q(U) D_U ν = 0` for the genuine `Q = QfullOf G U` (= `(bondSectorOf G U).Qfull`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.SliceCoerc

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.Balaban.QjComposite (Qcomposite)

theorem onLat_shift {L : PeriodicLatticeExtent} (m : ℕ) (hm : ∀ μ : Fin 3, m ∣ L μ + 1)
    (x : PeriodicLatticeSite L) (hx : OnLat m x) (μ : Fin 3) : OnLat m (coarseShift x m μ) := by
  intro ν
  by_cases hν : ν = μ
  · subst hν
    rw [coarseShift_val_eq, Nat.dvd_mod_iff (hm ν)]
    exact Nat.dvd_add (hx ν) (dvd_refl m)
  · rw [coarseShift_apply_ne _ _ _ _ hν]; exact hx ν

theorem B0_fullTower (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (U : Cfg (scaleUp ell k Lu))
    (hreg : RegTower ell (bgTower (geomOf ell k (fullTower ell k Lu)) U) k) :
    ∀ ν ∈ NQp (geomOf ell k (fullTower ell k Lu)) U,
      (bondSectorOf (geomOf ell k (fullTower ell k Lu)) U).Qfull (gradL2 U ν) = 0 := by
  intro ν hν
  set G := geomOf ell k (fullTower ell k Lu) with hG
  have hdiv : ∀ μ : Fin 3, ell ^ k ∣ scaleUp ell k Lu μ + 1 := by
    intro μ; rw [scaleUp_succ ell k Lu hell]; exact dvd_mul_left _ _
  refine PiLp.ext (fun p => ?_)
  show (QfullOf G U (gradL2 U ν)) p = 0
  obtain ⟨⟨j, hjlt⟩, c, hc⟩ := p
  have hjk : j = k := by
    by_contra hne
    have hlt : j < k := lt_of_le_of_ne (Nat.lt_succ_iff.mp hjlt) hne
    have hL := fullTower_lam_lt ell k Lu j hlt
    rcases hc.1 with h | h
    · rw [hL] at h; exact h
    · rw [hL] at h; exact h
  subst hjk
  have hlat0 : OnLat (ell ^ j) c.1 := by
    rcases hc.1 with h | h
    · exact (fullTower_lam_k ell j Lu _).mp h
    · have h2 : OnLat (ell ^ j) (coarseShift c.1 (ell ^ j) c.2) := (fullTower_lam_k ell j Lu _).mp h
      intro ν'
      by_cases hν' : ν' = c.2
      · subst hν'
        have h4 := h2 c.2
        rw [coarseShift_val_eq, Nat.dvd_mod_iff (hdiv _)] at h4
        exact (Nat.dvd_add_left (dvd_refl _)).mp h4
      · have h4 := h2 ν'
        rw [coarseShift_apply_ne _ _ _ _ hν'] at h4
        exact h4
  have hlat1 : OnLat (ell ^ j) (coarseShift c.1 (ell ^ j) c.2) := onLat_shift (ell ^ j) hdiv _ hlat0 _
  have hzero : ∀ y, OnLat (ell ^ j) y → Qcomposite (bgTower G U) G.ell j (WithLp.ofLp ν) y = 0 := by
    intro y hy
    have hyL : y ∈ G.Lam j := (fullTower_lam_k ell j Lu y).mpr hy
    have h := hν.2 j (le_refl j) y hyL
    rw [Qlev_apply] at h
    exact h
  exact QfullOf_grad_eq_zero G U hell hreg hdiv ν ⟨⟨j, hjlt⟩, c, hc⟩ hlat0 hlat1 (hzero _ hlat0) (hzero _ hlat1)

#print axioms onLat_shift
#print axioms B0_fullTower

end AdalyFormal.SliceCoerc
