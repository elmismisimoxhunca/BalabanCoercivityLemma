import CvO13

/-!
# CvO14 -- the tower of the staggered layer: `bg1`, `bg2` are temporal at their coarse sites; the unit-level background (lane omega)

For `ell` even, `2 ∣ L 1 + 1`, `ell ∣ L μ + 1`:
* `bg1_temporal`: at every stride-`ell` coarse site `bg1` is temporal with `a₁(v) = (t/2) D(v)`;
* `bg2_temporal`: `bg2 = stridedBlockedGauge (ell^1) ell bg1` is temporal at stride `ell*ell` with `a₂(v) = Σ_{j<ell} a₁((v + ell j) mod N₀)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge loopVar coarseBondVar gammaVarStrided cPlusS cPlusS_eq UbarTower)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)

variable {L : PeriodicLatticeExtent}

theorem crs_fit {s : ℕ} (hdiv : ∀ μ, s ∣ L μ + 1) {y : PeriodicLatticeSite L} (hy : Crs s y) (μ : Fin 3) :
    (y μ).val + s ≤ L μ + 1 := by
  obtain ⟨a, ha⟩ := hy μ
  obtain ⟨b, hb⟩ := hdiv μ
  have h1 : (y μ).val < L μ + 1 := (y μ).isLt
  have hlt : s * a < s * b := by omega
  have hab : a < b := lt_of_mul_lt_mul_left hlt (Nat.zero_le s)
  have : s * (a + 1) ≤ s * b := Nat.mul_le_mul_left s hab
  rw [Nat.mul_add] at this
  omega

theorem bg1_temporal (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : 2 ∣ ell) (hell : 0 < ell) (hdiv : ∀ μ, ell ∣ L μ + 1) (c : ℕ) (t : ℝ)
    (htπ : |t| < Real.pi) (hc1 : ell ≤ c) (hc2 : c + ell ≤ L 0 + 1) :
    IsTemporal ell (stridedBlockedGauge su2LogExp 1 ell (stagCfg c t : PeriodicLinkConfiguration SU2 L))
      (fun v => Dfun c ell (L 0 + 1) v * (t / 2)) := by
  intro y hy
  have hV := bg1_isUTemp hN hE hell c t htπ hc1 hc2 y
  refine ⟨?_, hV.2.1, hV.2.2⟩
  rw [hV.1]
  congr 1
  unfold u1
  have hf1 := crs_fit hdiv hy 1
  have hf2 := crs_fit hdiv hy 2
  have m1 : min ell (L 1 + 1 - (y 1).val) = ell := by omega
  have m2 : min ell (L 2 + 1 - (y 2).val) = ell := by omega
  have hev : (y 1).val % 2 = 0 := by
    obtain ⟨a, ha⟩ := hy 1
    obtain ⟨b, hb⟩ := hE
    rw [ha, hb, Nat.mul_assoc]; exact Nat.mul_mod_right 2 _
  have hs : sgnNat (y 1).val = 1 := by unfold sgnNat; rw [if_pos hev]
  rw [m1, m2, hs]
  obtain ⟨m, hm⟩ := hE
  have hell' : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  have hh : ((ell / 2 : ℕ) : ℝ) = (ell : ℝ) / 2 := by rw [hm, show 2 * m / 2 = m by omega]; push_cast; ring
  rw [hh]
  field_simp

theorem bg2_temporal (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : 2 ∣ ell) (hell : 0 < ell) (hdiv : ∀ μ, ell ∣ L μ + 1) (c : ℕ) (t : ℝ)
    (htπ : |t| < Real.pi) (hc1 : ell ≤ c) (hc2 : c + ell ≤ L 0 + 1) :
    IsTemporal (ell * ell)
      (stridedBlockedGauge su2LogExp ell ell (stridedBlockedGauge su2LogExp 1 ell (stagCfg c t : PeriodicLinkConfiguration SU2 L)))
      (fun v => ∑ j ∈ Finset.range ell, (fun v' => Dfun c ell (L 0 + 1) v' * (t / 2)) ((v + ell * j) % (L 0 + 1))) :=
  blocked_temporal hdiv (bg1_temporal hN hE hell hdiv c t htπ hc1 hc2)

#print axioms crs_fit
#print axioms bg1_temporal
#print axioms bg2_temporal

end AdalyFormal.CoverOmega
