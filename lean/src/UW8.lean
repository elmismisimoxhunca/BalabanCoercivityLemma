import UW7

/-!
# UW8 -- the profile `Fz` in `ℤ³`: bounds (lane unif_20261016)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.UnifLane.Z

open Matrix
open AdalyFormal.M2Glue3 (Z3 ev)
open AdalyFormal.M2Glue2 (frobNorm_sub_le' frobNorm_sub_comm cay isSu2_icay)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.Bch2 (frobNorm_add_le frobNorm_nonneg frobNorm_smul IsSu2)
open AdalyFormal.Balaban.RegularityGap (frobNorm_neg)

section prof
variable {W : Z3 → Fin 3 → SU2} {σ τ₁ τ₂ : Fin 3} {lo hi : Z3} {c0 c ch : ℤ} {Go Gn : Z3 → SU2} {w : ℕ}
  (hc0 : c0 + 2 ≤ c) (hch : c + 2 ≤ ch)
  {o1 o2 n1 n2 η : ℝ}
  (hO1 : C1 W Go (SlabS σ lo hi c0 c) o1) (hO2 : C2 W Go (SlabS σ lo hi c0 c) o2)
  (hN1 : C1 W Gn (SlabS σ lo hi c ch) n1) (hN2 : C2 W Gn (SlabS σ lo hi c ch) n2)
  (hH : HolB W (SlabS σ lo hi c0 ch) η)
  (ho1 : 0 ≤ o1) (hn1 : 0 ≤ n1) (hη : 0 ≤ η) (ho2 : 0 ≤ o2) (hn2 : 0 ≤ n2) (hsm : o1 + n1 ≤ 2)
  (hlh : ∀ ν, ν ≠ σ → lo ν ≤ hi ν) (hτ : ∀ ν, ν ≠ σ → ν = τ₁ ∨ ν = τ₂) (h1σ : τ₁ ≠ σ) (h2σ : τ₂ ≠ σ) (hw : 1 ≤ w)
include hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh

theorem fh_sup : SupB (fh W σ c lo hi Go Gn) (VBc o1 n1) := by
  intro y
  have hm := clampP_mem σ c ch (by omega) lo hi hlh y
  exact vf_bound hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hm.1 hm.2

theorem fh_d1 {τ : Fin 3} (hτσ : τ ≠ σ) : D1 τ (fh W σ c lo hi Go Gn) (Dvc o1 o2 n1 n2 η) := by
  intro y
  have hD : 0 ≤ Dvc o1 o2 n1 n2 η := by unfold Dvc g02c K0c; positivity
  simp only [fh]
  rcases clampP_add_ne σ c lo hi y hτσ with h | h
  · rw [h, sub_self, frobNorm_zero']; exact hD
  · rw [h]
    have hm := clampP_mem σ c ch (by omega) lo hi hlh y
    have hm' := clampP_mem σ c ch (by omega) lo hi hlh (y + ev τ)
    rw [h] at hm'
    exact vf_d1 hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hm.1 hm.2 hτσ hm'.1

theorem fh_su2 (y : Z3) : IsSu2 (fh W σ c lo hi Go Gn y) := isSu2_icay _

include h1σ h2σ in
theorem pfam_fh : PFam (fun n => P2 τ₁ τ₂ n (fh W σ c lo hi Go Gn)) τ₁ τ₂ (VBc o1 n1) (Dvc o1 o2 n1 n2 η) :=
  pfam_P2 (fh_sup hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh)
    (fh_d1 hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh h1σ)
    (fh_d1 hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh h2σ) (by unfold Dvc g02c K0c; positivity)

theorem fz_su2 (p : Z3) : IsSu2 (Fz W σ τ₁ τ₂ c lo hi Go Gn w p) := by
  unfold Fz Phi P2
  exact (isSu2_av (fun y => isSu2_av (fun z => fh_su2 hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh z) y) _).smul _

theorem fz_plane {p : Z3} (hp : p σ = c) : Fz W σ τ₁ τ₂ c lo hi Go Gn w p = 0 := by
  unfold Fz; rw [tp_plane hp]; simp [Phi, cf]

include hw in
theorem fz_one {p : Z3} (hp : p ∈ SlabS σ lo hi c ch) (hp1 : p σ = c + 1) :
    Fz W σ τ₁ τ₂ c lo hi Go Gn w p = Vf W σ c Go Gn (bp σ c p) := by
  unfold Fz
  have ht : tp σ c p = 1 := by simp [tp, hp1]
  rw [ht]
  simp only [Phi, cf, Nat.sub_self]
  rw [zeta_of_le hw hw]
  simp only [Nat.cast_one, one_mul, one_smul, P2, av_zero_radius, fh]
  rw [clampP_of_mem (bp_mem σ lo hi c0 c ch hc0 (by omega) hp).1 (bp_plane σ c p)]

include hτ h1σ h2σ hw in
theorem fz_d1 {p : Z3} {ν : Fin 3} (hp : p ∈ SlabS σ lo hi c ch) (hpν : p + ev ν ∈ SlabS σ lo hi c ch) :
    frobNorm (Fz W σ τ₁ τ₂ c lo hi Go Gn w (p + ev ν) - Fz W σ τ₁ τ₂ c lo hi Go Gn w p) ≤ F1c o1 o2 n1 n2 η w := by
  have hP := pfam_fh hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh h1σ h2σ
  have hVB : 0 ≤ VBc o1 n1 := by unfold VBc; positivity
  have hD : 0 ≤ Dvc o1 o2 n1 n2 η := by unfold Dvc g02c K0c; positivity
  unfold Fz F1c
  by_cases hνσ : ν = σ
  · rw [hνσ]
    rw [tp_add_self hp.2.1, bp_add_self]
    exact phi_dt hw hP hVB hD _ _
  · rw [tp_add_ne p hνσ, bp_add_ne σ c p hνσ]
    have := phi_dx hw hP hVB hD (tp σ c p) (bp σ c p) ν (hτ ν hνσ)
    have : (2 : ℝ) * w * Dvc o1 o2 n1 n2 η ≤ 8 * w * Dvc o1 o2 n1 n2 η := by
      have : (0 : ℝ) ≤ w := by positivity
      nlinarith
    linarith

include hτ h1σ h2σ hw in
theorem fz_d2 {p : Z3} {μ ν : Fin 3} (h0 : p ∈ SlabS σ lo hi c ch) (h1 : p + ev ν ∈ SlabS σ lo hi c ch)
    (h2 : p + ev μ ∈ SlabS σ lo hi c ch) (h3 : p + ev μ + ev ν ∈ SlabS σ lo hi c ch) :
    frobNorm (Fz W σ τ₁ τ₂ c lo hi Go Gn w (p + ev μ + ev ν) - Fz W σ τ₁ τ₂ c lo hi Go Gn w (p + ev μ)
      - (Fz W σ τ₁ τ₂ c lo hi Go Gn w (p + ev ν) - Fz W σ τ₁ τ₂ c lo hi Go Gn w p)) ≤ F2c o1 o2 n1 n2 η w := by
  have hP := pfam_fh hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh h1σ h2σ
  have hVB : 0 ≤ VBc o1 n1 := by unfold VBc; positivity
  have hD : 0 ≤ Dvc o1 o2 n1 n2 η := by unfold Dvc g02c K0c; positivity
  have hw0 : (0 : ℝ) < w := by exact_mod_cast hw
  have hF : 29 * Dvc o1 o2 n1 n2 η ≤ F2c o1 o2 n1 n2 η w := by
    unfold F2c; have : 0 ≤ 84 * VBc o1 n1 / w := by positivity
    linarith
  have hF' : 2 * Dvc o1 o2 n1 n2 η ≤ F2c o1 o2 n1 n2 η w := by linarith
  unfold Fz
  set P := fun n => P2 τ₁ τ₂ n (fh W σ c lo hi Go Gn)
  set t := tp σ c p
  set x := bp σ c p
  have hpc : c ≤ p σ := h0.2.1
  by_cases hμ : μ = σ
  · by_cases hν : ν = σ
    · rw [hμ, hν]
      rw [tp_add_self (by simp [ev_apply_self]; omega), tp_add_self hpc, bp_add_self, bp_add_self]
      have := phi_dtt hw hP hVB hD t x
      rw [show (t + 1 + 1) = t + 2 by ring]
      unfold F2c; linarith
    · rw [hμ]
      rw [show p + ev σ + ev ν = p + ev ν + ev σ by abel, tp_add_self (by simp [ev_apply_ne (Ne.symm hν)]; omega),
        tp_add_self hpc, tp_add_ne p hν, bp_add_self, bp_add_self, bp_add_ne σ c p hν]
      have := phi_dtx hw hP hVB hD t x ν (hτ ν hν)
      rw [show Phi w P (t + 1) (x + ev ν) - Phi w P (t + 1) x - (Phi w P t (x + ev ν) - Phi w P t x)
        = (Phi w P (t + 1) (x + ev ν) - Phi w P t (x + ev ν)) - (Phi w P (t + 1) x - Phi w P t x) by abel]
      linarith
  · by_cases hν : ν = σ
    · rw [hν]
      rw [tp_add_self (by simp [ev_apply_ne (Ne.symm hμ)]; omega), tp_add_self hpc, tp_add_ne p hμ, bp_add_self,
        bp_add_self, bp_add_ne σ c p hμ]
      have := phi_dtx hw hP hVB hD t x μ (hτ μ hμ)
      linarith
    · rw [tp_add_ne _ hν, tp_add_ne p hμ, tp_add_ne p hν, bp_add_ne σ c _ hν, bp_add_ne σ c p hμ, bp_add_ne σ c p hν]
      have := phi_dxx hw hP hVB hD t x μ ν (hτ μ hμ) (hτ ν hν)
      rw [show Phi w P t (x + ev μ + ev ν) - Phi w P t (x + ev μ) - (Phi w P t (x + ev ν) - Phi w P t x)
        = Phi w P t (x + ev μ + ev ν) - Phi w P t (x + ev μ) - Phi w P t (x + ev ν) + Phi w P t x by abel]
      linarith

end prof

end AdalyFormal.UnifLane.Z
