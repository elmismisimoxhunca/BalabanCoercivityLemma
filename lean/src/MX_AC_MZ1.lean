import MZ1
import MX_Base
import AC_MZ1

/-! AC copy of MZ1: affected declarations only (lane allc_20261016); 12 literal kept (control build). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace MXP.M2DLayer
open AdalyFormal.M2DLayer

open AdalyFormal.AllC MXP.AllC
variable {Φ : Set ℕ} [CubeFactorSet Φ]

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.M2Coverage (Near1 near1_self near1_shift near1_back near1_shift_shift near1_shift_back near1_back_shift_shift back_apply val_succ cube_index_ge)
open AdalyFormal.M1 (strat strat_le strat_eq_iff)

variable {L : PeriodicLatticeExtent}

/-- a class cube containing a stratum-`s` site is a grid box whose grid is a multiple of `M ℓ^{s-1}` -/
theorem cube_boxACΦ {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    {sites : Set (PeriodicLatticeSite L)} {i : ℕ} (hq : IsClassCubeΦ ell M Φ k S sites i)
    {x : PeriodicLatticeSite L} (hx : x ∈ sites) (hx0 : x ∈ S.Om 0) :
    ∃ (f : ℕ) (z : PeriodicLatticeSite L), f ∈ Φ ∧ sites = siteBox z (f * bigSide M ell i) ∧
      (∀ σ, bigSide M ell (strat S k x - 1) ∣ (z σ).val) ∧
      bigSide M ell (strat S k x - 1) ∣ f * bigSide M ell i := by
  obtain ⟨f, hf, hq⟩ := hq
  obtain ⟨-, ⟨z, hgrid, hzs⟩, -, -⟩ := hq.1
  have hj : x ∈ towerBj S (strat S k x) := (strat_eq_iff hS (strat_le S k x) x).2 ⟨hx0, rfl⟩
  have hle : strat S k x ≤ i + 1 := cube_index_ge hS hq hx hj
  have hdv : bigSide M ell (strat S k x - 1) ∣ bigSide M ell i := by
    unfold bigSide; exact Nat.mul_dvd_mul_left M (Nat.pow_dvd_pow ell (by omega))
  refine ⟨f, z, hf, hzs, fun σ => hdv.trans (Nat.dvd_of_mod_eq_zero (hgrid σ)), hdv.trans (Dvd.intro_left _ rfl)⟩

theorem stencil_boxACΦ {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hM : 1 ≤ M)
    (hRM : 3 ≤ R * M) (hcov : CoversOmΦ ell M Φ k S) (x : PeriodicLatticeSite L) (hs : 2 ≤ strat S k x)
    (ν₀ : Fin 3) (hfar : ∀ σ, σ ≠ ν₀ → ¬ NP (bigSide M ell (strat S k x - 1)) (x σ).val) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCubeΦ ell M Φ k S sites i ∧
      ∀ w, Near1 x w → w ∈ sites := by
  set g := bigSide M ell (strat S k x - 1) with hgdef
  have hell1 : 1 ≤ ell := by omega
  have hg2 : 2 ≤ g := by
    rw [hgdef]; unfold bigSide
    have h1 : ell ^ 1 ≤ ell ^ (strat S k x - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [pow_one] at h1
    nlinarith
  have hgN : ∀ σ, g ∣ L σ + 1 := fun σ => hS.2.2.1 _ (by have := strat_le S k x; omega) σ
  have hx0 : x ∈ S.Om 0 := AdalyFormal.M1DStrat.mem_om0_of_strat hS (by omega)
  have nom : ∀ w, pdist x w ≤ 3 → w ∈ S.Om 0 := fun w hw => near_om0 hS hell1 hRM hs hw
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Fin 3, ν₀ ≠ ρ := ⟨ν₀ + 1, by fin_cases ν₀ <;> decide⟩
  have p0 := AdalyFormal.M1DStrat.pd0 x
  -- the generic finish
  have fin : ∀ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCubeΦ ell M Φ k S sites i → x ∈ sites →
      (∀ σ, (x σ).val % g = g - 1 → periodicLatticeShift x σ ∈ sites) →
      (∀ σ, (x σ).val % g = 0 → periodicLatticeShiftBack x σ ∈ sites) →
      ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCubeΦ ell M Φ k S sites i ∧
        ∀ w, Near1 x w → w ∈ sites := by
    intro sites i hq hxs hsu hpr
    obtain ⟨fΦ, z, hfΦ, hzs, hgz, hgT⟩ := cube_boxACΦ hS hq hxs hx0
    subst hzs
    exact ⟨_, i, hq, near1_in_box hgN hgz hgT hg2 hxs hsu hpr⟩
  by_cases h0 : (x ν₀).val % g = 0
  · obtain ⟨p, hmem, hed⟩ := plaq_of (periodicLatticeShiftBack x ν₀) ν₀ ρ hρ
    have hpin : ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (S.Om 0) e := by
      intro e he
      have b1 := AdalyFormal.M1DStrat.pd_bk p0 ν₀
      rcases hed e he with rfl | rfl | rfl | rfl
      · exact ⟨nom _ (b1.trans (by norm_num)), nom _ ((AdalyFormal.M1DStrat.pd_sh b1 ν₀).trans (by norm_num))⟩
      · exact ⟨nom _ ((AdalyFormal.M1DStrat.pd_sh b1 ν₀).trans (by norm_num)),
          nom _ ((AdalyFormal.M1DStrat.pd_sh (AdalyFormal.M1DStrat.pd_sh b1 ν₀) ρ).trans (by norm_num))⟩
      · exact ⟨nom _ ((AdalyFormal.M1DStrat.pd_sh b1 ρ).trans (by norm_num)),
          nom _ ((AdalyFormal.M1DStrat.pd_sh (AdalyFormal.M1DStrat.pd_sh b1 ρ) ν₀).trans (by norm_num))⟩
      · exact ⟨nom _ (b1.trans (by norm_num)), nom _ ((AdalyFormal.M1DStrat.pd_sh b1 ρ).trans (by norm_num))⟩
    obtain ⟨sites, i, hq, hcb⟩ := hcov.2 p hpin
    have hb := hcb _ hmem
    have hxs : x ∈ sites := by have := hb.2; rwa [periodicLatticeShift_shiftBack] at this
    refine fin sites i hq hxs (fun σ hσ => ?_) (fun σ hσ => ?_)
    · by_cases hσ0 : σ = ν₀
      · subst hσ0; omega
      · exact absurd (Or.inr hσ) (hfar σ hσ0)
    · by_cases hσ0 : σ = ν₀
      · subst hσ0; exact hb.1
      · exact absurd (Or.inl hσ) (hfar σ hσ0)
  by_cases h1 : (x ν₀).val % g = g - 1
  · obtain ⟨p, hmem, hed⟩ := plaq_of x ν₀ ρ hρ
    have hpin : ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (S.Om 0) e := by
      intro e he
      rcases hed e he with rfl | rfl | rfl | rfl
      · exact ⟨nom _ (p0.trans (by norm_num)), nom _ ((AdalyFormal.M1DStrat.pd_sh p0 ν₀).trans (by norm_num))⟩
      · exact ⟨nom _ ((AdalyFormal.M1DStrat.pd_sh p0 ν₀).trans (by norm_num)),
          nom _ ((AdalyFormal.M1DStrat.pd_sh (AdalyFormal.M1DStrat.pd_sh p0 ν₀) ρ).trans (by norm_num))⟩
      · exact ⟨nom _ ((AdalyFormal.M1DStrat.pd_sh p0 ρ).trans (by norm_num)),
          nom _ ((AdalyFormal.M1DStrat.pd_sh (AdalyFormal.M1DStrat.pd_sh p0 ρ) ν₀).trans (by norm_num))⟩
      · exact ⟨nom _ (p0.trans (by norm_num)), nom _ ((AdalyFormal.M1DStrat.pd_sh p0 ρ).trans (by norm_num))⟩
    obtain ⟨sites, i, hq, hcb⟩ := hcov.2 p hpin
    have hb := hcb _ hmem
    refine fin sites i hq hb.1 (fun σ hσ => ?_) (fun σ hσ => ?_)
    · by_cases hσ0 : σ = ν₀
      · subst hσ0; exact hb.2
      · exact absurd (Or.inr hσ) (hfar σ hσ0)
    · by_cases hσ0 : σ = ν₀
      · subst hσ0; exact absurd hσ h0
      · exact absurd (Or.inl hσ) (hfar σ hσ0)
  · obtain ⟨sites, i, hq, hxs⟩ := hcov.1 x hx0
    refine fin sites i hq hxs (fun σ hσ => ?_) (fun σ hσ => ?_)
    · by_cases hσ0 : σ = ν₀
      · subst hσ0; exact absurd hσ h1
      · exact absurd (Or.inr hσ) (hfar σ hσ0)
    · by_cases hσ0 : σ = ν₀
      · subst hσ0; exact absurd hσ h0
      · exact absurd (Or.inl hσ) (hfar σ hσ0)

/-- the `ddA` stencils at `x` (every direction) lie in one class cube -/
def StencilCoveredACΦ {L : PeriodicLatticeExtent} (Φ : Set ℕ) (ell M k : ℕ) (S : Tower L) (x : PeriodicLatticeSite L) : Prop :=
  ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCubeΦ ell M Φ k S sites i ∧
    ∀ μ ν : Fin 3, ν ≠ μ → CurlReads sites (periodicLatticeShiftBack x ν) ν μ ∧ CurlReads sites x ν μ

theorem stencil_covACΦ {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hM : 1 ≤ M)
    (hRM : 3 ≤ R * M) (hcov : CoversOmΦ ell M Φ k S) (x : PeriodicLatticeSite L) (hs : 2 ≤ strat S k x)
    (ν₀ : Fin 3) (hfar : ∀ σ, σ ≠ ν₀ → ¬ NP (bigSide M ell (strat S k x - 1)) (x σ).val) :
    StencilCoveredACΦ Φ ell M k S x := by
  obtain ⟨sites, i, hq, hm⟩ := stencil_boxACΦ hS hell hM hRM hcov x hs ν₀ hfar
  exact ⟨sites, i, hq, curlreads_of_near1 sites x hm⟩

/-- **uncovered stencils sit next to grid planes on two axes** -/
theorem unc_two_nearACΦ {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hM : 1 ≤ M)
    (hRM : 3 ≤ R * M) (hcov : CoversOmΦ ell M Φ k S) (x : PeriodicLatticeSite L) (hs : 2 ≤ strat S k x)
    (hunc : ¬ StencilCoveredACΦ Φ ell M k S x) :
    ∃ a b : Fin 3, a ≠ b ∧ NP (bigSide M ell (strat S k x - 1)) (x a).val ∧
      NP (bigSide M ell (strat S k x - 1)) (x b).val := by
  by_contra hcon
  push Not at hcon
  apply hunc
  by_cases hex : ∃ a : Fin 3, NP (bigSide M ell (strat S k x - 1)) (x a).val
  · obtain ⟨a, ha⟩ := hex
    exact stencil_covACΦ hS hell hM hRM hcov x hs a (fun σ hσ hn => hcon a σ (fun h => hσ h.symm) ha hn)
  · push Not at hex
    exact stencil_covACΦ hS hell hM hRM hcov x hs 0 (fun σ _ => hex σ)

end MXP.M2DLayer

