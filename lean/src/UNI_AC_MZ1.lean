import MZ1
import UNI_Base
import AC_MZ1

/-! AC copy of MZ1: affected declarations only (lane allc_20261016); 12 literal kept (control build). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace UNI.M2DLayer
open UNI.AllC (CF CubeFamOK)
open AdalyFormal.M2DLayer

open AdalyFormal.AllC UNI.AllC
variable {Fm : CF} [CubeFamOK Fm]

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.M2Coverage (Near1 near1_self near1_shift near1_back near1_shift_shift near1_shift_back near1_back_shift_shift back_apply val_succ cube_index_ge)
open AdalyFormal.M1 (strat strat_le strat_eq_iff)

variable {L : PeriodicLatticeExtent}

/-- a class union containing a stratum-`s` site of `Ω₀` is a union of `b_{s-1}`-cells (`b_{s-1} ∣ b_i`). -/
theorem cube_unionACΦ {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    {sites : Set (PeriodicLatticeSite L)} {i : ℕ} (hq : IsClassCubeQ ell M Fm k S sites i)
    {x : PeriodicLatticeSite L} (hx : x ∈ sites) (hx0 : x ∈ S.Om 0) :
    BlockClosed (bigSide M ell i) sites ∧ bigSide M ell (strat S k x - 1) ∣ bigSide M ell i := by
  obtain ⟨f, hf, hq⟩ := hq
  have hj : x ∈ towerBj S (strat S k x) := (strat_eq_iff hS (strat_le S k x) x).2 ⟨hx0, rfl⟩
  have hle : strat S k x ≤ i + 1 := unionIndex_ge_pred hS hq hx hj.1
  have hdv : bigSide M ell (strat S k x - 1) ∣ bigSide M ell i := by
    unfold bigSide; exact Nat.mul_dvd_mul_left M (Nat.pow_dvd_pow ell (by omega))
  exact ⟨hq.1.2.1, hdv⟩


theorem cell_succ_same {N g x : ℕ} (hgN : g ∣ N) (hg : 2 ≤ g) (hx : x < N) (hr : x % g ≠ g - 1) :
    ((x + 1) % N) / g = x / g := by
  have hnd : ¬ g ∣ x + 1 := by
    intro hd
    have h1 : (x + 1) % g = 0 := Nat.mod_eq_zero_of_dvd hd
    have h2 : (x + 1) % g = (x % g + 1) % g := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < g)]
    have h3 : x % g < g := Nat.mod_lt _ (by omega)
    rw [Nat.mod_eq_of_lt (by omega : x % g + 1 < g)] at h2
    omega
  have hlt : x + 1 < N := by
    by_contra h
    have hxN : x + 1 = N := by omega
    exact hnd (hxN ▸ hgN)
  rw [Nat.mod_eq_of_lt hlt, Nat.succ_div]
  simp [hnd]

theorem cell_pred_same {N g x t : ℕ} (hxN : x < N) (ht : t < N) (hst : (t + 1) % N = x) (hr : x % g ≠ 0) :
    t / g = x / g := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hr
  have hlt : t + 1 < N := by
    by_contra h
    have hN : t + 1 = N := by omega
    rw [hN, Nat.mod_self] at hst
    exact hx0 hst.symm
  rw [Nat.mod_eq_of_lt hlt] at hst
  subst hst
  rw [Nat.succ_div]
  have : ¬ g ∣ t + 1 := fun hd => hr (Nat.mod_eq_zero_of_dvd hd)
  simp [this]

/-- the one-step neighbourhood of `x` in a union of blocks, when only the axis `ν₀` can cross a `g`-cell wall. -/
theorem near1_in_union {g b : ℕ} {sites : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hgN : ∀ σ, g ∣ L σ + 1) (hg : 2 ≤ g) (hgb : g ∣ b) (hbu : BlockClosed b sites) (hx : x ∈ sites)
    (ν₀ : Fin 3) (hfar : ∀ σ, σ ≠ ν₀ → ¬ NP g (x σ).val)
    (hsu : (x ν₀).val % g = g - 1 → periodicLatticeShift x ν₀ ∈ sites)
    (hpr : (x ν₀).val % g = 0 → periodicLatticeShiftBack x ν₀ ∈ sites) :
    ∀ w, Near1 x w → w ∈ sites := by
  intro w hw
  obtain ⟨t, ht⟩ := hgb
  have sat : ∀ v ∈ sites, (∀ τ, (w τ).val / g = (v τ).val / g) → w ∈ sites := by
    intro v hv h
    refine hbu v hv w (fun τ => ?_)
    rw [ht, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h τ]
  have hother : ∀ σ, σ ≠ ν₀ → (w σ).val / g = (x σ).val / g := by
    intro σ hσ
    have hn := hfar σ hσ
    unfold NP at hn
    push Not at hn
    rcases hw σ with h | h | h
    · rw [h]
    · rw [h, val_succ]; exact cell_succ_same (hgN σ) hg (x σ).isLt hn.2
    · rw [h]
      have hst : ((x σ - 1).val + 1) % (L σ + 1) = (x σ).val := by rw [← val_succ, sub_add_cancel]
      exact cell_pred_same (x σ).isLt (x σ - 1).isLt hst hn.1
  rcases hw ν₀ with h | h | h
  · refine sat x hx (fun τ => ?_)
    by_cases hτ : τ = ν₀
    · subst hτ; rw [h]
    · exact hother τ hτ
  · by_cases hr : (x ν₀).val % g = g - 1
    · refine sat _ (hsu hr) (fun τ => ?_)
      by_cases hτ : τ = ν₀
      · subst hτ; rw [h, AdalyFormal.M2Coverage.shift_apply, if_pos rfl]
      · rw [AdalyFormal.M2Coverage.shift_apply, if_neg hτ]; exact hother τ hτ
    · refine sat x hx (fun τ => ?_)
      by_cases hτ : τ = ν₀
      · subst hτ; rw [h, val_succ]; exact cell_succ_same (hgN τ) hg (x τ).isLt hr
      · exact hother τ hτ
  · by_cases hr : (x ν₀).val % g = 0
    · refine sat _ (hpr hr) (fun τ => ?_)
      by_cases hτ : τ = ν₀
      · subst hτ; rw [h, back_apply, if_pos rfl]
      · rw [back_apply, if_neg hτ]; exact hother τ hτ
    · refine sat x hx (fun τ => ?_)
      by_cases hτ : τ = ν₀
      · subst hτ
        rw [h]
        have hst : ((x τ - 1).val + 1) % (L τ + 1) = (x τ).val := by rw [← val_succ, sub_add_cancel]
        exact cell_pred_same (x τ).isLt (x τ - 1).isLt hst hr
      · exact hother τ hτ

theorem stencil_boxACΦ {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hM : 1 ≤ M)
    (hRM : 3 ≤ R * M) (hcov : CoversOmQ ell M Fm k S) (x : PeriodicLatticeSite L) (hs : 2 ≤ strat S k x)
    (ν₀ : Fin 3) (hfar : ∀ σ, σ ≠ ν₀ → ¬ NP (bigSide M ell (strat S k x - 1)) (x σ).val) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCubeQ ell M Fm k S sites i ∧
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
  have fin : ∀ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCubeQ ell M Fm k S sites i → x ∈ sites →
      (∀ σ, (x σ).val % g = g - 1 → periodicLatticeShift x σ ∈ sites) →
      (∀ σ, (x σ).val % g = 0 → periodicLatticeShiftBack x σ ∈ sites) →
      ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCubeQ ell M Fm k S sites i ∧
        ∀ w, Near1 x w → w ∈ sites := by
    intro sites i hq hxs hsu hpr
    obtain ⟨hbu, hdv⟩ := cube_unionACΦ hS hq hxs hx0
    exact ⟨sites, i, hq, near1_in_union hgN hg2 hdv hbu hxs ν₀ hfar (hsu ν₀) (hpr ν₀)⟩
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
def StencilCoveredACΦ {L : PeriodicLatticeExtent} (Fm : CF) (ell M k : ℕ) (S : Tower L) (x : PeriodicLatticeSite L) : Prop :=
  ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCubeQ ell M Fm k S sites i ∧
    ∀ μ ν : Fin 3, ν ≠ μ → CurlReads sites (periodicLatticeShiftBack x ν) ν μ ∧ CurlReads sites x ν μ

theorem stencil_covACΦ {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hM : 1 ≤ M)
    (hRM : 3 ≤ R * M) (hcov : CoversOmQ ell M Fm k S) (x : PeriodicLatticeSite L) (hs : 2 ≤ strat S k x)
    (ν₀ : Fin 3) (hfar : ∀ σ, σ ≠ ν₀ → ¬ NP (bigSide M ell (strat S k x - 1)) (x σ).val) :
    StencilCoveredACΦ Fm ell M k S x := by
  obtain ⟨sites, i, hq, hm⟩ := stencil_boxACΦ hS hell hM hRM hcov x hs ν₀ hfar
  exact ⟨sites, i, hq, curlreads_of_near1 sites x hm⟩

/-- **uncovered stencils sit next to grid planes on two axes** -/
theorem unc_two_nearACΦ {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hM : 1 ≤ M)
    (hRM : 3 ≤ R * M) (hcov : CoversOmQ ell M Fm k S) (x : PeriodicLatticeSite L) (hs : 2 ≤ strat S k x)
    (hunc : ¬ StencilCoveredACΦ Fm ell M k S x) :
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

end UNI.M2DLayer

