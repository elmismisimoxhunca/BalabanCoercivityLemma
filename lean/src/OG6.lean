import OG5
import PP5

/-!
# OG6 -- `anchorChart_of_ball` (lane m2_onegap_20261015)
`BallChartsAt` at an anchor `y ∈ Ω_j \ Ω_{j+1}` gives an `AnchorChart` of radius `16 ℓ^j` at the constant `α₀' = ℓ³ (C α₀)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.OneGap

open AdalyFormal.M2Bridge
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (Ball AgreeAt pdist_comm pdist_shift_le pdist_triangle)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.M1 (M1Bounds M1Regular bstrat strat StratReads om_anti le_bstrat_of_mem mem_strat_of_pos)

variable {L : PeriodicLatticeExtent}

theorem anchorChart12_of_ball {ell M R k j : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
    (hM : 2002 ≤ M) (hRM : 1000 * ell ≤ R * M) (hL : ∀ σ, 1 ≤ L σ) (hj : 1 ≤ j) (hjk : j ≤ k)
    {C α₀ η : ℝ} (hC : 1 ≤ C) (hα : 0 < α₀) (hη : 0 < η) {U : LinkCfg L} (hB : BallChartsAt ell M k S U C α₀ η)
    {y : PeriodicLatticeSite L} (hy : y ∈ S.Om j) (hy1 : y ∉ S.Om (j + 1)) :
    AdalyFormal.OneGap12.AnchorChart12 ell M k S U ((ell : ℝ) ^ 3 * (C * α₀)) η y (16 * ell ^ j) := by
  have hell0 : 0 < ell := by omega
  have hnpos : 2 ≤ ell ^ j := by
    calc 2 ≤ ell := hell
      _ = ell ^ 1 := (pow_one ell).symm
      _ ≤ ell ^ j := Nat.pow_le_pow_right hell0 hj
  set n : ℕ := ell ^ j with hn
  -- the radii
  set r16 : ℕ := 16 * n with hr16
  set W : ℕ := 64 * n with hW
  set h : ℕ := r16 + 2 * W + 4 with hh
  set s : ℕ := 2 * h + 1 with hs
  have hs_eq : s = 288 * n + 9 := by omega
  have hbS : ∀ σ, M * n ≤ L σ + 1 := by
    intro σ
    have hd := hS.2.2.1 j hjk σ
    exact Nat.le_of_dvd (Nat.succ_pos _) hd
  have hsN : ∀ σ, s ≤ L σ + 1 := by
    intro σ
    have h1 := hbS σ
    have h2 : 2002 * n ≤ M * n := Nat.mul_le_mul_right n hM
    omega
  have hhN : ∀ σ, h < L σ + 1 := fun σ => by have := hsN σ; omega
  set z : PeriodicLatticeSite L := cornerSite y h with hz
  have hoff : ∀ σ, offc z y σ = h := fun σ => offc_cornerSite y hhN σ
  have hyBox : y ∈ siteBox z s := by
    rw [mem_siteBox_offc]; intro σ; rw [hoff σ]; omega
  -- the ball of the hypothesis
  set r0 : ℕ := 1000 * n with hr0
  have hr0M : r0 ≤ 7 * M * n := by
    have : 143 * n ≤ M * n := Nat.mul_le_mul_right n (by omega)
    nlinarith
  have hr0nw : ∀ σ : Fin 3, 2 * r0 + 2 ≤ L σ + 1 := by
    intro σ
    have h1 := hbS σ
    have h2 : 2002 * n ≤ M * n := Nat.mul_le_mul_right n hM
    omega
  have hbelow : r0 ≤ R * bigSide M ell (j - 1) := by
    have e : n = ell * ell ^ (j - 1) := by
      rw [hn, ← pow_succ']; congr 1; omega
    show r0 ≤ R * (M * ell ^ (j - 1))
    have : 1000 * ell * ell ^ (j - 1) ≤ R * M * ell ^ (j - 1) := Nat.mul_le_mul_right _ hRM
    calc r0 = 1000 * (ell * ell ^ (j - 1)) := by rw [hr0, e]
      _ = 1000 * ell * ell ^ (j - 1) := by ring
      _ ≤ R * M * ell ^ (j - 1) := this
      _ = R * (M * ell ^ (j - 1)) := by ring
  have habove : r0 ≤ R * bigSide M ell (j + 1) := by
    show r0 ≤ R * (M * ell ^ (j + 1))
    have h1 : ell ^ (j + 1) = ell ^ j * ell := pow_succ ell j
    have h2 : 1000 * ell ≤ R * M := hRM
    calc r0 = 1000 * n := rfl
      _ ≤ 1000 * ell * n := by nlinarith
      _ ≤ R * M * n := Nat.mul_le_mul_right _ h2
      _ ≤ R * M * (ell ^ j * ell) := Nat.mul_le_mul_left _ (by nlinarith)
      _ = R * (M * ell ^ (j + 1)) := by rw [h1]; ring
  have hmem := ball_mem_below hS hj hjk hy hbelow
  have hnot := ball_not_above hS hy1 habove
  have hsub : siteBox z s ⊆ Ball y r0 := by
    intro x hx
    have := pdist_lt_three_s' hyBox hx
    show pdist y x ≤ r0
    omega
  obtain ⟨g, A, hexp, hd⟩ : ∃ (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → M2m),
      (∀ e : Bond L, CubeBond (siteBox z s) e →
        ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : M2m)
          = NormedSpace.exp (((η : ℂ) * Complex.I) • A e)) ∧
      CubeData12 ell M 12 ((ell : ℝ) ^ 3 * (C * α₀)) η (siteBox z s) j A := by
    have hreg := hB j hjk y ⟨y, hy, by rw [AdalyFormal.M2Bridge.pdist_self']; omega⟩ r0 hr0M hr0nw hmem hnot (Or.inl (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_right hell0 (by omega))))
    have hCα : 0 ≤ C * α₀ := by positivity
    exact cubeData12_of_region (M := M) (f := 12) (by omega) hη hCα hsub hj hreg
  have hwin : ∀ e : Bond L, CubeBond (siteBox z s) e → bstrat S k e ≤ j + 1 := by
    intro e he
    exact bstrat_le_of_not_mem hS (hnot _ (hsub he.1))
  have hα'' : 0 < (ell : ℝ) ^ 3 * (C * α₀) := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell0
    have : 0 < C := by linarith
    positivity
  obtain ⟨χ, V, hreg, -, hsupp, hcore, hagree⟩ := regime_of_virtual (M := M) (f := 12) (R := R) (i := j) (s := s)
    hS (by omega) (by norm_num) (by omega) hα'' hη (U := U) (z := z) hL (w := W) (by rw [hW]) (by omega) g A hd hwin hexp
  refine ⟨g, V, hreg, ?_⟩
  intro x' hx' μ
  have hcoreS : ∀ σ, s ≤ L σ + 1 → 2 * W + 4 ≤ offc z x' σ ∧ offc z x' σ + 2 * W + 5 ≤ s := by
    intro σ _
    have hmarg : ∀ σ', r16 + 2 * W + 4 ≤ offc z y σ' ∧ offc z y σ' + r16 + 2 * W + 5 ≤ s := by
      intro σ'; rw [hoff σ']; omega
    exact ball_core hsN hmarg hx' σ
  have hχ : χ x' = 1 := hcore x' hcoreS
  have hne : χ x' ≠ 0 := by rw [hχ]; norm_num
  have hsx := hsupp x' hne
  have hcb : CubeBond (siteBox z s) ((x', μ) : Bond L) :=
    ⟨hsx x' (by rw [AdalyFormal.M2Bridge.pdist_self']; norm_num), hsx _ (le_trans (pdist_shift_le x' μ) (by norm_num))⟩
  exact (hagree (x', μ) hcb hχ).symm

end AdalyFormal.OneGap

#print axioms AdalyFormal.OneGap.anchorChart12_of_ball
