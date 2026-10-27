import L0C4

/-!
# L0C5 -- the altered-class headline applied at the curved witness (lane level0_class_20261019)

`level0_instance_inequality`: constants first (`m₁, R₁, a₀, γ₀` from the cap headline `FamTorusCap`); then for every `m ≥ m₁` and `R ≥ max (max R₁ 1) (21 ell)` the curved slab witness
(`nonvac_core_L0` with `Φ = {12, 12 ell}`, `T = max R (12 ell)`) satisfies every hypothesis of `FamTorusCap` for the family of ALL triples with factor in `Φ`, contains for each of the two factors a
`DescribedAt0` box that leaves `Omega_0` (a member of the family, of no original class), and the headline's conclusion `InstAtWD` holds there (with the nonzero `B~` giving the explicit inequality).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 64000000

namespace AdalyFormal.L0NV

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.NonVacC
open AdalyFormal.P409L (DescribedAt0)
open AdalyFormal.L0C
open UNI.AllC UNI.Total

/-- the two factors the print consumes. -/
def Phi12 (ell : ℕ) : Set ℕ := {12, 12 * ell}

theorem level0_instance_inequality (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ (a₀ γ₀ : ℝ), 0 < a₀ ∧ 0 < γ₀ ∧
      ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, max (max R₁ 1) (21 * ell) ≤ R →
      ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
        (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
        2 ≤ k ∧ TorusOK ell (ell ^ m) Lu ∧ Admissible ell (ell ^ m) R k S ∧ LambdaOK2 ell (ell ^ m) R k S Lam ∧
        0 < α₀ ∧ (12 * (ell : ℝ)) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧
        ClassCoupledCap ell (ell ^ m) (famL (Phi12 ell) (scaleUp ell k Lu)) k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
        (∃ p, p ∉ S.Om 0) ∧
        (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
        (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
        Lam.Nonempty ∧ OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
        (∀ f ∈ Phi12 ell, ∃ C : Set (PeriodicLatticeSite (scaleUp ell k Lu)), (C, 0, f) ∈ famL (Phi12 ell) (scaleUp ell k Lu) ∧
          DescribedAt0 ell (ell ^ m) f S C ∧ (∃ x ∈ C, x ∉ S.Om 0) ∧ (∃ x ∈ C, x ∈ S.Om 0) ∧
          ∀ (f' j : ℕ), ¬ IsClassCube ell (ell ^ m) f' k S C j) ∧
        GenP.WellDefG (gparams ell k Lu (by omega) S U a Lam) ∧
        γ₀ * bondEnergy Bt ≤
          GenP.genForm (gparams ell k Lu (by omega) S U a Lam)
            (WithLp.toLp 2 (GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt)) := by
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ₀, hF⟩ := cap_unconditional ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, γ₀, ha₀, hγ₀, fun m hm R hR => ?_⟩
  have hR1 : 1 ≤ R := le_trans (le_trans (le_max_right R₁ 1) (le_max_left _ _)) hR
  have hRR1 : R₁ ≤ R := le_trans (le_trans (le_max_left R₁ 1) (le_max_left _ _)) hR
  have hM : 0 < ell ^ m := pow_pos (by omega) m
  have h12 : (12 : ℕ) ∈ Phi12 ell := Or.inl rfl
  have h12l : 12 * ell ∈ Phi12 ell := Or.inr rfl
  obtain ⟨k, Lu, S, Lam, U, α₀, Bt, hk, hT, hA, hL, hα, hαS, -, hCap, -, -, -, h3, h4, h5, hLam, -, hOT, hOT2, hen, hBt, hLu, hleave⟩ :=
    nonvac_core_L0 (ell := ell) (M := ell ^ m) (R := R) (T := max R (12 * ell)) (Phi12 ell) ⟨12, h12⟩
      (by
        intro f hf
        rcases hf with rfl | rfl
        · have := le_max_right R (12 * ell); omega
        · exact ⟨by omega, le_max_right _ _⟩)
      hell (dvd_pow_self ell (by omega)) hM hR1 (le_max_left _ _) (by have := le_max_left R (12 * ell); omega) ha₀
  have hα12l : (12 * (ell : ℝ)) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ := by
    have := hαS (12 * ell) h12l
    push_cast at this ⊢
    exact this
  have hmain := hF m hm R hRR1 k (by omega) Lu α₀ hα (famL (Phi12 ell) (scaleUp ell k Lu))
    (fun s j f hx => ⟨by
      rcases (show f ∈ Phi12 ell from hx) with rfl | rfl
      · omega
      · omega, hαS f hx⟩) hT S hA Lam hL U hCap
  exact ⟨k, Lu, S, Lam, U, α₀, Bt, hk, hT, hA, hL, hα, hα12l, hCap, h3, h4, h5, hLam, hOT, hOT2, hen, hBt, hleave,
    hmain.1, hmain.2 Bt hOT hOT2⟩

end AdalyFormal.L0NV

#print axioms AdalyFormal.L0NV.level0_instance_inequality
