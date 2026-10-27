import DLR5
import DLR60
import DLR74
import DLR76
import DLR83

/-!
# DL84 -- **`instIneq_M0_class_unconditional`**: the frozen (r7) `InstIneq` on M0 ∩ PerCubeRegular2, every `k`,
with k- and volume-free constants, and NO D-layer hypothesis left

Hypotheses: the M0 regime (`M0RegimeR`, `KUSmall`, `UnitSmall`, torus conditions, `LamBlockSum`), the PRINTED class
(`PerCubeRegular2 ℓ M f k (fullTower) α₀ ℓ^{-k} U`, `4 ≤ f`, `0 < M`, `4fMα₀ ≤ 1`), and the k-free numerics package
`M0ClassNum ℓ a t ρ β θ` (ρ = rhoM0 ℓ k e q0, β = fMα₀): the Combes–Thomas conditions of the `G` and `G₁` chains,
the two one-step `ℓ¹` contraction conditions, and `ε' < 1`.
The five D-layer premises of DL5 are discharged by DL60 (`hJs_class`), DL53 (`hHcol_M0`), DL74 (`hK2_M0`),
DL83 (`hH1col_M0`), DL76 (`hKDb_M0`).  Result: `γ₀ = gam0M0f ℓ a t ρ ε' εJ dC cB` with
  `ε' = 2·CHfree·JSfree(β)·K2free·K̂`,  `εJ = KDfree·CH1free·JSfree(β)`  — no `k`, no volume.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp OnLambdaTildeIn)
open AdalyFormal.StatementLane2 (OnLambdaT PerCubeRegular2)
open AdalyFormal.StatementLaneG (LamBlockSum InstIneq)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.AsmM0
open AdalyFormal.SliceCoerc
open AdalyFormal.BondComposite (rr)
open AdalyFormal.RegBgKU (KUSmall kapHat)
open AdalyFormal.M0Finish (PU UnitSmall dCM0 cBM0)
open AdalyFormal.NonflatJet (rhoOf)
open EstimatesLayer.E1E3 (e2Majorant)

/-- the `ψ`-constants of the `G₁` chain (k-free) -/
noncomputable def nuPsi (ell : ℕ) (a t ρ β θ : ℝ) (hc : CondM0 ell a ρ θ) (hK : 0 < KhatM0 ell a t ρ)
    (hEG : 4 * EGM0 ell a ρ θ hc ≤ 1 / KhatM0 ell a t ρ) : ℝ :=
  2 * CHfree ell a t ρ θ hc hK hEG * JSfree β * K2free ell ρ

noncomputable def deltaPsi (ell : ℕ) (a t ρ β θ : ℝ) (hc : CondM0 ell a ρ θ) (hK : 0 < KhatM0 ell a t ρ)
    (hEG : 4 * EGM0 ell a ρ θ hc ≤ 1 / KhatM0 ell a t ρ) : ℝ :=
  nuPsi ell a t ρ β θ hc hK hEG * 648 * ((Real.exp (5 * θ) - 1) * (Real.exp (5 * θ) + 1))

theorem JSfree_nonneg (β : ℝ) (hβ : 0 ≤ β) : 0 ≤ JSfree β := by unfold JSfree; positivity

theorem CHfree_nonneg (ell : ℕ) (a t ρ θ : ℝ) (hθ : 0 < θ) (hc : CondM0 ell a ρ θ) (hK : 0 < KhatM0 ell a t ρ)
    (hEG : 4 * EGM0 ell a ρ θ hc ≤ 1 / KhatM0 ell a t ρ)
    (hN : ENfree ell a t ρ θ hc hK hEG < 1 / bNS a ρ (δS ell ρ)) : 0 ≤ CHfree ell a t ρ θ hc hK hEG := by
  unfold CHfree
  have : 0 ≤ qBS ell a ρ := by unfold qBS; positivity
  have := hc.δBS_nonneg
  have : 0 < 1 / bNS a ρ (δS ell ρ) - ENfree ell a t ρ θ hc hK hEG := by linarith
  have := hc.ha
  positivity

theorem K2free_nonneg (ell : ℕ) (ρ : ℝ) (hell : 2 ≤ ell) (hρ : 0 ≤ ρ)
    (hK2c : 1536 * (ell : ℝ) ^ 2 * e2Majorant (rhoOf ell ρ) < 1 - 1 / (ell : ℝ)) : 0 ≤ K2free ell ρ := by
  unfold K2free thetaK2
  have : 0 < 1 - (1 / (ell : ℝ) + 1536 * (ell : ℝ) ^ 2 * e2Majorant (rhoOf ell ρ)) := by linarith
  have : 0 ≤ K2s ell := by unfold K2s; positivity
  positivity

theorem KDfree_nonneg (ell : ℕ) : 0 ≤ KDfree ell := by unfold KDfree K2s; positivity

/-- **the k-free numerics package** (all functions of `(ℓ, a, t, ρ, β, θ)` only) -/
structure M0ClassNum (ell : ℕ) (a t ρ β θ : ℝ) : Prop where
  hθ : 0 < θ
  hβ : 0 ≤ β
  hc : CondM0 ell a ρ θ
  hK : 0 < KhatM0 ell a t ρ
  hEG : 4 * EGM0 ell a ρ θ hc ≤ 1 / KhatM0 ell a t ρ
  hN : ENfree ell a t ρ θ hc hK hEG < 1 / bNS a ρ (δS ell ρ)
  hK2c : 1536 * (ell : ℝ) ^ 2 * e2Majorant (rhoOf ell ρ) < 1 - 1 / (ell : ℝ)
  hKDc : 192 * (8 * (ell : ℝ) * kapHat ell ρ + 8 * e2Majorant (rhoOf ell (kapHat ell ρ))) ≤ 1 / (2 * (ell : ℝ) ^ 3)
  hν : 0 ≤ nuPsi ell a t ρ β θ hc hK hEG
  hδ : 0 ≤ deltaPsi ell a t ρ β θ hc hK hEG
  hcg1 : 0 < cg1 ell a t ρ θ hc (nuPsi ell a t ρ β θ hc hK hEG)
  hEG1 : 4 * EGM1 ell a ρ θ hc (nuPsi ell a t ρ β θ hc hK hEG) (deltaPsi ell a t ρ β θ hc hK hEG) hν hδ
    ≤ cg1 ell a t ρ θ hc (nuPsi ell a t ρ β θ hc hK hEG)
  hN1 : EN1free ell a t ρ θ hc (nuPsi ell a t ρ β θ hc hK hEG) (deltaPsi ell a t ρ β θ hc hK hEG) hν hδ hK hcg1 hEG1
    < 1 / bN1 ell a t ρ θ hc (nuPsi ell a t ρ β θ hc hK hEG)
  hε' : 2 * CHfree ell a t ρ θ hc hK hEG * JSfree β * K2free ell ρ * KhatM0 ell a t ρ < 1

/-- the two k-free smallness constants of the conclusion -/
noncomputable def eps2free {ell : ℕ} {a t ρ β θ : ℝ} (h : M0ClassNum ell a t ρ β θ) : ℝ :=
  2 * CHfree ell a t ρ θ h.hc h.hK h.hEG * JSfree β * K2free ell ρ * KhatM0 ell a t ρ

noncomputable def epsJfree {ell : ℕ} {a t ρ β θ : ℝ} (h : M0ClassNum ell a t ρ β θ) : ℝ :=
  KDfree ell * CH1free ell a t ρ θ h.hc (nuPsi ell a t ρ β θ h.hc h.hK h.hEG) (deltaPsi ell a t ρ β θ h.hc h.hK h.hEG)
    h.hν h.hδ h.hK h.hcg1 h.hEG1 * JSfree β

/-- **THE TARGET: `InstIneq` on M0 ∩ PerCubeRegular2 at the full tower, every `k`, no D-layer hypothesis** -/
theorem instIneq_M0_class_unconditional (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ) (R : M0RegimeR ell k Lu U a t e q0)
    (H : KUSmall ell (rhoM0 ell k e q0)) (HU : UnitSmall ell (rhoM0 ell k e q0))
    (hstrict : ∀ μ : Fin 3, ell < Lu μ + 1) (hd : ∀ μ, ell ∣ Lu μ + 1)
    (Lam : Set (PeriodicLatticeSite Lu)) (hLB : LamBlockSum ell Lam)
    (M f : ℕ) (α₀ : ℝ) (hM : 0 < M) (hf : 4 ≤ f)
    (hP : PerCubeRegular2 ell M f k (fullTower ell k Lu) α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (hsm : 4 * ((f : ℝ) * M * α₀) ≤ 1)
    (θ : ℝ) (Num : M0ClassNum ell a t (rhoM0 ell k e q0) ((f : ℝ) * M * α₀) θ) :
    InstIneq ell k hell a Lu
      (gam0M0f ell a t (rhoM0 ell k e q0) (eps2free Num) (epsJfree Num)
        (dCM0 ell (rhoM0 ell k e q0)) (cBM0 ell (rhoM0 ell k e q0)))
      (fullTower ell k Lu) Lam U := by
  have hell2 : 2 ≤ ell := R.hell
  set ρ := rhoM0 ell k e q0 with hρdef
  set β := (f : ℝ) * M * α₀ with hβdef
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := by positivity
  set n := (ell : ℝ) ^ k with hndef
  have hρ0 : 0 ≤ ρ := m0_rho_nonneg ell k Lu U a t e q0 R
  -- the constants
  set CHf := CHfree ell a t ρ θ Num.hc Num.hK Num.hEG with hCHf
  set JS := JSfree β with hJS
  set K2f := K2free ell ρ with hK2f
  have hCHf0 : 0 ≤ CHf := CHfree_nonneg ell a t ρ θ Num.hθ Num.hc Num.hK Num.hEG Num.hN
  have hJS0 : 0 ≤ JS := JSfree_nonneg β Num.hβ
  have hK2f0 : 0 ≤ K2f := K2free_nonneg ell ρ hell2 hρ0 Num.hK2c
  set P := PU ell k Lu hell U a Lam with hPdef
  -- premise 1: hJs
  have hJs : ∀ b, ‖P.Jf b‖ ≤ JS / n ^ 3 := fun b => hJs_class ell M f k Lu hell U a Lam α₀ hM hf hP hsm b
  -- premise 2: hHcol
  have hHcol : ∀ (p : BIdx P.G) (v : SuTwo),
      ∑ b, ‖(iE P.G (P.data.H (WithLp.toLp 2 (Pi.single p v) : FSp P.G))) b‖ ≤ (CHf * n ^ 3) * ‖v‖ := by
    intro p v
    have := hHcol_M0 ell k Lu U a t e q0 R H θ Num.hθ Num.hc Num.hEG Num.hN Lam p v
    exact this
  -- premise 3: hK2
  have hK2 : ∀ z : BondFnL2 (scaleUp ell k Lu), ∑ p, ‖C2fullOf P.G U z p‖ ≤ (K2f / n ^ 2) * ‖z‖ ^ 2 :=
    fun z => hK2_M0 ell k Lu hell U a t e q0 R H Lam Num.hK2c z
  -- the ψ-bundle
  have hψ : ∀ p, ‖psiD P p‖ ≤ CHf * JS := by
    intro p
    have h := psi_le_of_col P (CHf * n ^ 3) (JS / n ^ 3) (by positivity) (by positivity) hHcol hJs p
    have e : CHf * n ^ 3 * (JS / n ^ 3) = CHf * JS := by field_simp
    rwa [e] at h
  have hθ0 : 0 ≤ θ := Num.hθ.le
  let pd0 : PsiBd ell k Lu U θ :=
    { ψ := psiD P
      S := CHf * JS
      K := K2f / n ^ 2
      νψ := nuPsi ell a t ρ β θ Num.hc Num.hK Num.hEG
      δψ := deltaPsi ell a t ρ β θ Num.hc Num.hK Num.hEG
      hS := by positivity
      hK := by positivity
      hψ := hψ
      hC := hK2
      hνψ := by
        apply le_of_eq
        unfold nuPsi
        rw [← hCHf, ← hJS, ← hK2f]
        simp only [hndef]
        field_simp
      hδψ := by
        apply le_of_eq
        unfold deltaPsi nuPsi
        rw [← hCHf, ← hJS, ← hK2f]
        simp only [hndef]
        field_simp }
  -- premise 4: hH1col
  have hH1col : ∀ (e' : Bond Lu) (v : SuTwo),
      ∑ b, ‖(P.H1in (WithLp.toLp 2 (Pi.single e' v) : BondFnL2 Lu)) b‖
        ≤ (CH1free ell a t ρ θ Num.hc (nuPsi ell a t ρ β θ Num.hc Num.hK Num.hEG)
            (deltaPsi ell a t ρ β θ Num.hc Num.hK Num.hEG) Num.hν Num.hδ Num.hK Num.hcg1 Num.hEG1 * n ^ 3) * ‖v‖ := by
    intro e' v
    exact hH1col_M0 ell k Lu U a t e q0 R H θ Num.hθ Num.hc Lam (fun _ => pd0) (fun _ => rfl)
      (nuPsi ell a t ρ β θ Num.hc Num.hK Num.hEG) (deltaPsi ell a t ρ β θ Num.hc Num.hK Num.hEG)
      (fun _ => rfl) (fun _ => rfl) Num.hν Num.hδ Num.hcg1 Num.hEG1 Num.hN1 e' v
  -- premise 5: hKDb
  have hKDb : ∀ B : BondFnL2 Lu, ∑ e', ‖(P.D2in B) e'‖ ≤ KDfree ell * ‖B‖ ^ 2 :=
    fun B => hKDb_M0 ell k Lu hell U a t e q0 R H HU hd Lam Num.hKDc B
  -- the smallness ε' < 1 in the DL5 form
  have hε'e : 2 * ((CHf * n ^ 3) * (JS / n ^ 3)) * (K2f / n ^ 2) * (n ^ 2 * KhatM0 ell a t ρ)
      = eps2free Num := by
    unfold eps2free; rw [← hCHf, ← hJS, ← hK2f]; field_simp
  have hεJe : KDfree ell * ((CH1free ell a t ρ θ Num.hc (nuPsi ell a t ρ β θ Num.hc Num.hK Num.hEG)
        (deltaPsi ell a t ρ β θ Num.hc Num.hK Num.hEG) Num.hν Num.hδ Num.hK Num.hcg1 Num.hEG1 * n ^ 3) * (JS / n ^ 3))
      = epsJfree Num := by
    unfold epsJfree; rw [← hJS]; field_simp
  have hCH1f0 : 0 ≤ CH1free ell a t ρ θ Num.hc (nuPsi ell a t ρ β θ Num.hc Num.hK Num.hEG)
      (deltaPsi ell a t ρ β θ Num.hc Num.hK Num.hEG) Num.hν Num.hδ Num.hK Num.hcg1 Num.hEG1 := by
    unfold CH1free
    have : 0 ≤ qBS ell a ρ := by unfold qBS; positivity
    have := Num.hc.δBS_nonneg
    have : 0 < 1 / bN1 ell a t ρ θ Num.hc (nuPsi ell a t ρ β θ Num.hc Num.hK Num.hEG)
        - EN1free ell a t ρ θ Num.hc (nuPsi ell a t ρ β θ Num.hc Num.hK Num.hEG)
            (deltaPsi ell a t ρ β θ Num.hc Num.hK Num.hEG) Num.hν Num.hδ Num.hK Num.hcg1 Num.hEG1 := by
      linarith [Num.hN1]
    have := Num.hcg1
    have := Num.hc.ha
    positivity
  have h := instIneq_M0_D ell k Lu hell U a t e q0 R H HU hstrict hd Lam hLB
    (JS / n ^ 3) (CHf * n ^ 3) (K2f / n ^ 2)
    (CH1free ell a t ρ θ Num.hc (nuPsi ell a t ρ β θ Num.hc Num.hK Num.hEG)
      (deltaPsi ell a t ρ β θ Num.hc Num.hK Num.hEG) Num.hν Num.hδ Num.hK Num.hcg1 Num.hEG1 * n ^ 3)
    (KDfree ell) (by positivity) (by positivity) (by positivity) (by positivity) (KDfree_nonneg ell)
    hJs hHcol hK2 hH1col hKDb (by rw [hε'e]; exact Num.hε')
  rw [hε'e, hεJe] at h
  exact h

#print axioms CHfree_nonneg
#print axioms K2free_nonneg
#print axioms instIneq_M0_class_unconditional

end AdalyFormal.DLayer
