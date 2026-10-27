import MF7

/-!
# MF9 -- the class form: one constant `γ₀(ᾱ)` for EVERY `k`, every torus, every `U` of the M0 class with parameter `α₀ ≤ ᾱ`.

The M0 class at scale `η = ell⁻ᵏ`: fine links `dv(U b) ≤ ᾱ η`, fine plaquettes `dv(U(∂p)) ≤ ᾱ η²` (one gauge, whole torus).
With `e = ᾱ ell⁻ᵏ`, `q0 = ᾱ ell⁻²ᵏ` as the BOUNDS of `M0RegimeR`, `ρ = rhoM0 ell k e q0 = (1+3π) ᾱ` for every `k` (`rhoM0_class`), so the
constant of `instIneq_M0_kuniform` is `γ₀ = gam0M0 ell a t ((1+3π)ᾱ) ε2s εJ (dCM0 ..) (cBM0 ..)`: a function of `(ell, a, t, ᾱ, ε2s, εJ)` only,
fixed BEFORE `k`, `Lu`, `U`, `Λ`, `B̃` (the headline's binder order for `γ₀`). The D-layer premises (`hD2`, `hJ`) remain premises.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.M0Finish

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp OnLambdaTildeIn)
open AdalyFormal.StatementLane2 (OnLambdaT)
open AdalyFormal.StatementLaneG (LamBlockSum InstIneq)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.AsmM0
open AdalyFormal.CurvBlock (dv)
open AdalyFormal.RegBgKU (KUSmall)

theorem rhoM0_class (ell k : ℕ) (hell : 0 < ell) (α : ℝ) :
    rhoM0 ell k (α / (ell : ℝ) ^ k) (α / ((ell : ℝ) ^ k) ^ 2) = (1 + 3 * Real.pi) * α := by
  unfold rhoM0
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := pow_pos (by exact_mod_cast hell) k
  field_simp

/-- **`InstIneq` on the M0 class with a constant fixed before `k`, `Lu`, `U`** (D-layer still a premise). -/
theorem instIneq_M0_class (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (hell2 : 2 ≤ ell)
    (U : Cfg (scaleUp ell k Lu)) (a t α : ℝ) (ha : 0 < a) (ht : 0 < t) (hα : 0 ≤ α)
    (hstrict : ∀ μ : Fin 3, ell < Lu μ + 1) (hd : ∀ μ, ell ∣ Lu μ + 1)
    (Lam : Set (PeriodicLatticeSite Lu)) (hLB : LamBlockSum ell Lam)
    -- the class (one gauge, whole torus)
    (hlinks : ∀ b, dv (U b) ≤ α / (ell : ℝ) ^ k)
    (hplaq : ∀ p : PeriodicLatticePlaquette (scaleUp ell k Lu), dv (periodicPlaquetteHolonomy U p) ≤ α / ((ell : ℝ) ^ k) ^ 2)
    -- k-free smallness of α (all in ρ = (1+3π)α)
    (hcb : 4000000 * (ell : ℝ) ^ 2 * α ≤ 1)
    (h216 : 216 * ((1 + 3 * Real.pi) * α) ^ 2 < 1)
    (h1000 : (1 + 3 * Real.pi) * α ≤ 1 / (1000 * (ell : ℝ) ^ 3))
    (hsmallU : ThetaM0 ell a t ((1 + 3 * Real.pi) * α) < min a 1 / 1000)
    (H : KUSmall ell ((1 + 3 * Real.pi) * α)) (HU : UnitSmall ell ((1 + 3 * Real.pi) * α))
    -- the D-layer (NOT proved)
    (ε2s εJ : ℝ) (hε2s : 0 ≤ ε2s) (hεJ : 0 ≤ εJ)
    (hε' : ε2s * KhatM0 ell a t ((1 + 3 * Real.pi) * α) < 1)
    (hD2 : ‖(PU ell k Lu hell U a Lam).data.Delta2 (PU ell k Lu hell U a Lam).data_laws‖
      ≤ ε2s / ((ell : ℝ) ^ k) ^ 2)
    (hJ : ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
        |⟪(PU ell k Lu hell U a Lam).H1in ((PU ell k Lu hell U a Lam).D2in
            (WithLp.toLp 2 (Cop Lam (PU ell k Lu hell U a Lam).Q1 Bt))), (PU ell k Lu hell U a Lam).Jf⟫|
          ≤ εJ * ‖(WithLp.toLp 2 (Cop Lam (PU ell k Lu hell U a Lam).Q1 Bt) : BondFnL2 Lu)‖ ^ 2) :
    InstIneq ell k hell a Lu
      (gam0M0 ell a t ((1 + 3 * Real.pi) * α) ε2s εJ (dCM0 ell ((1 + 3 * Real.pi) * α))
        (cBM0 ell ((1 + 3 * Real.pi) * α)))
      (fullTower ell k Lu) Lam U := by
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := pow_pos (by exact_mod_cast hell) k
  have hρ := rhoM0_class ell k hell α
  set e := α / (ell : ℝ) ^ k with he
  set q0 := α / ((ell : ℝ) ^ k) ^ 2 with hq0
  have R : M0RegimeR ell k Lu U a t e q0 := by
    refine ⟨hell2, ha, ht, by positivity, by positivity, ?_, hlinks, hplaq, ?_, by rw [hρ]; exact h216,
      by rw [hρ]; exact h1000, by rw [hρ]; exact hsmallU⟩
    · intro ρ'
      have h1 : scaleUp ell k Lu ρ' + 1 = (Lu ρ' + 1) * ell ^ k :=
        AdalyFormal.IngredientFamilyR2.scaleUp_succ ell k Lu hell ρ'
      have h2 : 3 ≤ Lu ρ' + 1 := by have := hstrict ρ'; omega
      have h3 := Nat.mul_le_mul_right (ell ^ k) h2
      have h4 : 0 < ell ^ k := pow_pos hell k
      omega
    · have e1 : ((ell : ℝ) ^ 2) ^ k * q0 = α := by
        rw [hq0, ← pow_mul, mul_comm 2 k, pow_mul]; field_simp
      rw [e1]; exact hcb
  have h := instIneq_M0_kuniform ell k Lu hell U a t e q0 R (by rw [hρ]; exact H) (by rw [hρ]; exact HU)
    hstrict hd Lam hLB ε2s εJ hε2s hεJ (by rw [hρ]; exact hε') hD2 hJ
  rw [hρ] at h
  exact h

#print axioms rhoM0_class
#print axioms instIneq_M0_class

end AdalyFormal.M0Finish
