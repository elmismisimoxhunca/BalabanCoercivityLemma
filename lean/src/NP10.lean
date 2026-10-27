import NP9

/-!
# NP10 -- local W3 at a real patch, at the real NON-FLAT configuration (m1_patch_nonflat, 2026-10-14)

* `w3loc_any` : NP8 `w3loc_chart` on any torus `L` with `ell^{i+1} ∣ L μ + 1` (W2F `exists_scaleUp`, `subst`).
* `smallA` : one `a₀ ∈ (0, 1/2]` (depending on `ell, a, Ci` only) such that `α = 2 a'` satisfies every WN8/WN11 smallness
  condition at `rhoM1 ell α` whenever `0 ≤ a' ≤ a₀`.
The real-patch instance built from these is NP11 `inst_local`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M1NonFlat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.SuTwoLogExp (M2)
open AdalyFormal.StatementLane (Tower BlockClosed Admissible bigSide pdist scaleUp)
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle pdist_shift_le)
open AdalyFormal.M1Patch (patchTower LemIFlat Kflat)
open AdalyFormal.CurvBlock (dv pw)
open AdalyFormal.RegBgKU (KUSmall kapHat)
open AdalyFormal.AsmM0 (rhoM0)
open AdalyFormal.W3NF (lamC ThetaP KG0 KG0_pos rhoM1 rho_M1_eq smallness small_of_continuous continuous_hs6 hs6_zero
  Kflat_pos)
open AdalyFormal.M1W2 (locG0)
open AdalyFormal.M1 (gsp)
open AdalyFormal.M1Decay (ramp ramp_nonneg ramp_le_one ramp_one ramp_zero ramp_lip pdist_back_le)

variable {L : PeriodicLatticeExtent}

/-- the fixed first-difference size. -/
noncomputable def thetaN (ell : ℕ) : ℝ := (3 + 2 * Real.pi) * (ell : ℝ) ^ 2

theorem thetaN_nonneg (ell : ℕ) : 0 ≤ thetaN ell := by unfold thetaN; have := Real.pi_pos; positivity

theorem w3loc_any {ell : ℕ} (hell : 2 ≤ ell) {a Ci : ℝ} (ha : 0 < a) (hCi : 0 ≤ Ci) (hI : LemIFlat ell a Ci)
    (i : ℕ) (hdvd : ∀ μ : Fin 3, ell ^ (i + 1) ∣ L μ + 1) (Rg : Set (PeriodicLatticeSite L))
    (hRg : BlockClosed (ell ^ (i + 1)) Rg) (V : Cfg L) (e q0 θ : ℝ) (he0 : 0 ≤ e) (hq0 : 0 ≤ q0) (hθ : 0 ≤ θ)
    (hlinks : ∀ b, dv (V b) ≤ e) (h0 : ∀ y ν μ, dv (pw 1 V y ν μ) ≤ q0)
    (hlinkθ : e ≤ θ / (ell : ℝ) ^ (i + 1))
    (hdiff : ∀ (x : PeriodicLatticeSite L) (μ : Fin 3),
      frobNorm (((V (x, μ) : SU2) : Matrix (Fin 2) (Fin 2) ℂ)
        - ((V (periodicLatticeShiftBack x μ, μ) : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) ≤ θ / ((ell : ℝ) ^ (i + 1)) ^ 2)
    (H : KUSmall ell (rhoM0 ell (i + 1) e q0))
    (hs1 : 432 * kapHat ell (rhoM0 ell (i + 1) e q0) ^ 2 ≤ 1)
    (hs2 : kapHat ell (rhoM0 ell (i + 1) e q0) ≤ 1 / (1000 * (ell : ℝ) ^ 3))
    (hs3 : kapHat ell (rhoM0 ell (i + 1) e q0) ≤ 1)
    (hs4 : 324 * lamC ell * kapHat ell (rhoM0 ell (i + 1) e q0) ≤ 1)
    (hs5 : 2 * ThetaP ell a (kapHat ell (rhoM0 ell (i + 1) e q0)) ≤ 1 / Kflat a Ci)
    (hs6 : 8 * (272 * (kapHat ell (rhoM0 ell (i + 1) e q0) / (3 * Real.pi)) / (4 * Real.sqrt 2)) ≤ 1 / Kflat a Ci)
    (d : ℕ) (hd : 12 * ell + 10 ≤ d) (w : PeriodicLatticeSite L) (s : ℕ) (A : BondFnL2 L)
    (hA : ∀ b : Bond L, (WithLp.ofLp A) b ≠ 0 → b.1 ∈ Ball w s ∨ periodicLatticeShift b.1 b.2 ∈ Ball w s) :
    (1 / ((ell : ℝ) ^ 2 * KG0 a Ci) - epsNF ell (PkA a) θ d) * AdalyFormal.M1.wnormSq (patchTower i Rg) ell (i + 1) A
      ≤ locG0 (patchTower i Rg) ell (i + 1) V a (Ball w (s + d * ell ^ i)) A := by
  obtain ⟨Lu', hL⟩ := AdalyFormal.M1W2.exists_scaleUp ell (i + 1) (by omega) L hdvd
  subst hL
  exact w3loc_chart hell i Lu' Rg hRg V e q0 θ he0 hq0 hθ hlinks h0 hlinkθ hdiff H hs1 hs2 ha hCi hI hs3 hs4 hs5 hs6
    d hd w s A hA

/-- **one smallness radius**. -/
theorem smallA (ell : ℕ) (hell : 2 ≤ ell) (a Ci : ℝ) (ha : 0 < a) (hCi : 0 ≤ Ci) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ a₀ ≤ 1 / 2 ∧ ∀ a' : ℝ, 0 ≤ a' → a' ≤ a₀ →
      KUSmall ell (rhoM1 ell (2 * a')) ∧
      432 * kapHat ell (rhoM1 ell (2 * a')) ^ 2 ≤ 1 ∧
      kapHat ell (rhoM1 ell (2 * a')) ≤ 1 / (1000 * (ell : ℝ) ^ 3) ∧
      kapHat ell (rhoM1 ell (2 * a')) ≤ 1 ∧
      324 * lamC ell * kapHat ell (rhoM1 ell (2 * a')) ≤ 1 ∧
      2 * ThetaP ell a (kapHat ell (rhoM1 ell (2 * a'))) ≤ 1 / Kflat a Ci ∧
      8 * (272 * (kapHat ell (rhoM1 ell (2 * a')) / (3 * Real.pi)) / (4 * Real.sqrt 2)) ≤ 1 / Kflat a Ci := by
  obtain ⟨δ1, hδ1, hsm⟩ := smallness ell hell a Ci ha hCi
  obtain ⟨δ2, hδ2, hsm6⟩ := small_of_continuous (continuous_hs6 ell) (hs6_zero ell)
    (show 0 < 1 / Kflat a Ci by have := Kflat_pos ha hCi; positivity)
  refine ⟨min (min δ1 δ2) 1 / 2, by positivity, by
    have := min_le_right (min δ1 δ2) 1; linarith, fun a' ha0 ha' => ?_⟩
  have h2 : 2 * a' ≤ min (min δ1 δ2) 1 := by linarith
  have hd1 : 2 * a' ≤ δ1 := h2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hd2 : 2 * a' ≤ δ2 := h2.trans ((min_le_left _ _).trans (min_le_right _ _))
  obtain ⟨-, hKU, hs1, hs2, hs3, hs4, hs5⟩ := hsm (2 * a') (by linarith) hd1
  exact ⟨hKU, hs1, hs2, hs3, hs4, hs5, (hsm6 (2 * a') (by linarith) hd2).le⟩

end AdalyFormal.M1NonFlat

#print axioms AdalyFormal.M1NonFlat.w3loc_any
#print axioms AdalyFormal.M1NonFlat.smallA
