import DLR56

/-!
# DL57 -- **`J_local_bound`**: `‖J(x,μ)‖ ≤ η³ (a₃ + 40a₁a₂ + 4144a₁³ + 8192ηa₁⁴)` from a local representation `U = e^{iηA}`

* `LocRep.Dstar_err` : for `ν ≠ μ`, `‖D*_ν F_{νμ}(x) − η²(curlA(x−ν;ν,μ) − curlA(x;ν,μ))‖ ≤ η³(20a₁a₂ + 2072a₁³ + 4096ηa₁⁴)`
  (transport `‖WFWᴴ − F‖ ≤ 2‖W−1‖‖F‖`, commutator DIFFERENCES via clause 2, cubic remainders);
* **`LocRep.J_local_bound`** : summed over the two `ν ≠ μ`, with `Σ_ν η²(curlA(x−ν) − curlA(x)) = η³ ddA` (clause 3).
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 20000

namespace AdalyFormal.DLayer

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm frobSq_nonneg frobNorm_nonneg frobNorm_sq)
open AdalyFormal.Balaban.SourceJ (piProj FnuMu DstarDir Jfield)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack
  periodicLatticeShiftBack_shift)
open AdalyFormal.Balaban.CovariantOperators (conjByAmbient)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 coe_inv)
open AdalyFormal.StatementLane2 (curlA ddA)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

local notation "Mt" => Matrix (Fin 2) (Fin 2) ℂ

variable {L : PeriodicLatticeExtent}

theorem transport_le (W X : Mt) (hW1 : W * Wᴴ = 1) (hW2 : Wᴴ * W = 1) :
    frobNorm (W * X * Wᴴ - X) ≤ 2 * frobNorm (W - 1) * frobNorm X := by
  have e : W * X * Wᴴ - X = (W - 1) * X * Wᴴ + X * (Wᴴ - 1) := by
    noncomm_ring
  rw [e]
  refine (fN_add _ _).trans ?_
  have h1 : frobNorm ((W - 1) * X * Wᴴ) = frobNorm ((W - 1) * X) := by
    apply fN_mul_unitary
    rw [Matrix.conjTranspose_conjTranspose]; exact hW2
  have h2 : frobNorm (X * (Wᴴ - 1)) ≤ frobNorm X * frobNorm (W - 1) := by
    refine (fN_mul _ _).trans (le_of_eq ?_)
    congr 1
    rw [show Wᴴ - 1 = (W - 1)ᴴ by rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one], fN_conjT]
  rw [h1]
  have h3 := fN_mul (W - 1) X
  nlinarith [frobNorm_nonneg X, frobNorm_nonneg (W - 1)]

section Local
variable {V : PeriodicLinkConfiguration SU2 L} {η : ℝ} {A : Bond L → Mt} {a1 a2 : ℝ} {InC : Bond L → Prop}

/-- the seven bonds that `D*_ν F_{νμ}(x)` reads, stated at `x = y+ν` -/
def NeedBonds (InC : Bond L → Prop) (y : PeriodicLatticeSite L) (ν μ : Fin 3) : Prop :=
  InC (y, ν) ∧ InC (periodicLatticeShift y ν, μ) ∧ InC (periodicLatticeShift y μ, ν) ∧ InC (y, μ)
  ∧ InC (periodicLatticeShift y ν, ν) ∧ InC (periodicLatticeShift (periodicLatticeShift y ν) ν, μ)
  ∧ InC (periodicLatticeShift (periodicLatticeShift y ν) μ, ν)

theorem LocRep.Dstar_err (h : LocRep V η A a1 a2 InC) (ν μ : Fin 3) (hνμ : ν ≠ μ) (y : PeriodicLatticeSite L)
    (hb : NeedBonds InC y ν μ) :
    frobNorm (DstarDir V ν (fun z => FnuMu V ν μ z) (periodicLatticeShift y ν)
        - (η ^ 2 : ℝ) • (curlA η A y ν μ - curlA η A (periodicLatticeShift y ν) ν μ))
      ≤ η ^ 3 * (20 * a1 * a2 + 2072 * a1 ^ 3 + 4096 * η * a1 ^ 4) := by
  obtain ⟨b1, b2, b3, b4, c1, c2, c3⟩ := hb
  have hη := h.hη
  have ha1 := h.a1_nonneg _ b1
  have ha2 : 0 ≤ a2 := le_trans (frobNorm_nonneg _) (h.h2 y μ ν b4 b2)
  set x := periodicLatticeShift y ν with hx
  -- the bonds at x, in F_expand's form
  have d4 : InC (x, μ) := b2
  have d1 : InC (x, ν) := c1
  have d2 : InC (periodicLatticeShift x ν, μ) := c2
  have d3 : InC (periodicLatticeShift x μ, ν) := c3
  obtain ⟨R', hF', hR'⟩ := h.F_expand ν μ hνμ y b1 b2 b3 b4
  obtain ⟨R, hF, hR⟩ := h.F_expand ν μ hνμ x d1 d2 d3 d4
  have hback : periodicLatticeShiftBack x ν = y := periodicLatticeShiftBack_shift y ν
  -- the transport element
  set W : Mt := (((V (y, ν))⁻¹ : SU2) : Mt) with hW
  have hHy : AHT (Hof η A (y, ν)) := HT_AHT η (A (y, ν)) (h.ht _ b1)
  have hWexp : W = NormedSpace.exp (-Hof η A (y, ν)) := by
    rw [hW, coe_inv, h.rep _ b1]; exact exp_conjT (Hof η A (y, ν)) hHy
  have hW1 : W * Wᴴ = 1 := by rw [hWexp]; exact exp_unitary _ hHy.neg
  have hW2 : Wᴴ * W = 1 := by
    rw [hWexp, exp_conjT _ hHy.neg, neg_neg]
    have := exp_unitary _ hHy
    rw [exp_conjT _ hHy] at this; exact this
  have hW1le : frobNorm (W - 1) ≤ 2 * (η * a1) := by
    rw [hWexp]
    have hHle := h.H_le _ b1
    have hsm : frobNorm (-Hof η A (y, ν)) ≤ 1 := by
      rw [fN_neg]; nlinarith [h.small]
    refine (exp_sub_one_le _ hHy.neg hsm).trans ?_
    rw [fN_neg]; linarith
  have hD : DstarDir V ν (fun z => FnuMu V ν μ z) x = W * FnuMu V ν μ y * Wᴴ - FnuMu V ν μ x := by
    unfold DstarDir
    rw [hback]
    rfl
  rw [hD, hF', hF]
  -- regroup
  set M' := (η ^ 2 : ℝ) • curlA η A y ν μ with hM'
  set M := (η ^ 2 : ℝ) • curlA η A x ν μ with hM
  set K' := Kpl (Hof η A) ν μ y with hK'
  set K := Kpl (Hof η A) ν μ x with hK
  have e : W * (M' + K' + R') * Wᴴ - (M + K + R) - (η ^ 2 : ℝ) • (curlA η A y ν μ - curlA η A x ν μ)
      = (W * (M' + K' + R') * Wᴴ - (M' + K' + R')) + (K' - K) + (R' - R) := by
    rw [hM', hM, smul_sub]; abel
  rw [e]
  -- the pieces
  have hcurl' : frobNorm (curlA η A y ν μ) ≤ 2 * a2 := h.curl_le y ν μ b1 b2 b3 b4
  have hKl' : frobNorm K' ≤ 6 * (η * a1) ^ 2 := h.Kpl_le ν μ y b1 b2 b3 b4
  have hG' : frobNorm (M' + K' + R') ≤ η ^ 2 * (2 * a2) + 6 * (η * a1) ^ 2 + 1024 * η ^ 3 * a1 ^ 3 := by
    refine (fN_add _ _).trans ?_
    refine (add_le_add (fN_add _ _) hR').trans ?_
    rw [hM', fN_rsmul, abs_of_nonneg (by positivity)]
    have := mul_le_mul_of_nonneg_left hcurl' (by positivity : (0 : ℝ) ≤ η ^ 2)
    linarith
  have ht := transport_le W (M' + K' + R') hW1 hW2
  have ht' : frobNorm (W * (M' + K' + R') * Wᴴ - (M' + K' + R'))
      ≤ 2 * (2 * (η * a1)) * (η ^ 2 * (2 * a2) + 6 * (η * a1) ^ 2 + 1024 * η ^ 3 * a1 ^ 3) := by
    refine ht.trans ?_
    have := mul_le_mul hW1le hG' (frobNorm_nonneg _) (by positivity)
    nlinarith
  -- the commutator difference
  have hKd : frobNorm (K' - K) ≤ 12 * (η * a1) * (η ^ 2 * a2) := by
    have hHle : ∀ e, InC e → frobNorm (Hof η A e) ≤ η * a1 := fun e he => h.H_le e he
    have hneg : ∀ e, InC e → frobNorm (-Hof η A e) ≤ η * a1 := fun e he => by rw [fN_neg]; exact hHle e he
    have hd : ∀ (z : PeriodicLatticeSite L) (dd : Fin 3), InC (z, dd) → InC (periodicLatticeShift z ν, dd) →
        frobNorm (Hof η A (z, dd) - Hof η A (periodicLatticeShift z ν, dd)) ≤ η ^ 2 * a2 :=
      fun z dd h0 h1 => h.H_diff z dd ν h0 h1
    have hdn : ∀ (z : PeriodicLatticeSite L) (dd : Fin 3), InC (z, dd) → InC (periodicLatticeShift z ν, dd) →
        frobNorm (-Hof η A (z, dd) - -Hof η A (periodicLatticeShift z ν, dd)) ≤ η ^ 2 * a2 := by
      intro z dd h0 h1
      rw [show -Hof η A (z, dd) - -Hof η A (periodicLatticeShift z ν, dd)
          = -(Hof η A (z, dd) - Hof η A (periodicLatticeShift z ν, dd)) by abel, fN_neg]
      exact hd z dd h0 h1
    have hhalf : ‖(1 / (2 * Complex.I) : ℂ)‖ = 1 / 2 := by simp
    -- shifted forms of the x-bonds
    have sx : periodicLatticeShift (periodicLatticeShift y μ) ν = periodicLatticeShift x μ := by
      rw [hx, shift_comm]
    rw [hK', hK]
    unfold Kpl
    split_ifs with hlt
    · rw [← smul_sub, fN_csmul, hhalf]
      have := Kc_diff _ _ _ _ _ _ _ _ (η * a1) (η ^ 2 * a2)
        (hHle _ b1) (hHle _ b2) (hneg _ b3) (hneg _ b4) (hHle _ d1) (hHle _ d2) (hneg _ d3) (hneg _ d4)
        (by have := hd y ν b1 c1; rwa [← hx] at this)
        (by have := hd x μ b2 c2; exact this)
        (by have := hdn (periodicLatticeShift y μ) ν b3 (by rw [sx]; exact d3); rwa [sx] at this)
        (by have := hdn y μ b4 b2; rwa [← hx] at this)
      linarith
    · rw [neg_sub_neg, ← smul_sub, fN_csmul, hhalf]
      set Ky := Kc (Hof η A (y, μ)) (Hof η A (periodicLatticeShift y μ, ν))
        (-Hof η A (periodicLatticeShift y ν, μ)) (-Hof η A (y, ν)) with hKy
      set Kx := Kc (Hof η A (x, μ)) (Hof η A (periodicLatticeShift x μ, ν))
        (-Hof η A (periodicLatticeShift x ν, μ)) (-Hof η A (x, ν)) with hKx
      have := Kc_diff _ _ _ _ _ _ _ _ (η * a1) (η ^ 2 * a2)
        (hHle _ b4) (hHle _ b3) (hneg _ b2) (hneg _ b1) (hHle _ d4) (hHle _ d3) (hneg _ d2) (hneg _ d1)
        (by have := hd y μ b4 b2; rwa [← hx] at this)
        (by have := hd (periodicLatticeShift y μ) ν b3 (by rw [sx]; exact d3); rwa [sx] at this)
        (by have := hdn x μ b2 c2; exact this)
        (by have := hdn y ν b1 c1; rwa [← hx] at this)
      rw [← hKy, ← hKx] at this
      have e2 : Kx - Ky = -(Ky - Kx) := by abel
      rw [e2, fN_neg]
      linarith
  have hRd : frobNorm (R' - R) ≤ 2048 * η ^ 3 * a1 ^ 3 := by
    refine (fN_sub _ _).trans ?_; linarith
  refine (fN_add _ _).trans ?_
  refine (add_le_add (fN_add _ _) hRd).trans ?_
  have := add_le_add ht' hKd
  nlinarith [mul_nonneg ha1 ha2, pow_nonneg ha1 3, pow_nonneg ha1 4, hη.le]

end Local

#print axioms transport_le
#print axioms LocRep.Dstar_err

end AdalyFormal.DLayer
