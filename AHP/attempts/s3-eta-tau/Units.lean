/-!
# S-3 — eta and tau-star units (UNCOMPILED DRAFT)

This file is not a Lake root and was not compiled. Nothing here is a theorem of the
project tree. It does not import the frozen modules. No `sorry`, `admit`, `axiom`,
`native_decide`, `unsafe`, `implemented_by` or `extern`.

The arithmetic below is the scaling model of the frozen flat reduction
`AdalyFormal.GenuineU1.Gen.genForm_reduction` (`lean/src/ZGU1E.lean`). That source text
already contains

  `P.eta * (P.ell : ℝ) ^ P.k = 1`

and the mass cancellation

  `P.eta * (P.a * (P.ell : ℝ) ^ P.k * ‖B‖ ^ 2) = P.a * ‖B‖ ^ 2`

at flat `U`, full support, every level `k`, with `Jf = 0`. This session did not run Lean,
so that source lemma was not rechecked. The lemmas in this file prove only the same
rational arithmetic, plus the dimension-3 measure identity for the printed source pairing
and the failure of homogeneity inside `BaseDataS.K`.

Readings the model is copied from (not re-proved):

* `GenP.firstTerm` = `P.eta * ⟪τ* B, N⁻¹ τ* B⟫`, `P.eta = ((ell : ℝ) ^ k)⁻¹`
  (`lean/src/ZXG3A.lean`, `lean/src/ZXR2Wire2.lean`).
* `GenP.genForm` = `firstTerm - a⟪B,B⟫ - 2⟪H1in (D2in B), Jf⟫` (`ZXG3A.lean`).
* `mass_inner`: `⟪A, Mass A⟫ = a * ell^k * ‖Q A‖²` at full support (`ZGU1D.lean`).
  The weight `ell^j` is the `d = 3` case of `L^{j(d-2)}` (`ZXR2Ops3.massW`).
* `τ*` copies su(2) values; `tau_adj_norm` gives `‖τ* B‖ = ‖B‖` on full support
  (`ZGU1D.lean`). No factor `η`.
* `Jf` is `JSU2Loc 1`, and `JSU2 η = (-i) η⁻³ • Jfield` (`ZXR2Wire2.lean`,
  `ZIngredientJ.lean`). The printed pairing carries `η^d` (`sources/corpus/pages/CMP99b_p392.md`,
  (3.11)). At `d = 3` those powers cancel. The sign in `Jf` is the lane's chart, not a unit.
* `bondEnergy A = ∑_b ‖A b‖²` (`RegularUPerturbation.lean`). For a `PiLp 2` field this is
  `⟪B,B⟫`.
-/

namespace AdalyFormal.AHP.S3EtaTau

/-- The frozen prefactor `η = L^{-k}`. -/
def eta (L k : ℕ) : ℚ := ((L : ℚ) ^ k)⁻¹

/-- `η * L^k = 1` whenever `L ≠ 0`. This is the identity named in `genForm_reduction`. -/
theorem eta_mul_pow (L k : ℕ) (hL : (L : ℚ) ≠ 0) :
    eta L k * ((L : ℚ) ^ k) = 1 := by
  unfold eta
  exact inv_mul_cancel₀ (pow_ne_zero k hL)

/-- Mass piece of the first term, before `η`: the full-support weight `a * L^k * E`. -/
def massPiece (L k : ℕ) (a E : ℚ) : ℚ := a * ((L : ℚ) ^ k) * E

/-- After the frozen prefactor, that piece equals `a * E`, with no leftover power of `L^k`. -/
theorem firstTerm_mass_eq_aE (L k : ℕ) (a E : ℚ) (hL : (L : ℚ) ≠ 0) :
    eta L k * massPiece L k a E = a * E := by
  unfold massPiece
  have hk : ((L : ℚ) ^ k) ≠ 0 := pow_ne_zero k hL
  have hreorder : a * ((L : ℚ) ^ k) * E = ((L : ℚ) ^ k) * (a * E) := by
    rw [mul_assoc, mul_left_comm a]
  rw [hreorder, ← mul_assoc, eta_mul_pow L k hL, one_mul]

/-- The `a⟨B,B⟩` summand carries no `η`. Same value as the cancelled mass piece. -/
theorem aTerm_matches_cancelled_mass (L k : ℕ) (a E : ℚ) (hL : (L : ℚ) ≠ 0) :
    eta L k * massPiece L k a E - a * E = 0 := by
  rw [firstTerm_mass_eq_aE L k a E hL, sub_self]

/-- Dropping `η` leaves the mass weight `L^k` in front of `a * E`. -/
theorem firstTerm_without_eta (L k : ℕ) (a E : ℚ) :
    massPiece L k a E = ((L : ℚ) ^ k) * (a * E) := by
  unfold massPiece
  rw [mul_assoc, mul_left_comm a]

/-- Printed source pairing over the unweighted pairing of `JSU2(1)`.
At `d = 3`, `η^d * η^{-3} = 1`. In any other dimension the ratio is `η^{d-3}`. -/
theorem j_pairing_ratio_d3 (η : ℚ) (hη : η ≠ 0) :
    η ^ 3 * (η ^ 3)⁻¹ = (1 : ℚ) :=
  mul_inv_cancel₀ (pow_ne_zero 3 hη)

/-- Printed pairing / unweighted pairing of `JSU2(1)` equals `η^{d-3}`.
It is `1` for every `η ≠ 0` only when `d = 3`. -/
theorem j_ratio_eq_eta_pow (d : ℕ) (η : ℚ) (hη : η ≠ 0) (hd : 3 ≤ d) :
    η ^ d * (η ^ 3)⁻¹ = η ^ (d - 3) := by
  have h3 : η ^ d = η ^ ((d - 3) + 3) := by
    congr 1
    exact (Nat.sub_add_cancel hd).symm
  rw [h3, pow_add, mul_assoc, j_pairing_ratio_d3 η hη, mul_one]

/-- Inside `BaseDataS.K` the quadratic part was divided by `η^{d-2} = η` and the source
pairing was not. The lean form is the printed quadratic part over `η`, minus the full
printed cross term, which is `η^{-1}` times (printed quadratic part minus `η` times the
cross term). -/
theorem two_cross (η c : ℚ) (hη : η ≠ 0) :
    η⁻¹ * (2 * (η * c)) = 2 * c := by
  have hcomm : 2 * (η * c) = η * (2 * c) := by
    rw [← mul_assoc, mul_comm 2 η, mul_assoc]
  rw [hcomm, ← mul_assoc, inv_mul_cancel₀ hη, one_mul]

theorem k_cross_not_homogeneous (η q c : ℚ) (hη : η ≠ 0) :
    q / η - 2 * c = η⁻¹ * (q - 2 * (η * c)) := by
  rw [div_eq_mul_inv, mul_comm q, mul_sub, two_cross η c hη]

end AdalyFormal.AHP.S3EtaTau
