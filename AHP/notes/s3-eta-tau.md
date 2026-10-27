# S-3 — eta and tau-star units

Uncompiled draft: [Units.lean](/home/sebastian/BalabanCoercivityLemma/AHP/attempts/s3-eta-tau/Units.lean). Not a Lake root. Not compiled. Not a theorem of the project tree. Frozen files were not edited. The deviation table was not edited.

The frozen first term is `P.eta * ⟪τ* B, (Q data.G1 Q*)⁻¹ τ* B⟫` with `P.eta = ((ell:ℝ)^k)⁻¹` (`ZXG3A.genForm` / `firstTerm`, `ZXR2Wire2.eta`). Print (3.156) (`sources/corpus/pages/CMP99b_p428.md`) has neither symbol. `τ*` is not a unit. The factor `η` is a unit, and on the flat full-support theory it is the one that puts the first term in the same unit as `a⟨B,B⟩`.

## Verdict

| Summand | Same unit as the restored first term? |
|---|---|
| `a⟨B,B⟩` | Yes. No factor `η`. |
| Displayed `J` term `-2⟨H₁ D̃⁽²⁾(B), J⟩` | Yes in `d = 3`, for the pairing as written in `genForm`. Not inside `BaseDataS.K`. |
| `bondEnergy` | Yes. Same unweighted unit-bond sum as `⟨B,B⟩`. |

The three displayed real scalars are the same unit. The source summand inside the quadratic form `K` of `G₁⁻¹` is not.

## Why `η` stands only on the first term

`R2Ops1` builds `Δ`, `DRD*` and `Q*aQ` as the unweighted Riesz maps of the printed forms with `η^{d-2}` divided out. The project fixes `d = 3`, so `η^{d-2} = η = L^{-k}`. The mass weight in the code is `a * ell^j` (`ZXR2Ops3.massW`), which is `a_j (L^j η)^{d-2} / η^{d-2}`. At level `k` and full support, `ZGU1D.Gen.mass_inner` says `⟨A, Mass A⟩ = a * ell^k * ‖Q A‖²`.

`ZGU1E.Gen.genForm_reduction` (source text; not recompiled here) specialises this at flat `U`, full support, every `k`, with `G₁⁻¹` and `N` units. It sets `Jf = 0` and proves

\[
\mathrm{genForm}(B) = \eta\big(\lVert\mathrm{curl}\, A\rVert^2 + \lVert R D^* A\rVert^2\big),
\]

where `Q A = τ* B`. The proof line is `P.eta * (P.ell : ℝ) ^ P.k = 1`, and then

\[
\eta\cdot\big(a\cdot \ell^k\cdot \lVert B\rVert^2\big) = a\cdot\lVert B\rVert^2.
\]

So the mass piece of `firstTerm` equals `a⟨B,B⟩` exactly, at every `k`. Omitting `η` would leave a factor `ℓ^k` and the two summands would not match. `Units.lean` proves that rational cancellation and nothing about the frozen operators.

The same source text records `‖τ* B‖ = ‖B‖` on full support (`ZGU1D.Gen.tau_adj_norm`) and `tau_adj_apply`: `(τ* B)` at the embedded unit bond equals `B` at that bond. `τ*` changes the carrier from a unit-bond field to the top level of `𝔅`. The print already writes `B` as that element (p.427, “Unit Lattice Propagators”; (3.156) restricts to `B = 0` off `Λ` and off the axial bonds). No scalar is inserted. The absence of `τ*` from (3.156) is notational.

`G1in = η⁻¹ • ι • data.G1 • pE` (`ZXR2Wire2`) is a third normalisation. `unit_of_chain` rewrites `Qin G1in Qin*` as `η⁻¹` times `τ N τ*`, so the external `η` converts `firstTerm` into the `Ingr` pairing. That is internal. It is not the claim that `G1in` equals the printed covariance. The printed match of the scalar is the mass cancellation above: the variational value of the eta-free form, times `η^{d-2}`.

## `a⟨B,B⟩`

Confirm. `⟪B,B⟫` is the unweighted `PiLp 2` sum on unit bonds. With the formalisation’s convention `ℓ^k η = 1`, the printed weight at level `k` is `(L^k η)^{d-2} = 1` (the weight written in (3.24) / the bond form (3.16)). The printed `a⟨B,B⟩` is therefore the same unweighted sum. It must not carry another `η`. The flat reduction cancels it against the first term with coefficients `1` and `1`. `ZXG3D2.genFormMut_zeroMode` says the same thing at a flat zero mode: a mutant that rescales one coefficient and not the other does not vanish.

## Displayed `J` term

Confirm the coefficient in `genForm`, in `d = 3` only.

`Jf` is `- JSU2Loc 1` (`ZXR2Wire2`). `JSU2 η = (-i) η⁻³ • Jfield`, the `η⁻¹` from `D*` and the `η⁻²` from `J = D* η⁻² Im ∂U` (`ZIngredientJ`). The header there says the weight `η^d` is not in the field. The printed pairing is `∑_b η^d tr(A(b) J(b))` (p.392, (3.11)). Substituting `J(η) = η⁻³ J(1)` gives the ratio `η^{d-3}` between the printed scalar and the unweighted pairing against `JSU2(1)`. At `d = 3` the ratio is `1` (`Units.lean`, `j_pairing_ratio_d3`). No further `η` belongs in front of `-2⟨H1in (D2in B), Jf⟩`.

`D2in` multiplies by `ell⁻¹`, the one-step factor `h = L⁻¹ ι H₀⁻¹ ρ` of the lane’s reading of CMP109 p.267 (`ZXR2Wire2.D2in`). That power is `L`, not `L^k`. It does not change the `k`-unit relative to `a⟨B,B⟩`.

The minus sign on `Jf` is the chart remark in `ZXR2Wire2` (`J_su2 = -JSU2`). It is not an `η` power. This note does not decide the chart.

## Where the units do not match

Reject homogeneity inside `BaseDataS.K` (`R2Algebra.lean`):

\[
K(A) = \langle A,\Delta_\pi A\rangle - 2\langle H C^{(2)}(A), J\rangle + \lVert T A\rVert^2 + \langle A, \mathrm{Mass}\, A\rangle.
\]

The three quadratic pieces are the eta-free bodies, so they equal the printed quadratic form divided by `η`. The cross term uses `data.J = pE Jf` with `Jf = JSU2Loc 1`, whose unweighted pairing equals the full printed pairing in `d = 3`, not that pairing divided by `η`. Hence

\[
K_{\mathrm{lean}} = \frac{Q_{\mathrm{print}}}{\eta} - 2\, C_{\mathrm{print}} = \eta^{-1}\big(Q_{\mathrm{print}} - 2\eta\, C_{\mathrm{print}}\big)
\]

(`Units.lean`, `k_cross_not_homogeneous`). The `H` inside `K` is built from `G`, whose form is purely quadratic, so its minimiser agrees with the printed minimiser and does not hide a compensating `η`.

Effect on (3.156): the leading mass and gradient pieces of `firstTerm` stay in the unit of `a⟨B,B⟩`. The `Δ^{(2)}` correction inside `G₁` is the printed correction multiplied by an extra `η = L^{-k}`. `H1in` is built from that `G₁` (`R2Algebra.H1`), so the displayed `J` term inherits the same relative error in the correction and not in the normalisation of the pairing. At flat `U`, `Jf = 0` (`Jf_flat`), both the displayed `J` term and this defect vanish, and `genForm_reduction` applies.

## `bondEnergy`

Confirm. `bondEnergy A = ∑_b ‖A b‖²` on the bonds it is given. For `B : BondFnL2 Lu`, `⟪B,B⟫ = ‖B‖²` is that sum (`genForm_reduction` rewrites `⟪B,B⟫ = ‖B‖ ^ 2`). The norm is the `su(2)` norm whose square is half the Frobenius square (`norm_sq_eq_half_frobSq`), i.e. the printed trace with `tr 1 = 1`. The separate `√2` discrepancy of the class bounds (`frobNorm`) is not this pairing.

The inequality compares `bondEnergy Bt` with `genForm(C Bt)`. `C = id - h Q` is the identity off the dropped bonds (`ZXR2Unit2.Cop_id`) and uses the same one-step `ell⁻¹`, not `L^{-k}`. `⟨C Bt, C Bt⟩` and `bondEnergy Bt` are the same kind of sum; they are not claimed equal bondwise. A `k`-independent factor from the constraint solve can sit in `γ₀`. It is not an `η` mismatch.

## What this does not say

- Not recompiled. `compiled` is false. `genForm_reduction`, `mass_inner` and `constMode_form` (`PGFC1.lean`) were read, not run.
- No row was added to the deviation table.
- `η = ℓ^{-k}` remains a convention of the formalisation (`OPEN_ITEMS` D-12). The unit check assumes that convention, because that is how the frozen `eta` is defined.
- The check is `d = 3`. The code writes `ell^j` and multiplies by `ell^{-k}`, which equal `L^{j(d-2)}` and `η^{d-2}` only for `d - 2 = 1`.
- Nothing here is a coercivity bound, a statement about non-flat `U` beyond the `K` ratio, or a claim that `G1in` is the printed operator.
