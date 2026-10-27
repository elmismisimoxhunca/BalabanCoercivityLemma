# Positivity R2 — P2 proved for the actual full right-star carrier

## Verdict and verification boundary

**P2 is CLOSED by clean builder compilations.** This is an unconditional proof of the exact original P2, not a conditional absorption criterion. **P3 and GoalNeg2 are not proved by this track.** No strict claim at the endpoint `pi/2` is made or needed: positivity includes zero and every angle strictly below `pi/2`, hence every closed prefix ending at the crossing once the proved crossing-range theorem is used.

The final local and shared sources were each executed separately through `bb heavy run -- AHP/round3/lean1.sh`, sequentially. All four exits are 0, all logs have no warnings/errors, and all printed dependencies are subsets of `{propext, Classical.choice, Quot.sound}`. These are builder/publication executions, **not independent reviewer verification**.

| Local source | Byte-identical publication | Lines | Dependency records | Exit |
|---|---|---:|---:|---:|
| `StarGeometry.lean` | `AHP/round13/shared/positivity/R2_StarGeometry.lean` | 2414 | 131 | 0 each |
| `P2.lean` | `AHP/round13/shared/positivity/R2_P2.lean` | 3523 | 140 | 0 each |

Every source has its own `.lean.log` and `.lean.exit`. Imports are only frozen `DrEquiv`; these are self-contained source certificates, not new importable modules.

`AUDIT.json` checks all four source/log hashes, source/publication identity, all printed dependencies, all 30 new public declarations (27 theorems and three definitions), seven copied source ranges, five additional direct round-12/round-13 source comparisons, and the **verbatim P2 statement** against `AHP/round12/shared/GAPS.md` (only whitespace ignored). It also checks the forbidden-token list and clean logs. Exact elaborated main/cofinal types are printed by `#check @...` in the final log.

## 1. Exact proved P2

Namespace `AdalyFormal.Round13.Positivity.Physical`, `P2.lean:3490`:

```lean
theorem rightStar_P2 :
    ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
      (t : ℝ), 0 < t → t < Real.pi/2 →
      ∀ x : TwistSpace q R, x ≠ 0 →
        AdalyFormal.Round12.Kernel.Actual.chargedCoordinate q R
          (rightSite hq R, (0 : Fin 3)) x = 0 →
        0 < ⟪x, vacA q R (rightStar hq R) 1 t x⟫
```

Literal axiom record:

```text
'AdalyFormal.Round13.Positivity.Physical.rightStar_P2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`rightStar`, `rightSite`, `vacA`, `TwistSpace`, and `chargedCoordinate` are the original definitions, copied verbatim, not replacement operators or observables. There is no unit, simplicity, spectral, finite-character, numeric, positive-remainder, or omitted-sum hypothesis in this theorem.

`rightStar_zero_coordinate_positive` at line 3448 is slightly stronger: its lower endpoint assumption is `0 ≤ t`. `cofinal_rightStar_P2` at line 3502 proves:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∀ (t : ℝ), 0 < t → t < Real.pi/2 →
    ∀ x : TwistSpace (2^j) R, x ≠ 0 →
      chargedCoordinate (2^j) R (rightSite (by positivity) R, (0 : Fin 3)) x = 0 →
      0 < ⟪x, vacA (2^j) R (rightStar (by positivity) R) 1 t x⟫
```

It chooses `j=j₀`, then `R=2*(R₀+18)`; every angle and every full carrier field are quantified after the same chosen radius. The stronger all-instance P2 lets assembly use any radius needed by P3, not merely this explicit cofinal choice.

## 2. What closed the physical gap

### Complete curved-plaquette geometry

- `star_edge_cases`, line 1957: a plaquette containing any of the four exterior star links is either one of the four actual `P1 rightSite ν` / `P2 rightSite ν` arms, or every vertex lies in two exterior normal layers.
- `right_forward_out` proves the second exterior layer does not wrap into the slab at any positive q.
- `exteriorPair_vertices`, line 1934: the second alternative makes both endpoints of every boundary bond exterior.
- `nonstar_nonneg`, line 2083: **every non-arm plaquette contributes nonnegatively** on the actual touching-bond space. If it contains no star link, all four links are identity, giving flat holonomy. Otherwise it is entirely exterior, the supported physical input vanishes on every edge, and its complete frozen energy is zero even if its holonomy is curved.

This avoids the false shortcut that every non-star plaquette is globally flat. No infinite-lattice embedding or numerical stencil is substituted for the periodic lattice.

### Actual full-color arm bounds

- `arm1_lower`, line 2215, proves the bound with actual atom order `(-normal-neighbor, -tangent, central, 0)`.
- `arm2_lower`, line 2240, proves it with order `(-central, -back-tangent, back-normal, 0)`.
- The frozen full-color formulas are reused verbatim. Vanishing of the charged central matrix entry does **not** zero its neutral component. The neutral square remains, with nonnegative coefficient `cos t`.
- `arm_injective` proves the four actual plaquettes distinct; `arm1_omitted` and `arm2_omitted` prove all four lie outside the localized selector.
- `armBudget_sum` identifies the four pair budgets with exactly the eight R1 physical leaf norms, without repetitions or a cardinality loss.

### Complete omitted sum and strict positivity

`rightStar_omitted_loss`, line 2348, and its raw-field version `rightStar_raw_omitted_loss`, line 2395, discharge the exact formerly missing physical inequality:

\[
 E_{\mathrm{omitted}}(x)\ge
 -(1-\cos t)\sum_{i=0}^{7}\|(i_E x)(\mathrm{leaf}_i)\|^2.
\]

The raw version has exactly the complete sum over all plaquettes outside `plaqIn Omega0`; the only angle premise is `0 ≤ cos t`. Round-12 `Wop_eq_on_omitted` and R1 `omittedEnergy_eq_raw` connect it to the dressed operator without an inverse-unit premise.

The genuine distinct level-zero rows from R1 pay this loss. R1's exact carrier split and nonnegative localized delta/gauge terms give, **unconditionally** on the charged-coordinate-zero subspace:

\[
 \langle x,A_t x\rangle\ge \cos t\,\langle x,B_t x\rangle.
\]

This is `rightStar_carrier_lower`, line 3427. Here `A_t` is the original `vacA` at mass one, identified by `vacA_rightStar`, and `B_t` is the actual localized carrier. R1's `rightStar_local_data_flat` and `rightStar_local_positive` are copied and recompiled, so \(B_t=B_0\) is strictly positive on every nonzero full carrier vector. Since \(\cos t>0\) below half pi, P2 follows.

`rightStar_prefix_lower`, line 3460, additionally proves for every `0 ≤ t ≤ T < pi/2`:

\[
 0<\cos T,\qquad
 \cos T\,\langle x,B_0x\rangle\le\langle x,A_tx\rangle.
\]

The **relative** lower factor is independent of q and R and valid on the entire closed prefix. This is all that strict P2 needs. We do not invent a uniform ordinary-norm spectral gap from `MINE.md`, whose weighted/localized constant has a different scope. Nor do we claim the bare zero-central star perturbation is nonnegative: R1 already proved that shortcut false. At half pi this particular lower factor is zero, so this estimate alone does not establish strict endpoint positivity.

## 3. Reuse and integration

The reusable publication `R2_P2.lean` contains all dependencies needed for the exact P2 and the cofinal theorem. `R2_StarGeometry.lean` contains the full omitted-sum proof without the larger localized flat-kernel join. Original interfaces and the full-color/mass/collar packages are copied verbatim; `COPIES.json` and `AUDIT.json` give their ranges/hashes.

Assembly may now specialize its P2 premise with:

```lean
AdalyFormal.Round13.Positivity.Physical.rightStar_P2
```

P1 was already accepted in trial R1; this track does not re-claim it. Combining the proved P2 with the existing P1/continuity/start/gauge inputs should discharge the `hp` premise of `CrossingActual.kernelLine_exists_before_halfpi`. **This track does not claim to have compiled that additional specialization or a KernelLine theorem.** Assembly owns that downstream join. The earlier shared gap ledger may still say P2 is open until its owner incorporates this publication; that old wording is superseded by this compiled theorem, not by a numerical claim.

## 4. Exact remaining mathematical input

There is **no remaining P2 obligation**. P3 is separate and not proved here. With the original package openings it is, verbatim:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u
```

A sufficient cofinal remainder, retaining the same actual family/crossing, is:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ u : TwistSpace (2^j) R,
    KernelLine (2^j) R (rightStar (by positivity) R) u ∧
    CurlDetected (2^j) R u
```

P2 by itself does not prove crossing-generator detection, response noncancellation, or pinned `GoalNeg2`. No assertion about those missing propositions is inserted as a hypothesis disguised as a proof.

## 5. Focused reproduction

```sh
python3 AHP/round13/positivity/r2/build.py --publish
bb heavy run -- AHP/round3/lean1.sh AHP/round13/positivity/r2/P2.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round13/positivity/r2/StarGeometry.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round13/shared/positivity/R2_P2.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round13/shared/positivity/R2_StarGeometry.lean
python3 AHP/round13/positivity/r2/audit.py
```

No new numerical experiment, `lake build`, `REPRODUCE.sh`, giant historical join, git commit/push, deletion, or edit of an earlier round was performed. All authored project files are under `AHP/round13/positivity/r2/` or `AHP/round13/shared/positivity/`. The build script copies prior compiled material rather than redoing its mathematical proofs.
