# Round 8, guarded reading: sign-free separation

**Status: counterexample mechanism. No pinned goal is closed.** `GoalPos1`, `GoalPos2`, `GoalNeg1`
and `GoalNeg2` (pin `AHP/round3/guarded/pin/Statement.lean:154-158`) remain open.

**The idea in one sentence.** The guard asks only that the all-plaquette carrier \(A\) be
*invertible*, not that it be positive definite. The exterior field is free in the class,
so the twist angle can run past \(A\)'s first crossing. Then a nonzero correction on the
crossing kernel, of **either** sign, produces an angle where \(A\) is a unit and \(A-D\)
is singular:
- positive sign: just before the crossing, where \(A\) is positive definite (the round-5 mechanism);
- negative sign: just after the crossing, where \(A\) is an **indefinite** unit (new).

The round-6 finding that the sign turns negative at very small curvature is therefore not
evidence for the positive reading. Numerically it moves the separation to the far side of
the crossing. At the decisive instance of the probe (\(q=2\), \(R=18\), \(\varepsilon=10^{-100}\)) I
computed the corrected boundary Schur matrix exactly and found:
- the corrected carrier \(A-D\) is singular at \(t_C=t_B+5.797\times10^{-171}\);
- the carrier \(A\) is invertible there, with boundary spectrum
  \([-1.874\times10^{-170},\ 2.115\times10^{-161},\ 0.998,\dots]\), and positive in every other sector;
- independent 400- and 500-digit runs agree on this shift to 227 relative digits.

The same happens:
- at \(\varepsilon=10^{-40}\) and \(10^{-60}\);
- at \(R=20\) (\(q=2\), \(\varepsilon=10^{-100}\), localised-mode regime);
- at \(R=24\) and \(30\) (\(q=2\), \(\varepsilon=10^{-140}\) and \(10^{-170}\), inside the small-curvature
  window);
- at the larger scale \(q=4\) (\(m=3\), \(M=8\)), \(R=18\), \(\varepsilon=10^{-170}\), where
  all 512 sectors were screened.

The positive-sign cases (\(q=2\), \(\varepsilon=10^{-6}\); \(q=1\), \(\varepsilon=10^{-40}\)) separate
before the crossing.

The vacuum coefficient \(c_1(q,R)\) controls the limit \(\varepsilon\to0\) at fixed \((q,R)\). It
is nonzero at every computed \((q,R)\): for \(q=2\) it equals \(K\rho_k^{8R}\) with one constant
\(K=-0.01916\) to 15 digits over \(R=18\) to \(30\), and for \(q=4\) the same normalisation gives
\(-0.01796\).

What is proved in Lean (compiled, standard axioms only) is a **conditional** reduction.
On the actual curved twist family, the open question becomes one proposition,
`CofinalTwistSeparation`:
- it implies `GoalNeg2` (`goalNeg2_of_cofinalTwistSeparation`);
- `GoalPos1` implies its negation (`not_cofinalTwistSeparation_of_goalPos1`).

The sign-free interval form `CofinalSignChange` suffices. It is implied by round 5's
`InitialKernelControl` and is also met in the negative-sign regime. A certificate layer
reduces its interval guard to two pointwise subspace certificates plus the exterior
sine/cosine pencil identity.

The premise itself is unproved: it is a statement about exact spectra of the actual
operators for all scales and radii.

---

## 1. Why the statement should be false: the structure

Notation as in the pin: \(A=G^{-1}_{\rm all}\), \(B=G^{-1}_{\rm in}\), \(D=\Delta^{(2)}_{\rm in}\),
\(C=B-D\), \(\Theta=A-B\).

**1.1 Interior data fixed, exterior free.** In the curved dilated family (round 4
`dilU`, round 5 `twistU`), \(B\) and \(D\), hence \(C\), do not depend on the exterior
field. This is compiled: `twist_data_constant`, `twistD_constant`, and round 5's
`dil_local_data_exterior_independent`. Class membership holds for **every** exterior
field once the interior amplitudes are fixed (compiled: `uniform_curved_family`), and the
cap \(a_0\) is chosen before the instance. Along the exterior twist \(U_t\):
\[
A(t)=B+\Theta(t),\qquad A(t)-D=C+\Theta(t).
\]
\(\Theta\) lives on the boundary coordinates of the omitted plaquettes:
\(\Theta=E_b\Theta_b E_b^*\). On omitted-plaquette edges the gradient part of \(W\)
vanishes, so this is an identity of the round-6 transcription (SOURCES.md), checked
there against dense assembly. Its exact Lean counterpart is the exterior path identity
`exterior_carrier_path` (prefix, round 5). With \(B,C\) positive definite,
the Schur complement and a congruence give, in every transverse sector,
\[
(n_-,n_0)(A(t))=(n_-,n_0)(S_B+\Theta_b(t)),\qquad
(n_-,n_0)(A(t)-D)=(n_-,n_0)(S_C+\Theta_b(t)),\qquad
S_X=(E_b^*X^{-1}E_b)^{-1},
\]
where \(n_-\) and \(n_0\) count negative and zero eigenvalues. Write \(X+E_b\Theta_bE_b^*\) as
\(X^{1/2}(I+K\Theta_bK^*)X^{1/2}\) with \(K=X^{-1/2}E_b\). The nonzero spectrum of
\(K\Theta_bK^*\) is that of \(M^{1/2}\Theta_bM^{1/2}\), where \(M=E_b^*X^{-1}E_b\), and
\(I+M^{1/2}\Theta_bM^{1/2}=M^{1/2}(S_X+\Theta_b)M^{1/2}\).
So the two problems differ by a **fixed** symmetric boundary matrix \(\delta N=S_C-S_B\).
It is the boundary return:
\(\delta N=-S_B\,E_b^*(C^{-1}-B^{-1})E_b\,S_B+O(\delta N^2)\).

**1.2 Both pencils are monotone.** The exterior identity
\(\Theta(t)=\cos t\,\Theta(0)+\sin t\,\Theta(\pi/2)\) holds, with \(\Theta(0)\succeq0\). It is
numerically exact (round 6 `path_identity.py`; my runs reproduce it with error below
\(10^{-400}\)). With \(X\in\{B,C\}\) positive definite,
\[
\frac{X+\Theta(t)}{\sin t}=X\csc t+\Theta(0)\cot t+\Theta(\pi/2)
\]
is Loewner-decreasing on \((0,\pi/2]\). Hence every eigenvalue of \(A(t)\), and of
\(A(t)-D\), crosses zero at most once there. The crossing angles are ordered,
\(t_{B1}\le t_{B2}\le\dots\) and \(t_{C1}\le t_{C2}\le\dots\), and \(A(t)\) is a unit exactly
off \(\{t_{Bi}\}\), with \(n_-(A(t))=\#\{i:t_{Bi}<t\}\). In particular, on
\((t_{B1},t_{B2})\) the carrier is an **indefinite unit**, and those angles are in the class.
The class does not force \(A\) to be PD where it is a unit.
(Lean: `pencil_rescaled_antitone`, `pencil_units_of_certificates`.)

**1.3 What the positive reading demands.** Along this path the positive reading says
\(\{t_{Ci}\}\subseteq\{t_{Bi}\}\), an *exact* coincidence of crossing angles. To first
order the first corrected crossing is displaced by
\[
t_{C1}-t_{B1}\approx \frac{d_{\rm eff}}{|\sigma'|},\qquad
d_{\rm eff}=\langle v,Dv\rangle+\langle Dv,C^{-1}Dv\rangle+\dots,
\]
where \(v\) is the unit carrier kernel at \(t_{B1}\). The exact value comes from \(S_C\).
- If \(d_{\rm eff}>0\), then \(t_{C1}<t_{B1}\) and \(A(t_{C1})\) is PD: separation (round 5).
- If \(d_{\rm eff}<0\), then \(t_{C1}>t_{B1}\). As long as the shift is smaller than the gap
  to the next carrier crossing, \(A(t_{C1})\) is an indefinite unit: separation again.

Only an exact coincidence escapes, and that requires the boundary return to vanish on the
crossing kernels. The guard is a unit condition, so the sign of \(D\) on the near-null
space is irrelevant. (Lean: `separation_of_sign_change`; necessity in this family:
`goalPos1_forces_no_twist_separation`.)

**1.4 The cap cannot help.** At fixed \((q,R)\) a smaller cap forces \(\varepsilon\to0\).
Then \(d_{\rm eff}(\varepsilon)=c_1(q,R)\,\varepsilon+O(\varepsilon^2)\). For \(q=1\),
\(c_1\) is positive but tiny (\(2.06\times10^{-246}\) at \(R=18\)), so at every computed
amplitude the positive quadratic term dominates. Meanwhile the
left/right partner splitting tends to its positive vacuum value. So if the vacuum
coefficient is nonzero, the separation persists below **every** cap. The exterior angle
\(t_C(\varepsilon)\) is part of \(U\), which the pinned order chooses after the cap. This
is ordinary analytic perturbation theory of a simple crossing. It is *not* formalised
here (section 5).

**1.5 Heuristic remark, beyond one path.** The class leaves *every* exterior field free.
So the positive reading at fixed interior data says
\(Z_C\cap\mathcal T\subseteq Z_B\), where \(Z_X=\{\Theta:\det(S_X+\Theta)=0\}\) and
\(\mathcal T\) is the set of omitted-plaquette Hessians that exterior fields reach. Since
\(Z_B=Z_C+\delta N\) is a translate, near a smooth point the inclusion forces \(\delta N\)
to be tangent to \(Z_C\), i.e. \(\langle y,\delta N\,y\rangle=0\) for every reachable
crossing kernel \(y\).

Up to genericity, then, the positive reading **is** the zero-return condition on reachable
crossing kernels. That condition is the converse of the compiled sufficient condition
`pencil_isUnit_of_no_boundary_return` (round 2, `r2-prove/Attempt.lean:475`). This is an argument, not a theorem: \(\mathcal T\) is a structured,
block-sparse set and its tangent directions were not computed. The one-parameter version
along the twist is what the Lean bridge and the numerics use.

## 2. Why this survives the known obstructions

- **(2) No uniform gap.** The negative direction needs no gap. It uses exactly that the
  cap cannot depend on the exterior field.
- **(3) Near-null modes visible to J.** This is what drives the separation: the
  correction sees the crossing mode, with a nonzero pairing.
- **(4) Exterior independence, flat-near-top and strip zeros.** All consistent. The
  family keeps the curvature at the edge of \(\Omega_1\), so \(D\neq0\) (the round-6
  boundary-strip family has \(D=0\) and cannot separate). Exterior tuning only moves along
  the twist; it does not change \(B\) or \(D\).
- **(5) Negative sign at small \(\varepsilon\).** That is the post-crossing regime, and it
  separates. At \(\varepsilon=10^{-100}\) the probe's "alternative" (a negative corrected
  form *before* the crossing) correctly failed. The separation is on the other side.

## 3. The suggested positive ideas, tested against this mechanism

- **(a) Sign/monotonicity.** \(A-D\succeq A\) on the near-null modes keeps the first
  singularity in \(A\), but then \(A-D\) becomes singular at
  \(t_{C1}\in(t_{B1},t_{B2})\), where \(A\) is an indefinite unit. The class does not force
  \(A\) PD wherever it is a unit (1.2). Measured sign of \(D\) on \(A\)'s first crossing
  kernel: positive on the round-6 grid; negative at \(\varepsilon=10^{-40},10^{-60},10^{-100}\)
  (\(q=2,R=18\)). Both signs separate.
- **(b) Schur decomposition with a definite correction.** In the boundary Schur form
  above, the correction is the fixed matrix \(\delta N\). A definite sign of \(\delta N\) on
  the crossing kernel decides only on which side of \(t_{B1}\) the corrected crossing lies.
- **(c) Homotopy / spectral flow.** From \(t=0\) (both PD) to \(t=\pi/2\) the two pencils
  have the same spectral flow, but their crossing *angles* differ by \(O(d_{\rm eff})\).
  Equal flow does not give simultaneous singularity, and separation sits between the
  angles.
- **(d) Analytic perturbation in \(\alpha_0\), cap last.** At fixed \((m,R)\) this gives
  \(t_{C1}-t_{B1}=c_1\varepsilon/|\sigma'|+O(\varepsilon^2)\neq0\): it supports the
  *negative* reading (1.4).
- **(e) Quantifier order.** The cap precedes \(k\), \(L_u\), \(\alpha_0\), \(S\), \(\Lambda\),
  \(U\). The exterior field is part of \(U\), so no cap can exclude \(t_C(\varepsilon)\).
  A cap depending on the instance's own gap is not allowed by the pin.

## 4. What is proved (Lean)

`Attempt.lean` is the complete round-5 `AHP/round5/guarded/ivt-r2/Attempt.lean` (which
begins with the complete round-3 pin) followed byte-for-byte by `Appendix.lean`. Both
prefixes are verified by `audit.py`. Sole import: frozen `DrEquiv`. Namespace
`AdalyFormal.Round8.Guarded.SignFree`.

All 26 new declarations print exactly `[propext, Classical.choice, Quot.sound]`
(`Attempt.lean.log`). Line numbers refer to `Attempt.lean`.

| Line | Declaration | Content |
|---:|---|---|
| 2440 | `separation_of_sign_change` | Finite-dimensional, **sign-free**. Let \(A(t)\) be a continuous symmetric path and \(D\) symmetric. If \(A(t)\) is a unit on \([t_0,t_1]\), \(A(t_0)-D\) is PSD and \(\langle w,(A(t_1)-D)w\rangle<0\), then some \(t\in[t_0,t_1)\) has \(A(t)\) a unit and \(A(t)-D\) not a unit. \(A\) may be indefinite throughout. |
| 2474 | `sign_change_of_kernel_positive` | Round-5 positive-kernel data (guard on \([0,T)\), \(A(T)v=0\), \(\langle v,Dv\rangle>0\)) yield such an interval, so the new premise is weaker than the old one. |
| 2507 | `post_crossing_witness` | If \(A(t_0)-D\succeq0\) and \(\langle x,A(t_0)x\rangle<0\), then \(A(t_0)\) is not PSD and \(\langle x,Dx\rangle<0\). The post-crossing regime starts at an indefinite carrier and needs a negative correction direction. |
| 2531 | `unit_of_definite_complements` | Spectral-theory-free unit certificate: if \(X\) is symmetric, negative definite on \(U\), positive definite on \(V\), and \(\dim U+\dim V\ge\dim E\), then \(X\) is a unit. |
| 2576 | `units_of_scaled_certificates` | If \(A(t)/g(t)\) (\(g>0\)) is Loewner-nonincreasing on \([t_0,t_1]\), a negative-definite subspace at \(t_0\) and a positive-definite subspace at \(t_1\) of complementary dimension certify a unit at every \(t\in[t_0,t_1]\). |
| 2604 | `pencil_rescaled_antitone` | For \(A(t)=B+\cos t\,\Theta_0+\sin t\,\Theta_1\) with \(B,\Theta_0\) PSD, \(\langle x,A(t)x\rangle/\sin t\) is nonincreasing on \((0,\pi/2]\). \(\Theta_1\) is arbitrary. |
| 2631 | `pencil_units_of_certificates` | The two previous results combined: pencil form plus two endpoint certificates give the whole interval guard. |
| 2656 | `TwistSeparation q R ε` | Definition (premise, not a fact): some exterior angle \(t\) has `twistA` a unit and `twistA − twistD` not a unit (mass \(a=1\)). |
| 2663 | `SignChangeControl q R ε` | Definition (premise, not a fact): an interval of `twistA` units on which the corrected form goes from PSD to a negative direction. No sign of the kernel correction and no positivity of the carrier are required. |
| 2670 | `twistSeparation_of_signChange` | `SignChangeControl → TwistSeparation` on the actual operators (uses `twistA_continuous`, the frozen symmetry lemmas, `twistD_constant`). |
| 2686, 2694 | `signChange_of_kernelPositiveCrossing`, `signChange_of_initialKernelControl` | Round 5's `KernelPositiveCrossing` and `InitialKernelControl` imply `SignChangeControl`. |
| 2704 | `goalNeg2_of_twist_separation` | **Cofinal bridge:** if for every \(q>0\), every even \(R\ge18\) and every \(\delta>0\) some \(0<\varepsilon<\delta\) has `TwistSeparation q R ε`, then `GoalNeg2`. Witnesses: \(\ell=2\), \(a=1\), \(m=m_0+1\), \(q=2^{m_0}\), \(R=2(R_0+18)\), chosen **before** the cap; then \(\varepsilon<\min(a_0/(3840q),1)\), \(\alpha=160\varepsilon\). Full frozen class, torus, admissibility, `LambdaOK2` and positive-energy competitor obligations are discharged by the copied round-4/5 theorems. |
| 2741 | `goalNeg1_of_twist_separation` | The same premise gives `GoalNeg1`. |
| 2750 | `goalNeg2_of_sign_change_control` | **Main sign-free bridge:** the cofinal `SignChangeControl` premise implies `GoalNeg2`. |
| 2763 | `goalPos1_forces_no_twist_separation` | What the positive reading demands: `GoalPos1` implies that for all large \(m\), then all large even \(R\ge18\), there is \(\delta>0\) such that no \(0<\varepsilon<\delta\) has `TwistSeparation (2^(m-1)) R ε`. Every corrected crossing along the twist must then be a carrier crossing. |
| 2803 | `TwistPencil q R ε` | Definition (premise): `twistA t = B + cos t • Θ₀ + sin t • Θ₁` for fixed operators, with \(B,\Theta_0\) PSD. |
| 2811 | `PencilCertificates q R ε` | Definition (premise): `TwistPencil`, plus subspace certificates at two angles in \((0,\pi/2]\), corrected form PSD at \(t_0\) and negative somewhere at \(t_1\). |
| 2823, 2832 | `signChange_of_pencilCertificates`, `goalNeg2_of_pencil_certificates` | `PencilCertificates → SignChangeControl`, and the cofinal version gives `GoalNeg2`. |
| 2846 | `CofinalTwistSeparation` | Definition (the **single remaining statement**, in its weakest form): \(\forall j_0\,\exists j\ge j_0\,\forall R_0\,\exists R\ge R_0\) with \(2\mid R\) and \(R\ge18\), \(\forall\delta>0\,\exists\,0<\varepsilon<\delta\) with `TwistSeparation (2^j) R ε`. These are exactly the cofinal quantifiers of the pin, with \(R\) before the cap. |
| 2851 | `CofinalSignChange` | The same with `SignChangeControl`. |
| 2856 | `goalNeg2_of_cofinalTwistSeparation` | **Main bridge:** `CofinalTwistSeparation → GoalNeg2`. |
| 2891 | `not_cofinalTwistSeparation_of_goalPos1` | `GoalPos1 → ¬ CofinalTwistSeparation`. On this family the open question is therefore exactly `CofinalTwistSeparation`: it refutes the pinned positive reading, and the positive reading refutes it. |
| 2894, 2905 | `cofinalTwistSeparation_of_cofinalSignChange`, `goalNeg2_of_cofinalSignChange` | The sign-free interval form suffices. |


None of these closes a pinned goal. The bridges have explicit, unproved cofinal premises.

## 5. What remains: one clean statement

**Missing fact (unproved): `CofinalTwistSeparation` (`Attempt.lean:2846`).** For
infinitely many dyadic scales \(q=2^j\), and for each of them infinitely many even
radii \(R\ge18\), every \(\delta>0\) admits a curvature \(0<\varepsilon<\delta\) and an
exterior angle at which the actual carrier `twistA` is a unit and `twistA − twistD` is
not.

`goalNeg2_of_cofinalTwistSeparation` turns it into `GoalNeg2`, and
`not_cofinalTwistSeparation_of_goalPos1` shows the positive reading forbids it. Sufficient
forms:
- `CofinalSignChange`: interval data, sign-free;
- `PencilCertificates`: the pencil identity `TwistPencil` plus two subspace certificates,
  finitely checkable at each \((q,R,\varepsilon)\).

The natural proof route has two steps, neither formalised:
1. Vacuum nondegeneracy at \(\varepsilon=0\), for every \((q,R)\) in the family: a simple
   first crossing in its character, nonzero slope, positive partner splitting, and a
   nonzero first nonvanishing amplitude coefficient of the exact boundary shift.
2. An analytic perturbation theorem turning these into `SignChangeControl` for all small
   \(\varepsilon\).

Step 1 is supported numerically for the computed \((q,R)\) (section 6) but is a
parametric statement over infinitely many lattices. The data suggest the precise form
\(c_1(q,R)\approx K(k_q)\,\rho_{k_q}^{4qR}\), with \(K\) constant in \(R\) to 15 digits at
\(q=2\), and \(K(k_q)\approx-0.018\) to \(-0.019\) at \(q=2,4\). Step 1 would then reduce to
a half-space nonvanishing \(K(k)\neq0\) near the continuum first momentum, plus uniform
finite-size bounds. Proving it needs exact control of
exponentially small boundary-to-\(\Omega_1\) propagation; no closed form for the
finite-volume kernel is available. A positive proof would instead have to show
that the boundary return vanishes exactly on every crossing kernel. The numbers below say
it does not.

## 6. Numerical evidence

All operators are the round-6 transcription of the actual pinned assemblies (operator
dictionary with Lean line citations: `AHP/round6/probe/SOURCES.md`): exact raw Taylor
jets, the full localized augmented inverse and the full neutral KKT solve for
\(H^*J\). The new ingredient is the **exact corrected boundary Schur matrix**
\(S_C=(E_b^*C^{-1}E_b)^{-1}\). It is computed by solving the corrected augmented system
(round-6 `positivity.corrected_aug`, i.e. \(\Delta\to\Delta-M\) with
\(D=W^*MW\)) on every boundary column. No first-order perturbation formula is used
for the separation itself. The family: \(\ell=2\), \(k=1\), mass \(a=1\), fine sides
\((q(12R+16),8q,8q)\), defect at the left edge of \(\Omega_1\), exterior twist
\(U_\theta\). This is exactly `twistA`/`twistD` of the Lean file.

### 6.1 Separating angles

Each row is one transverse character: the first carrier crossing of the family. For
\(q\le2\) this comes from the round-6 screens and my screen in 6.3; for \(q=4\), from my
512-sector screen in 6.4.
- \(t_{B1}\), \(t_{B2}\): first two roots of the carrier boundary Schur matrix \(S_B+\Theta_b(t)\).
- \(t_{C1}\): first root of \(S_C+\Theta_b(t)\).
- "A at \(t_{C1}\)": the two lowest eigenvalues of \(S_B+\Theta_b(t_{C1})\). Since \(B\) is PD,
  these carry the carrier's inertia.
- "A−D at \(t_{C1}\)": the lowest eigenvalue of \(S_C+\Theta_b(t_{C1})\), which is zero to
  working precision.
- The corrected-kernel residual is that of the reconstructed carrier vector in the full
  corrected augmented system.
- "exact/first-order" is \(\langle y,(S_C-S_B)y\rangle/(-\|v\|^2\langle v,Dv\rangle)\).

| q | R | eps | dps | char | <v,Dv> (unit v) | t_C1 - t_B1 | t_B2 - t_B1 | side | A at t_C1 (two lowest) | A-D at t_C1 | corr. kernel residual | exact/first-order | separation |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | 18 | 1e-40 | 200 | (0,0) | 7.59e-113 | -4.401e-113 | 1.742e-64 | before (A PD) | 1.011e-112, 4.002e-64 | -1.6e-200 | 1.6e-196 | 1.26952 | yes |
| 2 | 18 | 1e-100 | 400 | (7,7) | -1.812e-170 | 5.797e-171 | 6.542e-162 | after (A indefinite unit) | -1.874e-170, 2.115e-161 | -2.2e-400 | 1.5e-394 | 1.0 | yes |
| 2 | 18 | 1e-100 | 500 | (7,7) | -1.812e-170 | 5.797e-171 | 6.542e-162 | after (A indefinite unit) | -1.874e-170, 2.115e-161 | -2.5e-500 | 4.5e-500 | 1.0 | yes |
| 2 | 18 | 1e-40 | 400 | (7,7) | -1.754e-215 | 5.206e-216 | 1.487e-109 | after (A indefinite unit) | -1.683e-215, 4.807e-109 | 1.3e-401 | 1.3e-394 | 1.0 | yes |
| 2 | 18 | 1e-60 | 400 | (7,7) | -1.754e-195 | 5.206e-196 | 1.487e-129 | after (A indefinite unit) | -1.683e-195, 4.807e-129 | 3.9e-400 | 1.4e-394 | 1.0 | yes |
| 2 | 18 | 1e-6 | 300 | (7,7) | 2.762e-191 | -8.833e-192 | 1.487e-75 | before (A PD) | 2.856e-191, 4.807e-75 | 4.3e-301 | 6.9e-301 | 1.0 | yes |
| 2 | 20 | 1e-100 | 450 | (7,7) | -1.44e-182 | 4.272e-183 | 4.111e-177 | after (A indefinite unit) | -1.381e-182, 1.329e-176 | -2.3e-450 | 2.2e-450 | 1.0 | yes |
| 2 | 24 | 1e-140 | 450 | (7,7) | -3.833e-233 | 1.226e-233 | 7.073e-214 | after (A indefinite unit) | -3.964e-233, 2.287e-213 | 4.0e-451 | 3.4e-450 | 1.0 | yes |
| 2 | 30 | 1e-170 | 460 | (7,7) | -8.106e-286 | 2.593e-286 | 7.648e-266 | after (A indefinite unit) | -8.382e-286, 2.473e-265 | 7.4e-460 | 6.2e-455 | 1.0 | yes |
| 4 | 18 | 1e-170 | 480 | (15,15) | -4.72e-297 | 1.796e-297 | 3.443e-276 | after (A indefinite unit) | -4.908e-297, 9.411e-276 | 2.7e-480 | 2.0e-480 | 1.0 | yes |

In every row \(A\) is a unit at \(t_{C1}\) and \(A-D\) is singular there:
- In the "before" rows the carrier is positive definite at \(t_{C1}\): the round-5
  mechanism, here confirmed with the exact \(S_C\).
- In the "after" rows the carrier has exactly one negative (complex, i.e. two real)
  eigenvalue at \(t_{C1}\). This is the post-crossing separation that the earlier rounds
  did not test. \(t_{C1}\) lies in \((t_{B1},t_{B2})\) by a factor between \(10^{6}\) and
  \(10^{106}\).

In the rows inside the small-curvature window of 6.4 (\(R=18\) at \(10^{-100}\), \(R=24,30\),
and \(q=4\)), the pairing equals \(c_1(q,R)\,\varepsilon\) to the printed digits.

The \(\varepsilon=10^{-100}\) row is the probe's decisive negative instance, where the
pre-crossing test fails (probe: corrected form \(+2.72\times10^{-170}\) at the pre-crossing
offset). It separates after the crossing.

The interval data of `SignChangeControl` are also in the JSON files (`interval`):
- at \(t_{B1}+\tfrac1{10}(t_{C1}-t_{B1})\): \(n_-(A)=1\) and \(n_-(A-D)=0\);
- at \(t_{B1}+2(t_{C1}-t_{B1})\): \(n_-(A)=1\) and \(n_-(A-D)=1\);
- the "before" rows are mirrored.

Through the Schur inertia identity of 1.1, \(n_-(A-D)=0\) in this character is \(A-D\)
PSD there. \(A\) stays a unit on the whole interval by monotonicity, since \(n_-(A)\) is
the same at both ends.

For \(q=1\) the exact shift is 1.2695 times the first-order prediction: this is the
quadratic-order term \(\langle Dv,C^{-1}Dv\rangle\ge0\). For \(q=2\) the two agree to 12
digits (linear regime).

### 6.2 Precision

The \(q=2\), \(R=18\), \(\varepsilon=10^{-100}\) instance was run independently at 400 and
500 digits (`out/agree_q2_R18_e1e-100_p400_p500.json`). Relative agreement:
- \(t_{C1}-t_{B1}\): 227.4 digits;
- \(t_{B2}-t_{B1}\): 243.2 digits;
- the unit-kernel pairing \(\langle v,Dv\rangle=-1.8124680628969907\times10^{-170}\): 235.6
  digits, matching the round-6 probe's own 400/500 agreement and value;
- the lowest carrier Schur eigenvalue at \(t_{C1}\): 227.4 digits.

Corrected-kernel augmented residuals are at most \(1.5\times10^{-394}\) (400 digits) and
\(4.5\times10^{-500}\) (500 digits). The exterior pencil identity error is below
\(5\times10^{-400}\) in every run.

### 6.3 The carrier is a unit on the whole carrier at the separating angle

The screen covers \(q=2\), \(R=18\), all 64 characters × {neutral, charged} = 128 sectors
(`numerics/screen.py`, `out/screen_q2_R18_vacuum.json`; modest-precision assembly,
double spectra). It was evaluated at \(t=0.5639715179855609\), which differs from \(t_{C1}\)
by \(6\times10^{-171}\). Curvature effects of size \(\varepsilon\le10^{-40}\) are invisible
at double precision.
- The localized augmented system has the required inertia in all 128 sectors (\(B\) PD).
- The only non-positive boundary Schur minimum is the (7,7) charged sector, at
  \(-1.8\times10^{-16}\), i.e. double-precision zero; it is resolved at 400–500 digits in 6.1.
- Every other sector is \(\ge0.05196\).

This agrees with the round-6 probe's own complete screen of the \(\varepsilon=10^{-100}\)
instance (120-digit assembly): 124 sectors positive at the later root 0.58656 and three
competitors \(\ge0.0519\) at \(t_{B1}\). So, numerically, \(A(t_{C1})\) is a unit on the
whole carrier and \(A(t_{C1})-D\) is not: a guarded separation at this instance.

### 6.4 Vacuum data: why the separation survives every cap at fixed \((q,R)\)

At \(\varepsilon=0\) the correction vanishes (round-6 `twistD_zero_amplitude`). For small
\(\varepsilon\) the corrected crossing is displaced by
\(\approx c_1\varepsilon/|\text{slope}|\), while the partner crossing stays a vacuum
splitting \(s_0>0\) away. `numerics/vacuum_coeff.py` computes, at \(\varepsilon=0\):
- the first root;
- \(s_0\), the second boundary Schur eigenvalue there;
- the kernel-form slope;
- the finite-sum coefficient \(c_1=2\sum_j h'_j\,C^{(2)}_j(W_0v_0)\). This is round-6
  `leading_vacuum.py` generalised; \(h'\) is checked there against the full KKT solve.

| q | R | dps | char | vacuum root t* | partner splitting s0 | kernel-form slope | c1 | left-half mass |
|---|---|---|---|---|---|---|---|---|
| 1 | 18 | 200 | (0,0) | 5.865589686386088e-1 | 4.002e-64 | -2.189 | 2.06e-246 | 5.0e-1 |
| 2 | 18 | 340 | (7,7) | 5.639715179855609e-1 | 2.115e-161 | -3.127 | -1.812e-70 | 5.0e-1 |
| 2 | 20 | 400 | (7,7) | 5.639715179855609e-1 | 1.008e-178 | -3.127 | -5.012e-78 | 5.0e-1 |
| 2 | 24 | 400 | (7,7) | 5.639715179855609e-1 | 2.287e-213 | -3.127 | -3.833e-93 | 5.0e-1 |
| 2 | 30 | 400 | (7,7) | 5.639715179855609e-1 | 2.473e-265 | -3.127 | -8.106e-116 | 5.0e-1 |
| 4 | 18 | 520 | (15,15) | 5.593474882146265e-1 | 9.411e-276 | -2.629 | -4.72e-127 | 5.0e-1 |

For \(q=2\) the coefficient is nonzero and negative at every radius computed. Hence, in
the window \(|c_1|\varepsilon\ll s_0\), i.e. \(\varepsilon\ll e^{-11.2R}\) (about \(10^{-91}\)
at \(R=18\)), the corrected crossing sits just after the carrier crossing and before its
partner: post-crossing separation below every cap. Above that window the modes localise
and the shift has a different law (the \(10^{-40}\), \(10^{-60}\) rows,
\(\propto1/\varepsilon\)), still separating.

The coefficient obeys an exact-looking law,
\[
c_1(2,R)=K\,\rho_k^{\,8R},\qquad K=-0.0191639341944987,\qquad
\rho_k=\tfrac12\bigl(3+T-\sqrt{(3+T)^2-4}\bigr),\ T=4(1-\cos k),\ k=-\pi/8,
\]
with \(K\) the same to all 15 printed digits at \(R=18,20,24,30\). The rate \(8|\log\rho_k|=8.7017523\)
is the round-6 collar decay squared over the boundary-to-\(\Omega_1\) distance \(4R\). The
splitting obeys \(s_0\propto e^{-19.942718R}\), constant to 8 digits.

The same normalisation at \(q=4\) (first character (15,15), \(k=-\pi/16\), distance
\(8R\)) gives \(c_1(4,18)/\rho_k^{16R}=-0.0179649513\). The half-space constant thus has
the same sign and size at the two nonzero momenta computed. For larger \(q\) the first
momentum moves toward the continuum minimiser \(k^*\approx-0.267\) (`halfspace.py`),
which lies between them. Only the symmetric \(k=0\) mode (\(q=1\)) has a suppressed
linear coefficient.

So the nondegeneracy needed in section 5 looks like the statement that a fixed
half-space constant \(K(k)\) is nonzero near \(k^*\), plus finite-size error control.
This is a conjecture supported by data at \(q=2,4\), not a computation for all \(q\).

The ratio of the shift to the partner gap is about \(\varepsilon/\varepsilon_x\), with
\(\varepsilon_x=s_0/|c_1|\); measured: \(10^{-107}\), \(10^{-67}\) and \(10^{-9}\) at
\(\varepsilon=10^{-40},10^{-60},10^{-100}\). Only a neighbourhood of
\(\varepsilon\approx\varepsilon_x\) needs a genuine two-mode analysis. The cofinal premise
needs arbitrarily small \(\varepsilon\), where the ratio vanishes linearly.

For \(q=1\) the coefficient is positive, \(c_1=2.06\times10^{-246}\). It is tiny but has
no cancellation: positive terms \(2.07\times10^{-246}\), negative \(-1.2\times10^{-248}\).
The positive quadratic term dominates at all computed amplitudes, so this is the
pre-crossing regime.

**Larger scale, \(q=4\) (\(m=3\), \(M=8\)), \(R=18\).** The closed half-space
boundary equation (`halfspace.py`; it reproduces the \(q=1,2\) finite-volume roots to all
printed digits) predicts the first crossing in the diagonal character (15,15)
(\(k=-\pi/16\)), at \(t_\infty=0.559347488214626\).

The full vacuum screen (`out/screen_q4_R18_vacuum.json`: \(16\times16\) characters ×
{neutral, charged} = 512 sectors, double spectra) confirms it:
- \(B\) has the required inertia in all 512 sectors;
- the boundary Schur minimum is \(\ge0.99999\) at \(t=0\) in every sector;
- at \(t=0.5594\), the only non-positive sector is (15,15) charged; the next lowest are
  (14,15) and (15,14) at \(0.01359\), then (14,14) at \(0.01478\).

The vacuum run gives:
- finite-volume root \(0.5593474882146264681\);
- partner splitting \(s_0=9.41\times10^{-276}\);
- \(c_1(4,18)=-4.72\times10^{-127}\), i.e. \(c_1/\rho_k^{16R}=-0.01796\).

So the post-crossing window is \(\varepsilon\ll\varepsilon_x=2.0\times10^{-149}\).
The direct separation check at \(q=4\), \(\varepsilon=10^{-170}\) (480 digits, row in the
table of 6.1) gives \(t_{C1}-t_{B1}=1.80\times10^{-297}\), with the partner at
\(3.44\times10^{-276}\). At \(t_{C1}\):
- \(A\) has boundary spectrum \([-4.91\times10^{-297},\ 9.41\times10^{-276},\ 1.044,\dots]\);
- \(A-D\) is singular to \(2.7\times10^{-480}\);
- the unit-kernel pairing is \(-4.71992\times10^{-297}=c_1(4,18)\,\varepsilon\), as predicted
  by the vacuum coefficient.

With the 512-sector screen (all other sectors \(\ge0.0136\) at the crossing angle), this
is a numerical guarded separation at \(m=3\), \(M=8\): again post-crossing, at an
indefinite carrier unit.

### 6.5 What these numbers do not show

- They are floating-point (mpmath) results. There are no directed-rounding intervals, no
  certified eigenvector enclosures, and no Lean operator/Fourier dictionary.
- Only \(q\in\{1,2,4\}\) (\(m\le3\)) is computed, at radii 18 to 30 (and \(R=18\) only
  for \(q=4\)). The eventual thresholds of the pinned statement are unknown. A separation at these
  scales refutes nothing by itself; the bridge needs `CofinalTwistSeparation`, with
  infinitely many scales and radii.
- The other-sector screens are double precision.
- The exterior pencil identity and \(\Theta=E_b\Theta_bE_b^*\) are transcription
  identities, checked numerically, not Lean theorems.
- The persistence argument of 6.4 is analytic perturbation theory, not formalised.

## 7. Files, commands and verification

All paths are relative to `AHP/round8/guarded-idea/`.

| File | Content |
|---|---|
| `Attempt.lean` | Deliverable: round-5 `ivt-r2/Attempt.lean` (hence the round-3 pin) verbatim, then `Appendix.lean` verbatim. |
| `Attempt.lean.log`, `Attempt.lean.exit` | Wrapper outputs of `AHP/round3/lean1.sh AHP/round8/guarded-idea/Attempt.lean`: exit **0**, no errors, no warnings, 182 dependency records. |
| `Draft.lean`, `Draft.lean.log`, `Draft.lean.exit` | Earlier compile of byte-identical source (`cmp` equal), exit 0. Its log equals the final log apart from a 3-line heavy-slot waiting notice at the top (`diff` of the rest is empty). Kept as a replay, not as the deliverable. |
| `Appendix.lean` | The new round-8 section alone (not compiled separately; it needs the prefix). |
| `audit.py`, `CHECKS.json`, `CHECKS.Draft.lean.json` | Artifact audit. |
| `numerics/sepcheck.py` | Exact boundary-Schur separation check (\(S\), \(S_C\) from the exact corrected augmented system, \(\Theta_b(t)\), roots \(t_{B1},t_{B2},t_{C1},t_{C2}\), spectra, interval data, first-order consistency, corrected-kernel residual). |
| `numerics/vacuum_coeff.py` | Vacuum first root, partner splitting, slope and the finite-sum coefficient \(c_1(q,R)\). |
| `numerics/screen.py` | All-sector double-precision screen (B inertia, boundary Schur minima at given angles). |
| `numerics/halfspace.py` | Closed half-space crossing angle for diagonal momenta (predicts the first character for larger \(q\)). |
| `numerics/summarise.py`, `tables.md`, `SUMMARY.json`, `NUMERICS_TEXT.md`, `fill_idea.py` | Section 6 of this file: prose source plus tables regenerated from `out/*.json` (no new numerics). |
| `numerics/batch1.sh`, `batch2.sh`, `batch3.sh` | Sequential job lists (one heavy slot at a time). |
| `numerics/agree.py`, `brief.py`, `show.py`, `time_q4.py`, `debug1.py` | Comparison, display, timing and the \(R=6\) first-order diagnostic. |
| `numerics/out/*.json`, `numerics/*.log`, `numerics/*.exit` | Raw outputs. |

**Lean verification.** Compiled only through the shared wrapper, launched detached and
polled for the `.exit` file:
```
AHP/round3/lean1.sh AHP/round8/guarded-idea/Attempt.lean
python3 AHP/round8/guarded-idea/audit.py            # writes CHECKS.json, exit 0
```
`audit.py` checks:
- the round-3 pin is a byte prefix, and so is the whole round-5 `ivt-r2/Attempt.lean`;
- `Attempt.lean` = that file + `Appendix.lean`;
- the sole import is `DrEquiv`;
- the raw source (comments included) contains no `sorry`, `admit`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `opaque` or `axiom` command;
- exit 0, with source ≤ log ≤ exit timestamps;
- no error lines, and no `sorryAx` in the log;
- every dependency record, line wraps re-joined, is a subset of `propext`, `Classical.choice`, `Quot.sound`;
- each of the 26 new declarations has its own record.

Compile history (seven wrapper invocations, in order):
1. The first `Attempt.lean`, started in the foreground, died before Lean started (empty
   log, no exit file, no surviving process). It was relaunched detached.
2. `Attempt.lean`, first appendix version: exit 0, 166 records, 6 cosmetic warnings
   (three deprecated `ContinuousLinearMap.sub_apply`, two unused automatically included
   section variables, one unused hypothesis).
3. `Draft.lean` with the certificate section: exit 1, a wrong hypothesis passed in
   `pencil_units_of_certificates` (`t ≤ t₁` where `t ≤ π/2` was needed).
4. `Draft.lean`, that fixed: exit 0, 176 records, no warnings.
5. `Attempt.lean`, byte-identical to (4): exit 0, log byte-identical to (4).
6. `Draft.lean` with the cofinal declarations: exit 0, 182 records, no warnings.
7. **Final** `Attempt.lean`, byte-identical to (6): exit 0, 182 records, no warnings. Its
   log equals (6) apart from (6)'s heavy-slot waiting notice.

No compile timed out or was relaunched while pending.

**Numerics.** Every job longer than a minute went through `"$BB_CLI" heavy run --`,
single-threaded BLAS, a 4 GiB address-space cap set by the scripts, and peak RSS below
1 GiB for \(q\le2\) (1.9 GiB for the \(q=4\) separation run). The round-6 probe modules are imported read-only, with bytecode
writing disabled; nothing was written outside this directory. Precision runs are
independent (400 and 500 digits).

These are **floating-point numerics**: no interval arithmetic, no certified eigenvector
enclosures, no Lean operator dictionary. They illustrate the mechanism; they do not
supply the cofinal premise.

**Hygiene.** Only files under `AHP/round8/guarded-idea/` were written; scratch files were
deleted only there. No protected source, lakefile, paper, notes, expected output, extras,
earlier round or the integration checkout was touched. No `lake build`, `REPRODUCE.sh`,
commit or push.
