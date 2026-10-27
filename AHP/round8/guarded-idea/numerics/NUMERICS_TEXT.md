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

SEPARATION_TABLE

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

VACUUM_TABLE

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
