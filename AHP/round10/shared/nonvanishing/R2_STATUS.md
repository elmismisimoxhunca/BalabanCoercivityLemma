# R2 compiled hand-off: let the interior defect site vary

**GoalNeg2 remains OPEN. No actual cofinal coupling premise is proved.**

Published and independently compiled: `R2_SourceFamily.lean` (+ `.log`, `.exit=0`). Namespace `AdalyFormal.Round10.Nonvanishing.FreeProfile`. Sole import frozen `D1IVT`. 47 declarations, individually audited, standard axioms only.

## Improvement over R1

R1 fixed the first source site and required v0 != 0 and every |vj| <= |v0|. R2 proves the source-response matrix is positive definite. Therefore **any nonzero finite vector of direction-1 block jets couples to some single even-site defect**. There is no domination, relative sign, asymptotic, or recurrence-in-R hypothesis. This uses the allowed free-profile premise, not the canonical fixed-profile premise.

For N blocks and source site i<N, solve the exact finite system with a[-1]=a[N]=0:

    6*a[j]+a[j-1]+a[j+1] = (3/2)*delta[j,i] + (1/2)*delta[j+1,i].

Existence for every N and RHS is proved (`exists_tri_solution`), by strict diagonal dominance and finite-dimensional injective => surjective. Put

    h_i[j] = delta[j,i] - delta[j+1,i] - 2*a[j-1] + 2*a[j+1]
    sourceResponse N i b = sum_j h_i[j]*b[j].

At i=0 this is EXACTLY R1's source equations/weights. `sourceResponse_pos` proves

    0 < sum_i b[i] * sourceResponse N i b

for every nonzero b on [0,N), zero-padded at N. `exists_sourceResponse_ne_zero` gives some i<N with a nonzero pairing. `exists_actual_coupling_of_source_dictionary` exposes the actual operator identification as an explicit hypothesis.

Proof: constrained Dirichlet lift y[2j+1]=b[j]+a[j], y[2j+2]=b[j]-a[j], y[0]=y[2N+1]=0. Its stationary equation is A*a=b_prev-b_next. The two fine Laplacians in each block coincide. Their common value equals sourceResponse by exact tridiagonal reciprocity; twice its pairing with b is the sum of all edge-difference squares. This is strictly positive unless all averages b vanish.

## Dictionary request

Physical defect i: direction 1 link at (p+2i,0,0), p=q*(2R+4), repeated at even transverse coordinates. N=4q*(R+1). Jet b[j] is the direction-1 normalized level-1 C2 at fine-base (p+2j,0,0) (coarse x=p/2+j). **Normalization distinction:** if b[j] is the physical C2full coordinate of the physically normalized lifted vector, the predicted overall coupling factor is 2*(4*q)^2, because there are (4*q)^2 translated coarse cells. If b[j] is the cell jet used by R6 `rawjet` on the cell-normalized vector, the lift's quadratic 1/(4*q)^2 cancels that count and the predicted factor is 2. The level-1 1/2 factor is already included in both b definitions. Neither dictionary is yet formalized. Source map is the same for either exterior twist; prefer left-only crossing.

The generalized source formula has been checked against the FULL neutral KKT solve from the R6 transcription at zero curvature (Jprime=Delta_flat*f, NOT a finite-curvature extrapolation): (q,R)=(1,2),(2,2),(2,18),(4,18); i=0,1,N/2,N-1 (16 tests, including N=152,304). At 80 digits, maximum discrepancy and maximum other-direction source component are 7.49e-74. Peak RSS 607 MiB. These are numerical evidence, not a dictionary proof, crossing computation, or cofinal witness. Artifacts: `AHP/round10/nonvanishing/r2/source_family_check.json` and `check_source_family.py`.

## Exact gaps

1. Prove the actual first-order source-pairing dictionary for these translated defect profiles, with physical normalization (factor 2 in the existing transcription).
2. Prove that the crossing mode's direction-1 jet vector is not identically zero. **R2 does NOT prove this.** It only removes the much stronger all-jets-domination requirement.
3. Full-kernel charged-line containment / spectral exclusion, and nested cofinal scales/radii.
4. Assemble into the free-profile/free-path round-9 bridge. No such assembly is claimed here.
