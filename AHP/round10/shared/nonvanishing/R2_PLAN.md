# Nonvanishing r2 — design note (superseded by the compiled hand-off)

See `R2_STATUS.md` and `R2_SourceFamily.lean` for the final 47-declaration compiled result. The finite source-controllability argument below is now proved in that scalar model. The actual operator dictionary and crossing-jet nonvanishing are not proved; GoalNeg2 remains open.

Source index requested by dictionary: p=q*(2R+4), N=4*q*(R+1), direction 1 at fine base (p+2*j,0,0), or coarse site (p/2+j,0,0). `probe.b1[3*j+2]` includes an incoming longitudinal coarse bond at index 0. Jet is actual normalized level-1 C2 (factor 1/2 already included). Prefer left-only crossing; source independent of exterior twist.

Potential improvement over r1: allow an arbitrary profile on the even longitudinal defect sites instead of insisting on the first site. In the neutral, transverse-uniform tangential channel, write the constrained lift of coarse data b as y_even(j)=b_j+a_j, y_odd(j)=b_j-a_j, zero outside the core. Minimizing curl energy gives

    6*a_j+a_(j-1)+a_(j+1)=b_(j-1)-b_(j+1).

Then the fine Laplacian has equal even/odd entries

    h_j=b_j-b_(j-1)+3*a_j+a_(j-1).

The exact energy identity is

    2*sum_j b_j*h_j = sum_edges (y_(x+1)-y_x)^2 > 0  (b != 0).

Consequently the source response matrix is positive definite: SOME even-site profile couples to every nonzero vector of direction-1 jets, without any first-jet dominance, signed-tail estimate, or leading constant. For first-site profile the adjoint recurrence reproduces r1's h_j=delta_j0-2*alpha_(j-1)+2*alpha_(j+1), A alpha=(3/2)e0.

I am formalizing the finite Dirichlet chain/source-response argument in short files. Actual frozen H/source identification remains a dictionary obligation; no exact crossing jet nonvanishing is inferred. More generally choosing neutral f=H0*C2(Wu) gives coupling 2||curl H0*C2(Wu)||^2 if J'[f]=curl*curl f. A nonzero transverse coarse circulation rules out zero curl.
