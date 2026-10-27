
/-!
Round 9.2, qualitative route: the vacuum crossing is a theorem, the two twist directions are
gauge equivalent, and the remaining premise is soft regularity plus one coupling.

* Abstract: a symmetric operator is a unit iff its Gram determinant is nonzero; along a path
  whose matrix coefficients are real-analytic the Gram determinant is analytic, so non-units
  are isolated once the path is a unit somewhere (identity theorem).  A continuous path that is
  positive definite at `t₀`, has a negative direction at `t₁` and isolated non-units, crosses
  at the end of its initial positive semidefinite interval: positive definite arbitrarily close
  before, a negative direction arbitrarily close after.
* Lattice: the frozen continuity chain for the plaquette Hessian (`D1Cont`), repeated with
  `Continuous` replaced by entrywise real-analyticity, and over a general parameter space.
* Concrete: the vacuum carrier of the actual exterior twist is positive definite at angle `0`
  for all large scales and radii (frozen `M2RightInv.p428Target8`), negative at `π` (round 5),
  analytic in the angle; hence it crosses canonically, forwards and backwards.  Joint
  continuity follows from interior continuity.  The literal family may use negative angles.
* Gauge flip: the constant gauge transformation by `[[0,1],[-1,0]]` maps the twist at
  `(ε, t)` to `(-ε, -t)` (frozen covariance lane, extended to the all-plaquette carrier), so
  the backward crossing is the forward one and the coupling changes sign between them.
* Diagonal `U(1)`: the constant rotations `diag(e^{iα}, e^{-iα})` fix every configuration of
  the family, so the vacuum carrier and the first-order coefficient commute with them; on a
  charged complex line the coupling is the single number `⟪u₀, De u₀⟫` (round 8's `c₁`).

Nothing here proves a pinned goal.  The premises `TwistSoftCouplingFwd`, `TwistSoftU1`,
`TwistSoftCoupling` and `PathSoftCoupling` are explicit, unproved hypotheses on the actual
operators.
-/
