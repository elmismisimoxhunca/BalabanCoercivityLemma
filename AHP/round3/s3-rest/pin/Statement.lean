import ZT5A

/-!
S-3 REST PIN. The round-two dictionary below is copied verbatim through
InversesExist from AHP/round2/s3-normalisation/pin/Statement.lean.
The old first-term goals/proofs are deliberately not copied as new goals.

Page:line citations below refer to sources/corpus/pages/CMP99b_pNNN.md.
The rendered equations were also read; see PIN.md. In dimension 3 put
s_j = ell^j eta. We rebuild the physical-coordinate objects, with physical
pairings and adjoints, rather than defining the printed answer by rescaling
GenP.Nmat or P.G1inv. The fixed geometric/localisation conventions are listed
in PIN.md; this pin does not reopen S-1 or replace the frozen statement.

The two constructors are the two LINKED H/C conventions explicitly offered
on p.421:28, not the rejected abstract-jet recipes of Stage A.
-/

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

namespace AdalyFormal.Round2.S3Pin

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf staircasePath)
open Classical

abbrev Fine (P : IngrBParams) := BondFnL2 P.Lf
abbrev E (P : IngrBParams) := ↥(bondSupp P.G)
abbrev F (P : IngrBParams) := FSp P.G
abbrev Sites (P : IngrBParams) := SiteL2 P.Lf
abbrev UnitB (P : IngrBParams) := BondFnL2 P.Lu

/-- p.393:49-53, p.427:39: the last lattice has spacing one.
Thus eta = ell^(-k); this is also ZXR2Wire2:37. -/
noncomputable def mesh (P : IngrBParams) : ℝ := ((P.ell : ℝ) ^ P.k)⁻¹

/-- Physical spacing at level j, p.393:51,57. -/
noncomputable def spacing (P : IngrBParams) (j : ℕ) : ℝ :=
  (P.ell : ℝ) ^ j * mesh P

/-- p.392:61,101-108: normalised trace and eta^d. Same numerical field
values in the i*A_h chart as the frozen SuTwo carrier; not eta*A_h. -/
noncomputable def finePair (P : IngrBParams) (A B : E P) : ℝ :=
  mesh P ^ 3 * ⟪A, B⟫

/-- p.393:87-88 (fine sites); p.422:50,61,92 (level volume factors).
On the disjoint union of level bonds the measure is s_j^3, not eta^3. -/
noncomputable def levelMetric (P : IngrBParams) : F P →L[ℝ] F P :=
  diagW P.G (fun p => spacing P p.1 ^ 3)

noncomputable def levelPair (P : IngrBParams) (f g : F P) : ℝ :=
  ⟪f, levelMetric P g⟫

/-- p.392:66-70, p.394:58: each derivative has one eta inverse. -/
noncomputable def PrintedD (P : IngrBParams) : Sites P →L[ℝ] Fine P :=
  (mesh P)⁻¹ • gradL2 P.U

noncomputable def PrintedDs (P : IngrBParams) : Fine P →L[ℝ] Sites P :=
  ContinuousLinearMap.adjoint (PrintedD P)

noncomputable def PrintedLap (P : IngrBParams) : Sites P →L[ℝ] Sites P :=
  (PrintedDs P).comp (PrintedD P)

/-- (3.24), p.394:66-70. Recursive a_j belongs to SITES only.
The eta^-3 converts the explicitly weighted form to coordinates. -/
noncomputable def PrintedQpa (P : IngrBParams) : Sites P →L[ℝ] Sites P :=
  (mesh P ^ 3)⁻¹ •
    (∑ j ∈ Finset.range (P.k + 1), ∑ y : PeriodicLatticeSite P.Lf,
      if y ∈ P.G.Lam j then (ajSeq P.a P.ell j * spacing P j) •
        ((ContinuousLinearMap.adjoint (Qlev P.G P.U j y)).comp (Qlev P.G P.U j y))
      else 0)

/-- p.394:70-85: Dirichlet site sandwich. -/
noncomputable def PrintedDelp (P : IngrBParams) : Sites P →L[ℝ] Sites P :=
  ((siteMask P.G.Om0).comp (PrintedLap P + PrintedQpa P)).comp (siteMask P.G.Om0)

/-- Padding is solely a representation of the inverse on the site subspace.
It is guarded below, not treated as a source value at singular points. -/
noncomputable def PrintedGp (P : IngrBParams) : Sites P →L[ℝ] Sites P :=
  (Ring.inverse (PrintedDelp P + (1 - siteMask P.G.Om0))).comp (siteMask P.G.Om0)

/-- (3.21)-(3.23), p.394:39-58. Orthogonal projection onto the actual
physical Laplacian image of N(Q'); the common eta^3 weight does not change
orthogonality. Qlev/NQp are the frozen (3.18)-(3.19) component operators. -/
noncomputable def PrintedR (P : IngrBParams) : Sites P →L[ℝ] Sites P :=
  (Submodule.map
    ((((siteMask P.G.Om0).comp (PrintedLap P)).comp (siteMask P.G.Om0)) :
      Sites P →ₗ[ℝ] Sites P) (NQp P.G P.U)).starProjection

/-- (3.119), p.419:55. This is rebuilt, not stipulated equal to Wop. -/
noncomputable def PrintedW (P : IngrBParams) : Fine P →L[ℝ] Fine P :=
  1 - (PrintedD P).comp ((PrintedGp P).comp ((PrintedR P).comp (PrintedDs P)))

/-- (3.10), p.392:89-95: two inverse mesh powers. The retained plaqIn
selector is the S-1 departure, not a new scale convention. -/
noncomputable def PrintedDelta (P : IngrBParams) : Fine P →L[ℝ] Fine P :=
  ((mesh P)⁻¹ ^ 2) • Delta P.G P.U

noncomputable def PrintedDpi (P : IngrBParams) : E P →L[ℝ] E P :=
  (pE P.G).comp ((ContinuousLinearMap.adjoint (PrintedW P)).comp
    ((PrintedDelta P).comp ((PrintedW P).comp (iE P.G))))

/-- RD* on the Dirichlet bond space, (3.128), p.421:32-38. -/
noncomputable def PrintedT (P : IngrBParams) : E P →L[ℝ] Sites P :=
  (PrintedR P).comp ((PrintedDs P).comp (iE P.G))

/-- (3.14)-(3.15), p.393:28-40: Q_j = ell^-j times the raw first jet.
Same componentwise nonlinear averaging primitive, no freely chosen matrix. -/
noncomputable def PrintedQ (P : IngrBParams) : E P →L[ℝ] F P :=
  (QfullOf P.G P.U).comp (iE P.G)

/-- Weighted adjoint: eta^-3 Q^t diag(s_j^3).
The defining pairing identity is pinned by finePair and levelPair. -/
noncomputable def PrintedQs (P : IngrBParams) : F P →L[ℝ] E P :=
  (mesh P ^ 3)⁻¹ • ((ContinuousLinearMap.adjoint (PrintedQ P)).comp (levelMetric P))

/-- (3.16), p.393:57: constant a, weight a*s_j in the form.
Thus multiplication by a*s_j^-2 between Q and its physical adjoint. -/
noncomputable def PrintedMass (P : IngrBParams) : E P →L[ℝ] E P :=
  (PrintedQs P).comp
    ((diagW P.G (fun p => P.a * (spacing P p.1)⁻¹ ^ 2)).comp (PrintedQ P))

/-- (3.122), p.420:25-31. This G is the gauge-invariant one, not G_0. -/
noncomputable def PrintedGinv (P : IngrBParams) : E P →L[ℝ] E P :=
  PrintedDpi P + (ContinuousLinearMap.adjoint (PrintedT P)).comp (PrintedT P) +
    PrintedMass P

noncomputable def PrintedG (P : IngrBParams) : E P →L[ℝ] E P :=
  Ring.inverse (PrintedGinv P)

noncomputable def PrintedN0 (P : IngrBParams) : F P →L[ℝ] F P :=
  ((PrintedQ P).comp (PrintedG P)).comp (PrintedQs P)

/-- Plain H, (3.126), p.420:82. Inversion takes place on ALL levels. -/
noncomputable def PrintedH (P : IngrBParams) : F P →L[ℝ] E P :=
  ((PrintedG P).comp (PrintedQs P)).comp (Ring.inverse (PrintedN0 P))

/-- (3.11), p.392:101-108: physical J has eta^-3. The minus sign is
required by the i*A_h chart; see ZXR2Wire2:45-53, ZLocJ:71-89. -/
noncomputable def PrintedJ (P : IngrBParams) : E P :=
  pE P.G (WithLp.toLp 2 (fun b =>
    -(AdalyFormal.IngredientFamily.JSU2Loc (mesh P) (plaqIn P.G.Om0) P.U b)))

/-- The two jointly specified representations in p.421:28.
They are not permission to vary H while leaving C unchanged. -/
inductive Reading where
  | plainH
  | dimensionlessH
  deriving DecidableEq

/-- C_j^(2)(A), p.393:28-32: the raw second jet evaluated at ell^-j*A,
NOT the second coefficient of Q_j(eta*A)/(ell^j*eta). This tracks the
ARGUMENT change in C_j(ell^j*eta*A). -/
noncomputable def PrintedCjBil (P : IngrBParams) (j : ℕ) :
    Fine P →ₗ[ℝ] Fine P →ₗ[ℝ] Fine P :=
  ((1 / 2 : ℝ) • D2B P.G P.U j).compl₁₂
    ((((P.ell : ℝ) ^ j)⁻¹) • (1 : Fine P →ₗ[ℝ] Fine P))
    ((((P.ell : ℝ) ^ j)⁻¹) • (1 : Fine P →ₗ[ℝ] Fine P))

noncomputable def CInputScale (P : IngrBParams) (r : Reading) (j : ℕ) : ℝ :=
  match r with
  | .plainH => 1
  | .dimensionlessH => spacing P j

noncomputable def COutputScale (P : IngrBParams) (r : Reading) (j : ℕ) : ℝ :=
  match r with
  | .plainH => spacing P j
  | .dimensionlessH => 1

/-- (3.128), p.421:28,32-38: C_pi(A) = C(WA). The bilinear map uses
actual D2B and actual U at every level. No level-zero jet is inserted. -/
noncomputable def PrintedCBil (P : IngrBParams) (r : Reading) :
    E P →ₗ[ℝ] E P →ₗ[ℝ] F P :=
  LinearMap.mk₂ ℝ
    (fun A B => WithLp.toLp 2 (fun p : BIdx P.G =>
      COutputScale P r p.1 •
        (PrintedCjBil P p.1
          (CInputScale P r p.1 • PrintedW P (iE P.G A))
          (CInputScale P r p.1 • PrintedW P (iE P.G B))) p.2.1))
    (fun A A' B => by ext p; simp [smul_add])
    (fun c A B => by ext p; simp [smul_smul, mul_comm, mul_left_comm, mul_assoc])
    (fun A B B' => by ext p; simp [smul_add])
    (fun c A B => by ext p; simp [smul_smul, mul_comm, mul_left_comm, mul_assoc])

noncomputable def PrintedC (P : IngrBParams) (r : Reading) (A : E P) : F P :=
  PrintedCBil P r A A

/-- The first H convention on p.421:28 divides its input by s_j;
the second is plain (3.126). Also p.422:67-70. -/
noncomputable def PrintedHFor (P : IngrBParams) (r : Reading) : F P →L[ℝ] E P :=
  match r with
  | .plainH => PrintedH P
  | .dimensionlessH => (PrintedH P).comp (diagW P.G (fun p => (spacing P p.1)⁻¹))

/-- Physical bilinear form underlying (3.128), p.421:32-38.
Symmetrising its Riesz representative changes no diagonal value. -/
noncomputable def PrintedKBil (P : IngrBParams) (r : Reading) :
    E P →ₗ[ℝ] E P →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun A B => mesh P ^ 3 *
      (⟪A, PrintedDpi P B⟫ - 2 * ⟪PrintedHFor P r (PrintedCBil P r A B), PrintedJ P⟫ +
        ⟪PrintedT P A, PrintedT P B⟫ + ⟪A, PrintedMass P B⟫))
    (fun A A' B => by
      simp only [map_add, LinearMap.add_apply, inner_add_left]
      ring)
    (fun c A B => by
      simp [inner_smul_left]
      ring)
    (fun A B B' => by
      simp only [map_add, inner_add_left, inner_add_right]
      ring)
    (fun c A B => by
      simp [inner_smul_left, inner_smul_right]
      ring)

/-- (3.128) defines an operator using the eta^3 fine pairing, hence the
inverse metric in front of the unweighted Riesz construction. -/
noncomputable def PrintedG1inv (P : IngrBParams) (r : Reading) : E P →L[ℝ] E P :=
  (mesh P ^ 3)⁻¹ • symmOp (PrintedKBil P r)

noncomputable def PrintedG1 (P : IngrBParams) (r : Reading) : E P →L[ℝ] E P :=
  Ring.inverse (PrintedG1inv P r)

/-- Multilevel QG1Q*, (3.129), p.421:45; (3.132), p.422:50-54.
In particular this is NOT tau*N*tau* followed by an inverse. -/
noncomputable def PrintedN (P : IngrBParams) (r : Reading) : F P →L[ℝ] F P :=
  ((PrintedQ P).comp (PrintedG1 P r)).comp (PrintedQs P)

/-- p.427:39-48 and p.428:32-35: a unit field is zero on all lower
level rows. The finite sum is an explicit coordinate insertion, not tau*,
not a choice of an extension, and not multiplied by eta. -/
noncomputable def PrintedB (P : IngrBParams) (B : UnitB P) : F P :=
  WithLp.toLp 2 (fun p : BIdx P.G =>
    if (p.1 : ℕ) = P.k then
      ∑ e : Bond P.Lu, if unitBondEmb P.ell P.k P.Lu P.hell e = p.2.1 then B e else 0
    else 0)

/-- The first summand of (3.156), p.428:32, in printed physical units.
Every constituent above is built without GenP.firstTerm, Nmat or G1inv.
There is no inserted external eta or identification of inverse/compression. -/
noncomputable def PrintedFirstTerm (P : IngrBParams) (r : Reading) (B : UnitB P) : ℝ :=
  levelPair P (PrintedB P B) (Ring.inverse (PrintedN P r) (PrintedB P B))

/-- The actual subspace written immediately after (3.156), p.428:35.
Q1 B = 0 is imposed on ALL rows, not just CRowIn. Touching support and
axial staircases are the frozen geometric interpretation, explicitly retained. -/
def AdmissibleB (P : IngrBParams) (B : UnitB P) : Prop :=
  OnLambdaT P.Lam (WithLp.ofLp B) ∧
  (∀ y ∈ LamPrime P.ell P.Lam, ∀ x ∈ blockOf y P.ell,
    ∀ b ∈ staircasePath y x, B b = 0) ∧
  P.Q1 (WithLp.ofLp B) = 0

/-- The encoded admissible/covered geometric and regularity regime, at
arbitrary depth, not full support and not U=1. Equality of units needs no
smallness threshold once all inverses exist. R>=18, powers M=ell^m and c=12
retain the headline regime; they are disclosed in PIN.md. -/
def AdmissibleConfiguration (P : IngrBParams) : Prop :=
  2 ≤ P.ell ∧ 1 ≤ P.k ∧ 0 < P.a ∧
  ∃ m R : ℕ, ∃ α : ℝ, 1 ≤ m ∧ 18 ≤ R ∧ 0 < α ∧
    TorusOK P.ell (P.ell ^ m) P.Lu ∧
    Admissible P.ell (P.ell ^ m) R P.k P.S ∧
    LambdaOK2 P.ell (P.ell ^ m) R P.k P.S P.Lam ∧
    ClassCoupled P.ell (P.ell ^ m) 12 P.k P.S α (mesh P) P.U

/-- Every inverse used in either expression is guarded. No positivity is
inferred merely from invertibility. No guard assumes the comparison. -/
def InversesExist (P : IngrBParams) (r : Reading) : Prop :=
  IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)) ∧
  IsUnit P.data.Ginv ∧ IsUnit ((P.data.Q.comp P.data.G).comp P.data.Qs) ∧
  IsUnit P.G1inv ∧ IsUnit (GenP.Nmat P) ∧
  IsUnit (PrintedDelp P + (1 - siteMask P.G.Om0)) ∧
  IsUnit (PrintedGinv P) ∧ IsUnit (PrintedN0 P) ∧
  IsUnit (PrintedG1inv P r) ∧ IsUnit (PrintedN P r)

end AdalyFormal.Round2.S3Pin

namespace AdalyFormal.Round3.S3Rest

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.S3Pin
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open Classical

/-- p.392, first sentence: tr 1 = 1. In the retained i*A_h chart
tr(A_h B_h) = -ReTr(XY)/2. Not a full-Frobenius convention. -/
noncomputable def PrintedTracePair (X Y : SuTwo) : ℝ :=
  -(1 / 2 : ℝ) *
    (Matrix.trace ((X : Matrix (Fin 2) (Fin 2) ℂ) *
      (Y : Matrix (Fin 2) (Fin 2) ℂ))).re

/-- p.427, Sect. E: the lattice of B is UNIT, so its volume is 1^3.
p.392 (3.11) supplies the pairing/normalized trace convention. -/
noncomputable def PrintedUnitPair (P : IngrBParams) (B C : UnitB P) : ℝ :=
  ∑ b : Bond P.Lu, (1 : ℝ) ^ 3 * PrintedTracePair (B b) (C b)

/-- The separate subtraction in p.428 (3.156), NOT the mass inside G1.
a is constant as in p.393 (3.16); not the site recursion of p.394 (3.24). -/
noncomputable def PrintedMassSubtraction (P : IngrBParams) (B : UnitB P) : ℝ :=
  P.a * PrintedUnitPair P B B

/-- The metric in the lower-bound claim after (3.158), p.428, applied to
B-tilde, not to C B-tilde. Zero extension permits the full unit bond sum. -/
noncomputable def PrintedBondEnergy (P : IngrBParams) (Bt : Bond P.Lu → SuTwo) : ℝ :=
  PrintedUnitPair P (WithLp.toLp 2 Bt) (WithLp.toLp 2 Bt)

/-- Two LINKED ways to write the one-step nonlinear constraint at eta=1.
Raw: derivative of q and its raw quadratic coefficient; normalized: both
are divided by ell, as in p.393 (3.14) with j=1, eta=1.
CMP109 p.267 explicitly uses L*Qtilde*h=I and h*Ctilde^(2).
Its h is the inverse of the RAW derivative on the dropped bonds.
Neither constructor changes only the quadratic coefficient. -/
inductive UnitReading where
  | rawConstraint
  | normalizedConstraint
  deriving DecidableEq

noncomputable def unitConstraintScale (P : IngrBParams) (u : UnitReading) : ℝ :=
  match u with
  | .rawConstraint => 1
  | .normalizedConstraint => (P.ell : ℝ)⁻¹

/-- The actual raw first jet, not P.Q1 relabelled as a printed object.
Primitive: ZLocJet.lean:41; unit background: ZXR2Wire2.lean:67-69.
(3.13)-(3.15), pp.392-393, specialized to one step on the unit lattice. -/
noncomputable def PrintedUnitRawQ (P : IngrBParams) :
    (Bond P.Lu → SuTwo) →ₗ[ℝ] (CoarseBond P.Lu P.ell → SuTwo) where
  toFun B := fun c =>
    (suCoordFInv (QlinStepL 1 P.ell P.unitBgU (suCoordF B))) (c.1.1, c.2)
  map_add' A B := by funext c; simp
  map_smul' t B := by funext c; simp

noncomputable def PrintedUnitQ (P : IngrBParams) (u : UnitReading) :
    (Bond P.Lu → SuTwo) →ₗ[ℝ] (CoarseBond P.Lu P.ell → SuTwo) :=
  unitConstraintScale P u • PrintedUnitRawQ P

/-- Actual second Taylor coefficient, including 1/2, on the same background.
ZLocJet.lean:90-105 gives the componentwise second derivative, not a free jet.
For raw q(B) = rawQ B + rawC2(B) + higher terms, p.393 (3.14).
CMP109 p.267 identifies Dtilde^(2)=Ctilde^(2) BEFORE the corridor lift h. -/
noncomputable def PrintedUnitRemainder (P : IngrBParams) (u : UnitReading)
    (B : UnitB P) : CoarseBond P.Lu P.ell → SuTwo :=
  unitConstraintScale P u • fun c =>
    (suCoordFInv (C2StepL 1 P.ell P.unitBgU (suCoordF (WithLp.ofLp B)))) (c.1.1, c.2)

/-- p.428: solve for the dropped bonds. The finite coupled realization is
retained; it is not a claim that the printed single-variable equations
have already been proved to decouple for these nonabelian jets. -/
noncomputable def PrintedConstraintMatrix (P : IngrBParams) (u : UnitReading) :
    (Dset P.Lu P.ell P.Lam → SuTwo) →ₗ[ℝ] (Dset P.Lu P.ell P.Lam → SuTwo) :=
  (rhoD P.ell P.Lam).comp ((PrintedUnitQ P u).comp (iotaD P.ell P.Lam))

/-- Invert the printed constraint matrix on the dropped variables, then
insert the solution. This is assembled without H0inv, hLift, Cop or D2in. -/
noncomputable def PrintedCorridorLift (P : IngrBParams) (u : UnitReading) :
    (CoarseBond P.Lu P.ell → SuTwo) →ₗ[ℝ] (Bond P.Lu → SuTwo) :=
  (iotaD P.ell P.Lam).comp
    ((Ring.inverse (PrintedConstraintMatrix P u)).comp (rhoD P.ell P.Lam))

/-- CMP99b p.427 only describes Dtilde qualitatively. The concrete reading
here uses CMP109 p.267 (2.11), which explicitly refers back to (3.156):
the field inserted into H1 is h*Ctilde^(2), not the coarse Ctilde^(2) alone.
At unit spacing no fine eta power occurs in this construction. -/
noncomputable def PrintedDtilde (P : IngrBParams) (u : UnitReading) (B : UnitB P) :
    UnitB P :=
  WithLp.toLp 2 (PrintedCorridorLift P u (PrintedUnitRemainder P u B))

/-- Independently assembled C of p.428 (3.157). Same retained dropped set. -/
noncomputable def PrintedUnitC (P : IngrBParams) (u : UnitReading) :
    (Bond P.Lu → SuTwo) →ₗ[ℝ] (Bond P.Lu → SuTwo) :=
  LinearMap.id - (PrintedCorridorLift P u).comp (PrintedUnitQ P u)

/-- Physical H1 from p.421 (3.129), with G1 and the adjoint constructed
using the round-two physical pairings. All of F is inverted first. -/
noncomputable def PrintedH1 (P : IngrBParams) (r : Reading) : F P →L[ℝ] E P :=
  ((PrintedG1 P r).comp (PrintedQs P)).comp (Ring.inverse (PrintedN P r))

/-- The p.421 linked H convention. For the top-level inserted unit field
the additional input factor is s_k^-1 = 1, not eta^-1. -/
noncomputable def PrintedH1For (P : IngrBParams) (r : Reading) : F P →L[ℝ] E P :=
  match r with
  | .plainH => PrintedH1 P r
  | .dimensionlessH =>
      (PrintedH1 P r).comp (diagW P.G (fun p => (spacing P p.1)⁻¹))

/-- Magnitude (including its printed 2) of the LAST subtraction of (3.156).
The pairing is fine-lattice eta^3, the source is physical J, and Dtilde is
unit-lattice. It is NOT the C_pi correction already accounted for inside G1. -/
noncomputable def PrintedNonlinearTerm (P : IngrBParams) (r : Reading)
    (u : UnitReading) (B : UnitB P) : ℝ :=
  2 * finePair P (PrintedH1For P r (PrintedB P (PrintedDtilde P u B))) (PrintedJ P)

noncomputable def PrintedGenForm (P : IngrBParams) (r : Reading)
    (u : UnitReading) (B : UnitB P) : ℝ :=
  PrintedFirstTerm P r B - PrintedMassSubtraction P B - PrintedNonlinearTerm P r u B

/-- The full instance inequality of p.428 on the frozen B-tilde domain.
The separate global support/Ax/Q1 identification remains disclosed in PIN.md. -/
def PrintedInstIneq (P : IngrBParams) (r : Reading) (u : UnitReading) (gamma : ℝ) : Prop :=
  ∀ Bt : Bond P.Lu → SuTwo, OnLambdaTildeIn P.Lam P.ell Bt → OnLambdaT P.Lam Bt →
    gamma * PrintedBondEnergy P Bt ≤
      PrintedGenForm P r u (WithLp.toLp 2 (PrintedUnitC P u Bt))

/-- Explicit candidate, independent of all parameters, even depth. -/
def gammaScale (_ell _k : ℕ) : ℝ := 1

theorem gammaScale_pos (ell k : ℕ) : 0 < gammaScale ell k := by
  norm_num [gammaScale]

noncomputable def FrozenMassSubtraction (P : IngrBParams) (B : UnitB P) : ℝ :=
  P.a * ⟪B, B⟫

noncomputable def FrozenNonlinearTerm (P : IngrBParams) (B : UnitB P) : ℝ :=
  2 * ⟪P.H1in (P.D2in B), P.Jf⟫

/-- This bundles the real remaining termwise question and the requested
whole inequality. The first-term identity alone cannot settle this predicate.
The all-B comparison deliberately avoids assuming Cop's global-Q1 transfer. -/
def RestComparison (P : IngrBParams) (r : Reading) (u : UnitReading) : Prop :=
  (∀ B : UnitB P,
    FrozenMassSubtraction P B = PrintedMassSubtraction P B ∧
    FrozenNonlinearTerm P B = PrintedNonlinearTerm P r u B ∧
    GenP.genForm P B = PrintedGenForm P r u B) ∧
  (∀ Bt : Bond P.Lu → SuTwo,
    bondEnergy Bt = PrintedBondEnergy P Bt ∧
    GenP.genC P Bt = PrintedUnitC P u Bt) ∧
  (∀ gamma : ℝ,
    InstIneq P.ell P.k P.hell P.a P.Lu gamma P.S P.Lam P.U ↔
      PrintedInstIneq P r u (gammaScale P.ell P.k * gamma))

/-- Primary reading, both linked H/C conventions, all depths k>=1.
EXACTLY the round-two configuration/inverse guards. The comparison is
stronger than printed existence at singular corridor matrices: there both
sides are merely their totalized extensions. Negative witnesses below
must additionally have real corridor inverses; see PIN.md. -/
def GoalPos1 : Prop :=
  ∀ r : Reading, ∀ P : IngrBParams,
    AdmissibleConfiguration P → InversesExist P r → RestComparison P r .rawConstraint

/-- Divide the unit constraint AND its quadratic remainder by ell.
This is a linked representation of the same candidate, not a new power of eta. -/
def GoalPos2 : Prop :=
  ∀ r : Reading, ∀ P : IngrBParams,
    AdmissibleConfiguration P → InversesExist P r →
      RestComparison P r .normalizedConstraint

/-- Needed for the physical interpretation of the NEW corridor inverse.
Not added as an assumption of the positive goals. Explicit in all witnesses. -/
def CorridorInversesExist (P : IngrBParams) (u : UnitReading) : Prop :=
  Function.Bijective (H0 P.Lam P.Q1) ∧ IsUnit (PrintedConstraintMatrix P u)

/-- Change the ACTUAL parameter a everywhere, including G', G1 and their
inverses; not just the visible mass subtraction. Used only by the strong
negative certificate to state what a proposed a-rescaling would mean. -/
def massRescale (P : IngrBParams) (d : ℝ) : IngrBParams := { P with a := d * P.a }

/-- IMPORTANT: unequal summand ratios alone do not disprove equivalence
of two universally quantified inequalities. This separate obligation asks
for an actual truth-value separator for EVERY positive gamma/a rescaling
on this configuration, whenever the rescaled printed inverses exist.
It is deliberately stronger than failure of c=1, a unchanged. -/
def NoGammaMassRepair (P : IngrBParams) (r : Reading) (u : UnitReading) : Prop :=
  ∀ c d : ℝ, 0 < c → 0 < d →
    InversesExist (massRescale P d) r → CorridorInversesExist (massRescale P d) u →
    ∃ gamma : ℝ, 0 < gamma ∧
      ¬ (InstIneq P.ell P.k P.hell P.a P.Lu gamma P.S P.Lam P.U ↔
        PrintedInstIneq (massRescale P d) r u (c * gamma))

/-- Genuine depth>=2 witness, with actual background, real jets and source,
nonzero admitted fields, unequal nonlinear/energy ratios, AND the separate
no-repair obligation. No arbitrary matrices, free jets, or free J. -/
structure ScaleWitness (r : Reading) (u : UnitReading) where
  P : IngrBParams
  configuration : AdmissibleConfiguration P
  depth : 2 ≤ P.k
  inverses : InversesExist P r
  corridor : CorridorInversesExist P u
  BtJ : Bond P.Lu → SuTwo
  BtE : Bond P.Lu → SuTwo
  tildeJ : OnLambdaTildeIn P.Lam P.ell BtJ
  supportJ : OnLambdaT P.Lam BtJ
  tildeE : OnLambdaTildeIn P.Lam P.ell BtE
  supportE : OnLambdaT P.Lam BtE
  nonzeroJ : BtJ ≠ 0
  nonzeroE : BtE ≠ 0
  admissibleJ : AdmissibleB P (WithLp.toLp 2 (GenP.genC P BtJ))
  admissibleE : AdmissibleB P (WithLp.toLp 2 (GenP.genC P BtE))
  sameParamJ : GenP.genC P BtJ = PrintedUnitC P u BtJ
  sameParamE : GenP.genC P BtE = PrintedUnitC P u BtE
  nonlinear_ne : PrintedNonlinearTerm P r u (WithLp.toLp 2 (GenP.genC P BtJ)) ≠ 0
  energy_ne : PrintedBondEnergy P BtE ≠ 0
  ratio_ne :
    FrozenNonlinearTerm P (WithLp.toLp 2 (GenP.genC P BtJ)) /
        PrintedNonlinearTerm P r u (WithLp.toLp 2 (GenP.genC P BtJ)) ≠
      bondEnergy BtE / PrintedBondEnergy P BtE
  no_repair : NoGammaMassRepair P r u

def GoalNeg1 : Prop := ∃ r : Reading, Nonempty (ScaleWitness r .rawConstraint)
def GoalNeg2 : Prop := ∃ r : Reading, Nonempty (ScaleWitness r .normalizedConstraint)

/-- Contract check only: not a construction of a witness. -/
theorem ScaleWitness_not_comparison (r : Reading) (u : UnitReading)
    (w : ScaleWitness r u) : ¬ RestComparison w.P r u := by
  intro h
  apply w.ratio_ne
  rw [(h.1 (WithLp.toLp 2 (GenP.genC w.P w.BtJ))).2.1,
    (h.2.1 w.BtE).1, div_self w.nonlinear_ne, div_self w.energy_ne]

theorem GoalNeg1_implies_not_GoalPos1 : GoalNeg1 → ¬ GoalPos1 := by
  rintro ⟨r, ⟨w⟩⟩ hp
  exact ScaleWitness_not_comparison r .rawConstraint w
    (hp r w.P w.configuration w.inverses)

theorem GoalNeg2_implies_not_GoalPos2 : GoalNeg2 → ¬ GoalPos2 := by
  rintro ⟨r, ⟨w⟩⟩ hp
  exact ScaleWitness_not_comparison r .normalizedConstraint w
    (hp r w.P w.configuration w.inverses)

#check PrintedMassSubtraction
#check PrintedBondEnergy
#check PrintedDtilde
#check PrintedUnitC
#check PrintedH1For
#check PrintedNonlinearTerm
#check PrintedGenForm
#check PrintedInstIneq
#check RestComparison
#check NoGammaMassRepair
#check GoalPos1
#check GoalNeg1
#check GoalPos2
#check GoalNeg2

set_option pp.fullNames true

#print axioms PrintedTracePair
#print axioms PrintedMassSubtraction
#print axioms PrintedBondEnergy
#print axioms PrintedUnitRawQ
#print axioms PrintedUnitRemainder
#print axioms PrintedConstraintMatrix
#print axioms PrintedCorridorLift
#print axioms PrintedDtilde
#print axioms PrintedUnitC
#print axioms PrintedH1For
#print axioms PrintedNonlinearTerm
#print axioms PrintedGenForm
#print axioms PrintedInstIneq
#print axioms CorridorInversesExist
#print axioms NoGammaMassRepair
#print axioms GoalPos1
#print axioms GoalPos2
#print axioms GoalNeg1
#print axioms GoalNeg2
#print axioms gammaScale_pos
#print axioms ScaleWitness_not_comparison
#print axioms GoalNeg1_implies_not_GoalPos1
#print axioms GoalNeg2_implies_not_GoalPos2

end AdalyFormal.Round3.S3Rest
