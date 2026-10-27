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

/-! Round-two comparison proofs copied verbatim, through firstTerm_eq_printed. -/
namespace AdalyFormal.Round2.S3Pin

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open Classical

set_option synthInstance.maxHeartbeats 200000

/-- Reused verbatim from frozen NsCvOS4, with only the enclosing namespace changed. -/
theorem ring_inverse_eq_of_mul {R : Type*} [Ring R] (a b : R) (h1 : a * b = 1) (h2 : b * a = 1) :
    Ring.inverse a = b :=
  Ring.inverse_unit (⟨a, b, h1, h2⟩ : Rˣ)

/-- Reused verbatim from frozen NsCvOS4. -/
theorem inverse_smul' {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c : ℝ) (hc : c ≠ 0)
    (u : X →L[ℝ] X) (hu : IsUnit u) : Ring.inverse (c • u) = c⁻¹ • Ring.inverse u := by
  apply ring_inverse_eq_of_mul
  · rw [smul_mul_smul_comm, mul_inv_cancel₀ hc, one_smul, Ring.mul_inverse_cancel _ hu]
  · rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, one_smul, Ring.inverse_mul_cancel _ hu]

lemma mesh_pos (P : IngrBParams) : 0 < mesh P := P.eta_pos
lemma mesh_ne (P : IngrBParams) : mesh P ≠ 0 := (mesh_pos P).ne'
lemma pow_ell_ne (P : IngrBParams) (j : ℕ) : (P.ell : ℝ) ^ j ≠ 0 := by
  exact pow_ne_zero _ (by exact_mod_cast P.hell.ne')
lemma spacing_ne (P : IngrBParams) (j : ℕ) : spacing P j ≠ 0 :=
  mul_ne_zero (pow_ell_ne P j) (mesh_ne P)

lemma PrintedDs_scale (P : IngrBParams) :
    PrintedDs P = (mesh P)⁻¹ • gradAdj P.U := by
  simp [PrintedDs, PrintedD, gradAdj]

lemma PrintedLap_scale (P : IngrBParams) :
    PrintedLap P = (mesh P)⁻¹ ^ 2 • lapFull P.U := by
  rw [PrintedLap, PrintedDs_scale]
  ext1 x
  simp [PrintedD, lapFull, smul_smul, pow_two]

lemma PrintedQpa_scale (P : IngrBParams) :
    PrintedQpa P = (mesh P)⁻¹ ^ 2 • Qpa P.G P.U P.a := by
  ext1 x
  simp only [PrintedQpa, Qpa, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro y hy
  split_ifs
  · simp only [ContinuousLinearMap.smul_apply, smul_smul]
    congr 1
    change (mesh P ^ 3)⁻¹ * (ajSeq P.a P.ell j * spacing P j) =
      (mesh P)⁻¹ ^ 2 * (ajSeq P.a P.ell j * (P.ell : ℝ) ^ j)
    unfold spacing
    field_simp [mesh_ne P]
    <;> ring
  · simp

lemma PrintedDelp_scale (P : IngrBParams) :
    PrintedDelp P = (mesh P)⁻¹ ^ 2 • DelpA P.G P.U P.a := by
  rw [PrintedDelp, PrintedLap_scale, PrintedQpa_scale]
  ext1 x
  simp [DelpA, smul_add]

/-- The image of a nonzero scalar multiple of the Laplacian is unchanged. -/
lemma PrintedR_eq (P : IngrBParams) : PrintedR P = Rproj P.G P.U := by
  have hD : ((siteMask P.G.Om0).comp (PrintedLap P)).comp (siteMask P.G.Om0) =
      (mesh P)⁻¹ ^ 2 • lapDir P.G P.U := by
    rw [PrintedLap_scale]
    ext1 x
    simp [lapDir]
  have hi : Submodule.map
      ((((siteMask P.G.Om0).comp (PrintedLap P)).comp (siteMask P.G.Om0)) :
        Sites P →ₗ[ℝ] Sites P) (NQp P.G P.U) = RImage P.G P.U := by
    rw [hD]
    exact Submodule.map_smul _ _ _ (pow_ne_zero _ (inv_ne_zero (mesh_ne P)))
  unfold PrintedR Rproj
  congr 1

/-- Padding is handled by solving the site equation, not by scaling the exterior identity. -/
lemma PrintedGp_scale (P : IngrBParams)
    (hu : IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)))
    (hp : IsUnit (PrintedDelp P + (1 - siteMask P.G.Om0))) :
    PrintedGp P = mesh P ^ 2 • Gp P.G P.U P.a := by
  ext1 x
  apply (ContinuousLinearMap.isUnit_iff_bijective.mp hp).1
  have h := Gp_spec P.G P.U P.a hu x
  have hi := congrArg (fun T : Sites P →L[ℝ] Sites P => T (siteMask P.G.Om0 x))
    (Ring.mul_inverse_cancel (PrintedDelp P + (1 - siteMask P.G.Om0)) hp)
  change (PrintedDelp P + (1 - siteMask P.G.Om0))
      (Ring.inverse (PrintedDelp P + (1 - siteMask P.G.Om0)) (siteMask P.G.Om0 x)) = _
  rw [show (PrintedDelp P + (1 - siteMask P.G.Om0))
      (Ring.inverse (PrintedDelp P + (1 - siteMask P.G.Om0)) (siteMask P.G.Om0 x)) =
      siteMask P.G.Om0 x from hi]
  simp only [PrintedDelp_scale, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply, map_smul, h.1, h.2,
    sub_self, add_zero, smul_smul]
  rw [← mul_pow, mul_inv_cancel₀ (mesh_ne P), one_pow, one_smul]

lemma PrintedW_eq (P : IngrBParams)
    (hu : IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)))
    (hp : IsUnit (PrintedDelp P + (1 - siteMask P.G.Om0))) :
    PrintedW P = Wop P.G P.U P.a := by
  rw [PrintedW, PrintedGp_scale P hu hp, PrintedR_eq, PrintedDs_scale]
  ext1 x
  simp only [PrintedD, Wop, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, map_smul, smul_smul]
  have hs : (mesh P)⁻¹ * mesh P ^ 2 * (mesh P)⁻¹ = 1 := by
    field_simp [mesh_ne P]
  rw [hs, one_smul]

/-- The actual quadratic jet, with both input arguments rescaled as in (3.14). -/
lemma PrintedCjBil_scale (P : IngrBParams) (j : ℕ) (A B : Fine P) :
    PrintedCjBil P j A B = ((P.ell : ℝ) ^ j)⁻¹ ^ 2 •
      ((1 / 2 : ℝ) • D2B P.G P.U j A B) := by
  simp [PrintedCjBil, smul_smul, pow_two, mul_assoc]

/-- Unlike the discarded Stage-A recipe, this all-level coefficient is uniform. -/
lemma PrintedC_plain_scale (P : IngrBParams) (A : E P) :
    PrintedC P .plainH A = mesh P • C2fullOf P.G P.U (PrintedW P (iE P.G A)) := by
  apply PiLp.ext
  intro p
  simp only [PrintedC, PrintedCBil, LinearMap.mk₂_apply, CInputScale, COutputScale,
    one_smul, PrintedCjBil_scale, PiLp.smul_apply, WithLp.ofLp_toLp, C2fullOf, C2rawB]
  simp only [smul_smul]
  congr 1
  change spacing P p.1 * (((P.ell : ℝ) ^ (p.1 : ℕ))⁻¹ ^ 2 * (1 / 2)) =
    mesh P * (((P.ell : ℝ) ^ (p.1 : ℕ))⁻¹ * (1 / 2))
  unfold spacing
  field_simp

lemma PrintedC_plain_eq (P : IngrBParams)
    (hu : IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)))
    (hp : IsUnit (PrintedDelp P + (1 - siteMask P.G.Om0))) (A : E P) :
    PrintedC P .plainH A = mesh P • P.data.C2 A := by
  rw [PrintedC_plain_scale, PrintedW_eq P hu hp]
  rfl

/-- The two paired H/C conventions of p.421 yield the same bilinear contribution. -/
lemma PrintedHC_readings (P : IngrBParams) (A B : E P) :
    PrintedHFor P .dimensionlessH (PrintedCBil P .dimensionlessH A B) =
      PrintedHFor P .plainH (PrintedCBil P .plainH A B) := by
  change PrintedH P (diagW P.G (fun p => (spacing P p.1)⁻¹)
    (PrintedCBil P .dimensionlessH A B)) = PrintedH P (PrintedCBil P .plainH A B)
  congr 1
  apply PiLp.ext
  intro p
  simp only [diagW, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, WithLp.ofLp_toLp, PrintedCBil, LinearMap.mk₂_apply,
    CInputScale, COutputScale, one_smul, map_smul, LinearMap.smul_apply,
    PiLp.smul_apply, smul_smul]
  simp [inv_mul_cancel_left₀ (spacing_ne P p.1)]

lemma PrintedKBil_readings (P : IngrBParams) :
    PrintedKBil P .dimensionlessH = PrintedKBil P .plainH := by
  ext A B
  simp only [PrintedKBil, LinearMap.mk₂_apply, PrintedHC_readings]

lemma PrintedG1inv_readings (P : IngrBParams) :
    PrintedG1inv P .dimensionlessH = PrintedG1inv P .plainH := by
  simp only [PrintedG1inv, PrintedKBil_readings]

lemma PrintedFirstTerm_readings (P : IngrBParams) (B : UnitB P) :
    PrintedFirstTerm P .dimensionlessH B = PrintedFirstTerm P .plainH B := by
  simp only [PrintedFirstTerm, PrintedN, PrintedG1, PrintedG1inv_readings]

lemma InversesExist_readings (P : IngrBParams) :
    InversesExist P .dimensionlessH ↔ InversesExist P .plainH := by
  simp only [InversesExist, PrintedN, PrintedG1, PrintedG1inv_readings]

lemma PrintedQ_eq (P : IngrBParams) : PrintedQ P = P.data.Q := rfl

lemma PrintedQs_scale (P : IngrBParams) :
    PrintedQs P = (mesh P ^ 3)⁻¹ • (P.data.Qs.comp (levelMetric P)) := rfl

lemma PrintedT_scale (P : IngrBParams) :
    PrintedT P = (mesh P)⁻¹ • P.data.T := by
  rw [PrintedT, PrintedR_eq, PrintedDs_scale]
  ext1 A
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, map_smul]
  rfl

lemma PrintedDpi_scale (P : IngrBParams)
    (hu : IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)))
    (hp : IsUnit (PrintedDelp P + (1 - siteMask P.G.Om0))) :
    PrintedDpi P = (mesh P)⁻¹ ^ 2 • P.data.Dpi := by
  rw [PrintedDpi, PrintedW_eq P hu hp]
  ext1 A
  simp only [PrintedDelta, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    map_smul]
  rfl

lemma metric_mass_diag (P : IngrBParams) (f : F P) :
    levelMetric P (diagW P.G (fun p => P.a * (spacing P p.1)⁻¹ ^ 2) f) =
      mesh P • diagW P.G (massW P.G P.a) f := by
  apply PiLp.ext
  intro p
  simp only [levelMetric, diagW, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, WithLp.ofLp_toLp, PiLp.smul_apply, smul_smul]
  congr 1
  change spacing P p.1 ^ 3 * (P.a * (spacing P p.1)⁻¹ ^ 2) =
    mesh P * (P.a * (P.ell : ℝ) ^ (p.1 : ℕ))
  have hs := spacing_ne P p.1
  have : spacing P p.1 ^ 3 * (P.a * (spacing P p.1)⁻¹ ^ 2) = P.a * spacing P p.1 := by
    field_simp
  rw [this, spacing]
  ring

lemma PrintedMass_scale (P : IngrBParams) :
    PrintedMass P = (mesh P)⁻¹ ^ 2 • P.data.Mass := by
  have hm : P.data.Mass = P.data.Qs.comp ((diagW P.G (massW P.G P.a)).comp P.data.Q) := by
    change (pE P.G).comp ((MassFull P.G P.a P.sector).comp (iE P.G)) =
      (ContinuousLinearMap.adjoint (P.sector.Qfull.comp (iE P.G))).comp
        ((diagW P.G (massW P.G P.a)).comp (P.sector.Qfull.comp (iE P.G)))
    rw [ContinuousLinearMap.adjoint_comp]
    rfl
  rw [PrintedMass, PrintedQs_scale, PrintedQ_eq, hm]
  ext1 A
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    metric_mass_diag, map_smul, smul_smul]
  congr 1
  field_simp [mesh_ne P]

lemma PrintedGinv_scale (P : IngrBParams)
    (hu : IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)))
    (hp : IsUnit (PrintedDelp P + (1 - siteMask P.G.Om0))) :
    PrintedGinv P = (mesh P)⁻¹ ^ 2 • P.data.Ginv := by
  rw [PrintedGinv, PrintedDpi_scale P hu hp, PrintedT_scale, PrintedMass_scale]
  have ht : ContinuousLinearMap.adjoint P.data.T = P.data.Ts := rfl
  simp only [map_smul, starRingEnd_apply, star_trivial]
  rw [ht]
  ext1 A
  simp [BaseDataS.Ginv, smul_add, smul_smul, pow_two]

lemma PrintedG_scale (P : IngrBParams)
    (hu : IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)))
    (hp : IsUnit (PrintedDelp P + (1 - siteMask P.G.Om0)))
    (hg : IsUnit P.data.Ginv) :
    PrintedG P = mesh P ^ 2 • P.data.G := by
  rw [PrintedG, PrintedGinv_scale P hu hp,
    inverse_smul' _ (pow_ne_zero _ (inv_ne_zero (mesh_ne P))) _ hg]
  simp [BaseDataS.G]

lemma PrintedN0_scale (P : IngrBParams)
    (hu : IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)))
    (hp : IsUnit (PrintedDelp P + (1 - siteMask P.G.Om0)))
    (hg : IsUnit P.data.Ginv) :
    PrintedN0 P = (mesh P)⁻¹ •
      (((P.data.Q.comp P.data.G).comp P.data.Qs).comp (levelMetric P)) := by
  rw [PrintedN0, PrintedQ_eq, PrintedG_scale P hu hp hg, PrintedQs_scale]
  ext1 f
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, map_smul, smul_smul]
  congr 1
  field_simp [mesh_ne P]

lemma PrintedH_eq (P : IngrBParams)
    (hu : IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)))
    (hp : IsUnit (PrintedDelp P + (1 - siteMask P.G.Om0)))
    (hg : IsUnit P.data.Ginv)
    (hn : IsUnit ((P.data.Q.comp P.data.G).comp P.data.Qs))
    (hpn : IsUnit (PrintedN0 P)) :
    PrintedH P = P.data.H := by
  have hleft (f : F P) : PrintedH P (PrintedN0 P f) = PrintedG P (PrintedQs P f) := by
    unfold PrintedH
    have hi := congrArg (fun T : F P →L[ℝ] F P => T f)
      (Ring.inverse_mul_cancel (PrintedN0 P) hpn)
    change Ring.inverse (PrintedN0 P) (PrintedN0 P f) = f at hi
    simp only [ContinuousLinearMap.comp_apply, hi]
  have hright (f : F P) : P.data.H (P.data.Q (P.data.G (P.data.Qs f))) =
      P.data.G (P.data.Qs f) := by
    unfold BaseDataS.H
    have hi := congrArg (fun T : F P →L[ℝ] F P => T f)
      (Ring.inverse_mul_cancel _ hn)
    change Ring.inverse ((P.data.Q.comp P.data.G).comp P.data.Qs)
      (P.data.Q (P.data.G (P.data.Qs f))) = f at hi
    simp only [ContinuousLinearMap.comp_apply, hi]
  ext1 f
  obtain ⟨g, rfl⟩ := (ContinuousLinearMap.isUnit_iff_bijective.mp hpn).2 f
  rw [hleft, PrintedG_scale P hu hp hg, PrintedQs_scale, PrintedN0_scale P hu hp hg]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_smul, hright,
    smul_smul]
  congr 1
  field_simp [mesh_ne P]

lemma PrintedJ_scale (P : IngrBParams) :
    PrintedJ P = (mesh P ^ 3)⁻¹ • P.data.J := by
  have hs (b : Bond P.Lf) :
      AdalyFormal.IngredientFamily.JSU2Loc (mesh P) (plaqIn P.G.Om0) P.U b =
        (mesh P ^ 3)⁻¹ • AdalyFormal.IngredientFamily.JSU2Loc 1 (plaqIn P.G.Om0) P.U b := by
    apply Subtype.ext
    simp only [AdalyFormal.IngredientFamily.JSU2Loc, Submodule.coe_smul_of_tower,
      inv_one, one_pow, Complex.ofReal_one, mul_one]
    ext i j
    simp [Matrix.smul_apply, smul_eq_mul]
    ring
  unfold PrintedJ
  change pE P.G _ = (mesh P ^ 3)⁻¹ • pE P.G P.Jf
  rw [← map_smul]
  congr 1
  apply PiLp.ext
  intro b
  simp [IngrBParams.Jf, hs]

lemma e_inner_smul_left (P : IngrBParams) (x y : E P) (c : ℝ) :
    ⟪c • x, y⟫ = c * ⟪x, y⟫ := by
  exact real_inner_smul_left x y c

lemma e_inner_smul_right (P : IngrBParams) (x y : E P) (c : ℝ) :
    ⟪x, c • y⟫ = c * ⟪x, y⟫ := by
  exact real_inner_smul_right x y c

lemma PrintedKBil_diag_scale (P : IngrBParams)
    (hu : IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)))
    (hp : IsUnit (PrintedDelp P + (1 - siteMask P.G.Om0)))
    (hg : IsUnit P.data.Ginv)
    (hn : IsUnit ((P.data.Q.comp P.data.G).comp P.data.Qs))
    (hpn : IsUnit (PrintedN0 P)) (A : E P) :
    PrintedKBil P .plainH A A = mesh P * P.data.K A := by
  change mesh P ^ 3 *
    (⟪A, PrintedDpi P A⟫ - 2 * ⟪PrintedH P (PrintedC P .plainH A), PrintedJ P⟫ +
      ⟪PrintedT P A, PrintedT P A⟫ + ⟪A, PrintedMass P A⟫) = _
  rw [PrintedDpi_scale P hu hp, PrintedC_plain_eq P hu hp,
    PrintedH_eq P hu hp hg hn hpn, PrintedJ_scale, PrintedT_scale, PrintedMass_scale]
  simp only [ContinuousLinearMap.smul_apply, map_smul]
  have ht : ‖(mesh P)⁻¹ • P.data.T A‖ ^ 2 = (mesh P)⁻¹ ^ 2 * ‖P.data.T A‖ ^ 2 := by
    have h := norm_smul ((mesh P)⁻¹) (P.data.T A)
    rw [h, mul_pow, Real.norm_eq_abs, sq_abs]
  simp only [e_inner_smul_left, e_inner_smul_right,
    real_inner_self_eq_norm_sq, ht, BaseDataS.K]
  field_simp [mesh_ne P]
  <;> ring

lemma PrintedG1inv_scale (P : IngrBParams)
    (hu : IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)))
    (hp : IsUnit (PrintedDelp P + (1 - siteMask P.G.Om0)))
    (hg : IsUnit P.data.Ginv)
    (hn : IsUnit ((P.data.Q.comp P.data.G).comp P.data.Qs))
    (hpn : IsUnit (PrintedN0 P)) :
    PrintedG1inv P .plainH = (mesh P)⁻¹ ^ 2 • P.G1inv := by
  apply symm_unique
  · intro A B
    simp only [PrintedG1inv, ContinuousLinearMap.smul_apply]
    rw [e_inner_smul_left, e_inner_smul_right, symmOp_symm]
  · intro A B
    simp only [ContinuousLinearMap.smul_apply]
    rw [e_inner_smul_left, e_inner_smul_right, P.G1inv_spec.symm]
  · intro A
    simp only [PrintedG1inv, ContinuousLinearMap.smul_apply]
    rw [e_inner_smul_right, e_inner_smul_right, inner_symmOp_diag,
      PrintedKBil_diag_scale P hu hp hg hn hpn, P.G1inv_spec.form]
    field_simp [mesh_ne P]

lemma PrintedG1_scale (P : IngrBParams) (hI : InversesExist P .plainH) :
    PrintedG1 P .plainH = mesh P ^ 2 • P.data.G1 P.G1inv := by
  rcases hI with ⟨hu, hg, hn, h1, _, hp, _, hpn, _, _⟩
  rw [PrintedG1, PrintedG1inv_scale P hu hp hg hn hpn,
    inverse_smul' _ (pow_ne_zero _ (inv_ne_zero (mesh_ne P))) _ h1]
  simp [BaseDataS.G1]

lemma PrintedN_scale (P : IngrBParams) (hI : InversesExist P .plainH) :
    PrintedN P .plainH = (mesh P)⁻¹ • ((GenP.Nmat P).comp (levelMetric P)) := by
  rw [PrintedN, PrintedQ_eq, PrintedG1_scale P hI, PrintedQs_scale]
  ext1 f
  simp only [GenP.Nmat, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    map_smul, smul_smul]
  congr 1
  field_simp [mesh_ne P]

/-- The metric cancels after the inverse of the FULL multilevel operator.
No compression is inverted in this argument. -/
lemma physical_schur_scale (P : IngrBParams) (hI : InversesExist P .plainH) (f : F P) :
    levelPair P f (Ring.inverse (PrintedN P .plainH) f) =
      mesh P * ⟪f, Ring.inverse (GenP.Nmat P) f⟫ := by
  have hn := hI.2.2.2.2.1
  have hpn := hI.2.2.2.2.2.2.2.2.2
  have hphys := congrArg (fun T : F P →L[ℝ] F P => T f)
    (Ring.mul_inverse_cancel (PrintedN P .plainH) hpn)
  change PrintedN P .plainH (Ring.inverse (PrintedN P .plainH) f) = f at hphys
  have he := congrArg (fun T : F P →L[ℝ] F P =>
    T (Ring.inverse (PrintedN P .plainH) f)) (PrintedN_scale P hI)
  rw [he] at hphys
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply] at hphys
  change (mesh P)⁻¹ • GenP.Nmat P
    (levelMetric P (Ring.inverse (PrintedN P .plainH) f)) = f at hphys
  have hb : GenP.Nmat P (levelMetric P (Ring.inverse (PrintedN P .plainH) f)) = mesh P • f := by
    have := congrArg (fun v : F P => mesh P • v) hphys
    simpa [smul_smul, mesh_ne P] using this
  have hi := congrArg (fun T : F P →L[ℝ] F P =>
    T (levelMetric P (Ring.inverse (PrintedN P .plainH) f)))
    (Ring.inverse_mul_cancel (GenP.Nmat P) hn)
  change Ring.inverse (GenP.Nmat P) (GenP.Nmat P
    (levelMetric P (Ring.inverse (PrintedN P .plainH) f))) =
      levelMetric P (Ring.inverse (PrintedN P .plainH) f) at hi
  rw [hb, map_smul] at hi
  rw [levelPair, ← hi, real_inner_smul_right]

/-- Explicit insertion is the adjoint of top-row extraction, without a full-support premise. -/
lemma PrintedB_eq_tau_adjoint (P : IngrBParams) (B : UnitB P) :
    PrintedB P B = ContinuousLinearMap.adjoint P.tau B := by
  apply ext_inner_left ℝ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hs (p : BIdx P.G) : ⟪f p, (PrintedB P B) p⟫ =
      ∑ e : Bond P.Lu, if (p.1 : ℕ) = P.k then
        if unitBondEmb P.ell P.k P.Lu P.hell e = p.2.1 then ⟪f p, B e⟫ else 0
        else 0 := by
    by_cases hj : (p.1 : ℕ) = P.k
    · simp only [PrintedB, WithLp.ofLp_toLp, hj, if_true, inner_sum]
      apply Finset.sum_congr rfl
      intro e he
      split_ifs <;> simp
    · simp [PrintedB, hj]
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp_rw [hs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hb : unitBondEmb P.ell P.k P.Lu P.hell e ∈ bondsLam P.G P.k
  · let q : BIdx P.G := ⟨Fin.last P.k, ⟨unitBondEmb P.ell P.k P.Lu P.hell e, hb⟩⟩
    have hq : ∀ p : BIdx P.G, (p.1 : ℕ) = P.k →
        unitBondEmb P.ell P.k P.Lu P.hell e = p.2.1 → p = q := by
      intro p hj heq
      obtain ⟨j, b⟩ := p
      have hj' : j = Fin.last P.k := Fin.ext hj
      subst j
      have hb' : b = q.2 := Subtype.ext heq.symm
      subst b
      rfl
    rw [Finset.sum_eq_single q]
    · simp [q, IngrBParams.tau, tauExt, hb]
    · intro p hp hne
      by_cases hj : (p.1 : ℕ) = P.k
      · by_cases heq : unitBondEmb P.ell P.k P.Lu P.hell e = p.2.1
        · exact False.elim (hne (hq p hj heq))
        · simp [heq]
      · simp [hj]
    · simp
  · have hz (p : BIdx P.G) : (if (p.1 : ℕ) = P.k then
        if unitBondEmb P.ell P.k P.Lu P.hell e = p.2.1 then ⟪f p, B e⟫ else 0
        else 0) = 0 := by
      by_cases hj : (p.1 : ℕ) = P.k
      · by_cases heq : unitBondEmb P.ell P.k P.Lu P.hell e = p.2.1
        · have hm : unitBondEmb P.ell P.k P.Lu P.hell e ∈ bondsLam P.G (p.1 : ℕ) := by
            rw [heq]
            exact p.2.property
          rw [hj] at hm
          exact False.elim (hb hm)
        · simp [heq]
      · simp [hj]
    simp only [hz, Finset.sum_const_zero]
    simp [IngrBParams.tau, tauExt, hb]

/-- Stronger comparison: all B and all depths, with exactly the pinned inverse guards. -/
theorem firstTerm_eq_printed (P : IngrBParams) (hI : InversesExist P .plainH)
    (B : UnitB P) : GenP.firstTerm P B = PrintedFirstTerm P .plainH B := by
  rw [PrintedFirstTerm, physical_schur_scale P hI, PrintedB_eq_tau_adjoint]
  rfl


end AdalyFormal.Round2.S3Pin

#print axioms AdalyFormal.Round2.S3Pin.ring_inverse_eq_of_mul
#print axioms AdalyFormal.Round2.S3Pin.inverse_smul'
#print axioms AdalyFormal.Round2.S3Pin.mesh_pos
#print axioms AdalyFormal.Round2.S3Pin.mesh_ne
#print axioms AdalyFormal.Round2.S3Pin.pow_ell_ne
#print axioms AdalyFormal.Round2.S3Pin.spacing_ne
#print axioms AdalyFormal.Round2.S3Pin.PrintedDs_scale
#print axioms AdalyFormal.Round2.S3Pin.PrintedLap_scale
#print axioms AdalyFormal.Round2.S3Pin.PrintedQpa_scale
#print axioms AdalyFormal.Round2.S3Pin.PrintedDelp_scale
#print axioms AdalyFormal.Round2.S3Pin.PrintedR_eq
#print axioms AdalyFormal.Round2.S3Pin.PrintedGp_scale
#print axioms AdalyFormal.Round2.S3Pin.PrintedW_eq
#print axioms AdalyFormal.Round2.S3Pin.PrintedCjBil_scale
#print axioms AdalyFormal.Round2.S3Pin.PrintedC_plain_scale
#print axioms AdalyFormal.Round2.S3Pin.PrintedC_plain_eq
#print axioms AdalyFormal.Round2.S3Pin.PrintedHC_readings
#print axioms AdalyFormal.Round2.S3Pin.PrintedKBil_readings
#print axioms AdalyFormal.Round2.S3Pin.PrintedG1inv_readings
#print axioms AdalyFormal.Round2.S3Pin.PrintedFirstTerm_readings
#print axioms AdalyFormal.Round2.S3Pin.InversesExist_readings
#print axioms AdalyFormal.Round2.S3Pin.PrintedQ_eq
#print axioms AdalyFormal.Round2.S3Pin.PrintedQs_scale
#print axioms AdalyFormal.Round2.S3Pin.PrintedT_scale
#print axioms AdalyFormal.Round2.S3Pin.PrintedDpi_scale
#print axioms AdalyFormal.Round2.S3Pin.metric_mass_diag
#print axioms AdalyFormal.Round2.S3Pin.PrintedMass_scale
#print axioms AdalyFormal.Round2.S3Pin.PrintedGinv_scale
#print axioms AdalyFormal.Round2.S3Pin.PrintedG_scale
#print axioms AdalyFormal.Round2.S3Pin.PrintedN0_scale
#print axioms AdalyFormal.Round2.S3Pin.PrintedH_eq
#print axioms AdalyFormal.Round2.S3Pin.PrintedJ_scale
#print axioms AdalyFormal.Round2.S3Pin.e_inner_smul_left
#print axioms AdalyFormal.Round2.S3Pin.e_inner_smul_right
#print axioms AdalyFormal.Round2.S3Pin.PrintedKBil_diag_scale
#print axioms AdalyFormal.Round2.S3Pin.PrintedG1inv_scale
#print axioms AdalyFormal.Round2.S3Pin.PrintedG1_scale
#print axioms AdalyFormal.Round2.S3Pin.PrintedN_scale
#print axioms AdalyFormal.Round2.S3Pin.physical_schur_scale
#print axioms AdalyFormal.Round2.S3Pin.PrintedB_eq_tau_adjoint
#print axioms AdalyFormal.Round2.S3Pin.firstTerm_eq_printed

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

lemma PrintedTracePair_eq_inner (X Y : SuTwo) : PrintedTracePair X Y = ⟪X, Y⟫ := by
  exact (AdalyFormal.Balaban.SuTwoInner.inner_eq_trace X Y).symm

lemma PrintedUnitPair_eq_inner (P : IngrBParams) (B C : UnitB P) :
    PrintedUnitPair P B C = ⟪B, C⟫ := by
  simp only [PrintedUnitPair, one_pow, one_mul, PrintedTracePair_eq_inner, PiLp.inner_apply]

lemma massSubtraction_eq (P : IngrBParams) (B : UnitB P) :
    FrozenMassSubtraction P B = PrintedMassSubtraction P B := by
  rw [FrozenMassSubtraction, PrintedMassSubtraction, PrintedUnitPair_eq_inner]

lemma bondEnergy_eq (P : IngrBParams) (Bt : Bond P.Lu → SuTwo) :
    bondEnergy Bt = PrintedBondEnergy P Bt := by
  simp only [PrintedBondEnergy, PrintedUnitPair_eq_inner, PiLp.inner_apply,
    real_inner_self_eq_norm_sq, bondEnergy]

/-- The normalized genuine jet is exactly the frozen normalized jet. -/
lemma PrintedUnitQ_normalized (P : IngrBParams) :
    PrintedUnitQ P .normalizedConstraint = P.Q1 := by
  ext B c
  rfl

lemma PrintedUnitRemainder_normalized (P : IngrBParams) (B : UnitB P) :
    PrintedUnitRemainder P .normalizedConstraint B =
      (P.ell : ℝ)⁻¹ • C2tilde P.ell P.unitBgU (WithLp.ofLp B) := rfl

/-- Match the two independently totalized inverses, including the singular case.
The bijective branch follows the frozen H0_H0inv proof, ZXR2Unit2:107. -/
lemma H0inv_eq_ring_inverse (P : IngrBParams) :
    H0inv P.Lam P.Q1 = Ring.inverse (H0 P.Lam P.Q1) := by
  by_cases hb : Function.Bijective (H0 P.Lam P.Q1)
  · unfold H0inv
    rw [dif_pos hb]
    symm
    apply ring_inverse_eq_of_mul
    · exact LinearMap.ext (fun w =>
        (LinearEquiv.ofBijective (H0 P.Lam P.Q1) hb).apply_symm_apply w)
    · exact LinearMap.ext (fun w =>
        (LinearEquiv.ofBijective (H0 P.Lam P.Q1) hb).symm_apply_apply w)
  · rw [H0inv, dif_neg hb, Ring.inverse_non_unit]
    exact fun h => hb ((Module.End.isUnit_iff _).mp h)

lemma PrintedConstraintMatrix_normalized (P : IngrBParams) :
    PrintedConstraintMatrix P .normalizedConstraint = H0 P.Lam P.Q1 := by
  rw [PrintedConstraintMatrix, PrintedUnitQ_normalized]
  rfl

lemma PrintedCorridorLift_normalized (P : IngrBParams) :
    PrintedCorridorLift P .normalizedConstraint = hLift P.Lam P.Q1 := by
  rw [PrintedCorridorLift, PrintedConstraintMatrix_normalized, ← H0inv_eq_ring_inverse]
  rfl

lemma PrintedDtilde_normalized (P : IngrBParams) (B : UnitB P) :
    PrintedDtilde P .normalizedConstraint B = P.D2in B := by
  rw [PrintedDtilde, PrintedCorridorLift_normalized, PrintedUnitRemainder_normalized, map_smul]
  rfl

lemma genC_eq_normalized (P : IngrBParams) :
    GenP.genC P = PrintedUnitC P .normalizedConstraint := by
  rw [PrintedUnitC, PrintedCorridorLift_normalized, PrintedUnitQ_normalized]
  rfl

/-- Reuse the round-two PrintedH_eq argument with the corrected propagator. -/
lemma PrintedH1_eq (P : IngrBParams) (hI : InversesExist P .plainH) :
    PrintedH1 P .plainH = P.data.H1 P.G1inv := by
  have hn := hI.2.2.2.2.1
  have hpn := hI.2.2.2.2.2.2.2.2.2
  have hleft (f : F P) : PrintedH1 P .plainH (PrintedN P .plainH f) =
      PrintedG1 P .plainH (PrintedQs P f) := by
    unfold PrintedH1
    have hi := congrArg (fun T : F P →L[ℝ] F P => T f)
      (Ring.inverse_mul_cancel (PrintedN P .plainH) hpn)
    change Ring.inverse (PrintedN P .plainH) (PrintedN P .plainH f) = f at hi
    simp only [ContinuousLinearMap.comp_apply, hi]
  have hright (f : F P) : P.data.H1 P.G1inv (GenP.Nmat P f) =
      P.data.G1 P.G1inv (P.data.Qs f) := by
    unfold BaseDataS.H1
    have hi := congrArg (fun T : F P →L[ℝ] F P => T f)
      (Ring.inverse_mul_cancel (GenP.Nmat P) hn)
    change Ring.inverse (GenP.Nmat P) (GenP.Nmat P f) = f at hi
    change P.data.G1 P.G1inv (P.data.Qs (Ring.inverse (GenP.Nmat P) (GenP.Nmat P f))) = _
    rw [hi]
  ext1 f
  obtain ⟨g, rfl⟩ := (ContinuousLinearMap.isUnit_iff_bijective.mp hpn).2 f
  rw [hleft, PrintedG1_scale P hI, PrintedQs_scale, PrintedN_scale P hI]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_smul, hright,
    smul_smul]
  congr 1
  field_simp [mesh_ne P]

lemma spacing_top (P : IngrBParams) : spacing P P.k = 1 := by
  exact mul_inv_cancel₀ (pow_ell_ne P P.k)

lemma top_diag_identity (P : IngrBParams) (B : UnitB P) :
    diagW P.G (fun p => (spacing P p.1)⁻¹) (PrintedB P B) = PrintedB P B := by
  apply PiLp.ext
  intro p
  by_cases hj : (p.1 : ℕ) = P.k
  · simp [diagW, PrintedB, hj, spacing_top]
  · simp [diagW, PrintedB, hj]

lemma PrintedH1_readings (P : IngrBParams) :
    PrintedH1 P .dimensionlessH = PrintedH1 P .plainH := by
  simp only [PrintedH1, PrintedN, PrintedG1, PrintedG1inv_readings]

lemma inverses_plain (P : IngrBParams) (r : Reading) (hI : InversesExist P r) :
    InversesExist P .plainH := by
  cases r
  · exact hI
  · exact (InversesExist_readings P).mp hI

lemma PrintedH1For_on_top (P : IngrBParams) (r : Reading)
    (hI : InversesExist P r) (B : UnitB P) :
    PrintedH1For P r (PrintedB P B) =
      P.data.H1 P.G1inv (ContinuousLinearMap.adjoint P.tau B) := by
  have hi := inverses_plain P r hI
  cases r
  · rw [PrintedH1For, PrintedH1_eq P hi, PrintedB_eq_tau_adjoint]
  · rw [PrintedH1For, ContinuousLinearMap.comp_apply, top_diag_identity,
      PrintedH1_readings, PrintedH1_eq P hi, PrintedB_eq_tau_adjoint]

lemma finePair_J_eq (P : IngrBParams) (A : E P) :
    finePair P A (PrintedJ P) = ⟪iE P.G A, P.Jf⟫ := by
  rw [finePair, PrintedJ_scale, e_inner_smul_right, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ (mesh_ne P)), one_mul]
  change ⟪A, pE P.G P.Jf⟫ = ⟪iE P.G A, P.Jf⟫
  exact ContinuousLinearMap.adjoint_inner_right (iE P.G) A P.Jf

lemma nonlinear_eq_normalized (P : IngrBParams) (r : Reading)
    (hI : InversesExist P r) (B : UnitB P) :
    FrozenNonlinearTerm P B = PrintedNonlinearTerm P r .normalizedConstraint B := by
  rw [PrintedNonlinearTerm, PrintedDtilde_normalized, PrintedH1For_on_top P r hI,
    finePair_J_eq]
  rfl

lemma firstTerm_eq_all_readings (P : IngrBParams) (r : Reading)
    (hI : InversesExist P r) (B : UnitB P) :
    GenP.firstTerm P B = PrintedFirstTerm P r B := by
  have hi := inverses_plain P r hI
  cases r
  · exact firstTerm_eq_printed P hi B
  · rw [PrintedFirstTerm_readings]
    exact firstTerm_eq_printed P hi B

lemma genForm_eq_normalized (P : IngrBParams) (r : Reading)
    (hI : InversesExist P r) (B : UnitB P) :
    GenP.genForm P B = PrintedGenForm P r .normalizedConstraint B := by
  change GenP.firstTerm P B - FrozenMassSubtraction P B - FrozenNonlinearTerm P B = _
  rw [firstTerm_eq_all_readings P r hI, massSubtraction_eq, nonlinear_eq_normalized P r hI]
  rfl

/-- Full pointwise comparison, in fact independent of the configuration predicate. -/
theorem restComparison_normalized (P : IngrBParams) (r : Reading)
    (hI : InversesExist P r) : RestComparison P r .normalizedConstraint := by
  refine ⟨?_, ?_, ?_⟩
  · intro B
    exact ⟨massSubtraction_eq P B, nonlinear_eq_normalized P r hI B,
      genForm_eq_normalized P r hI B⟩
  · intro Bt
    exact ⟨bondEnergy_eq P Bt, LinearMap.congr_fun (genC_eq_normalized P) Bt⟩
  · intro gamma
    change (∀ Bt : Bond P.Lu → SuTwo, OnLambdaTildeIn P.Lam P.ell Bt →
      OnLambdaT P.Lam Bt → gamma * bondEnergy Bt ≤
        GenP.genForm P (WithLp.toLp 2 (GenP.genC P Bt))) ↔ _
    simp only [PrintedInstIneq, gammaScale, one_mul, genForm_eq_normalized P r hI,
      genC_eq_normalized, bondEnergy_eq P]

/-- Exact pinned positive goal, with no additional inverse or support premise. -/
theorem goalPos2_proved : GoalPos2 := by
  intro r P _ hI
  exact restComparison_normalized P r hI

end AdalyFormal.Round3.S3Rest

#print axioms AdalyFormal.Round3.S3Rest.PrintedTracePair_eq_inner
#print axioms AdalyFormal.Round3.S3Rest.PrintedUnitPair_eq_inner
#print axioms AdalyFormal.Round3.S3Rest.massSubtraction_eq
#print axioms AdalyFormal.Round3.S3Rest.bondEnergy_eq
#print axioms AdalyFormal.Round3.S3Rest.PrintedUnitQ_normalized
#print axioms AdalyFormal.Round3.S3Rest.PrintedUnitRemainder_normalized
#print axioms AdalyFormal.Round3.S3Rest.H0inv_eq_ring_inverse
#print axioms AdalyFormal.Round3.S3Rest.PrintedConstraintMatrix_normalized
#print axioms AdalyFormal.Round3.S3Rest.PrintedCorridorLift_normalized
#print axioms AdalyFormal.Round3.S3Rest.PrintedDtilde_normalized
#print axioms AdalyFormal.Round3.S3Rest.genC_eq_normalized
#print axioms AdalyFormal.Round3.S3Rest.PrintedH1_eq
#print axioms AdalyFormal.Round3.S3Rest.spacing_top
#print axioms AdalyFormal.Round3.S3Rest.top_diag_identity
#print axioms AdalyFormal.Round3.S3Rest.PrintedH1_readings
#print axioms AdalyFormal.Round3.S3Rest.inverses_plain
#print axioms AdalyFormal.Round3.S3Rest.PrintedH1For_on_top
#print axioms AdalyFormal.Round3.S3Rest.finePair_J_eq
#print axioms AdalyFormal.Round3.S3Rest.nonlinear_eq_normalized
#print axioms AdalyFormal.Round3.S3Rest.firstTerm_eq_all_readings
#print axioms AdalyFormal.Round3.S3Rest.genForm_eq_normalized
#print axioms AdalyFormal.Round3.S3Rest.restComparison_normalized
#print axioms AdalyFormal.Round3.S3Rest.goalPos2_proved

/-! Explicit audit of the copied dictionary and every remaining local definition. -/
#print axioms AdalyFormal.Round2.S3Pin.Fine
#print axioms AdalyFormal.Round2.S3Pin.E
#print axioms AdalyFormal.Round2.S3Pin.F
#print axioms AdalyFormal.Round2.S3Pin.Sites
#print axioms AdalyFormal.Round2.S3Pin.UnitB
#print axioms AdalyFormal.Round2.S3Pin.mesh
#print axioms AdalyFormal.Round2.S3Pin.spacing
#print axioms AdalyFormal.Round2.S3Pin.finePair
#print axioms AdalyFormal.Round2.S3Pin.levelMetric
#print axioms AdalyFormal.Round2.S3Pin.levelPair
#print axioms AdalyFormal.Round2.S3Pin.PrintedD
#print axioms AdalyFormal.Round2.S3Pin.PrintedDs
#print axioms AdalyFormal.Round2.S3Pin.PrintedLap
#print axioms AdalyFormal.Round2.S3Pin.PrintedQpa
#print axioms AdalyFormal.Round2.S3Pin.PrintedDelp
#print axioms AdalyFormal.Round2.S3Pin.PrintedGp
#print axioms AdalyFormal.Round2.S3Pin.PrintedR
#print axioms AdalyFormal.Round2.S3Pin.PrintedW
#print axioms AdalyFormal.Round2.S3Pin.PrintedDelta
#print axioms AdalyFormal.Round2.S3Pin.PrintedDpi
#print axioms AdalyFormal.Round2.S3Pin.PrintedT
#print axioms AdalyFormal.Round2.S3Pin.PrintedQ
#print axioms AdalyFormal.Round2.S3Pin.PrintedQs
#print axioms AdalyFormal.Round2.S3Pin.PrintedMass
#print axioms AdalyFormal.Round2.S3Pin.PrintedGinv
#print axioms AdalyFormal.Round2.S3Pin.PrintedG
#print axioms AdalyFormal.Round2.S3Pin.PrintedN0
#print axioms AdalyFormal.Round2.S3Pin.PrintedH
#print axioms AdalyFormal.Round2.S3Pin.PrintedJ
#print axioms AdalyFormal.Round2.S3Pin.Reading
#print axioms AdalyFormal.Round2.S3Pin.PrintedCjBil
#print axioms AdalyFormal.Round2.S3Pin.CInputScale
#print axioms AdalyFormal.Round2.S3Pin.COutputScale
#print axioms AdalyFormal.Round2.S3Pin.PrintedCBil
#print axioms AdalyFormal.Round2.S3Pin.PrintedC
#print axioms AdalyFormal.Round2.S3Pin.PrintedHFor
#print axioms AdalyFormal.Round2.S3Pin.PrintedKBil
#print axioms AdalyFormal.Round2.S3Pin.PrintedG1inv
#print axioms AdalyFormal.Round2.S3Pin.PrintedG1
#print axioms AdalyFormal.Round2.S3Pin.PrintedN
#print axioms AdalyFormal.Round2.S3Pin.PrintedB
#print axioms AdalyFormal.Round2.S3Pin.PrintedFirstTerm
#print axioms AdalyFormal.Round2.S3Pin.AdmissibleB
#print axioms AdalyFormal.Round2.S3Pin.AdmissibleConfiguration
#print axioms AdalyFormal.Round2.S3Pin.InversesExist
#print axioms AdalyFormal.Round3.S3Rest.PrintedUnitPair
#print axioms AdalyFormal.Round3.S3Rest.UnitReading
#print axioms AdalyFormal.Round3.S3Rest.unitConstraintScale
#print axioms AdalyFormal.Round3.S3Rest.PrintedUnitQ
#print axioms AdalyFormal.Round3.S3Rest.PrintedH1
#print axioms AdalyFormal.Round3.S3Rest.gammaScale
#print axioms AdalyFormal.Round3.S3Rest.FrozenMassSubtraction
#print axioms AdalyFormal.Round3.S3Rest.FrozenNonlinearTerm
#print axioms AdalyFormal.Round3.S3Rest.RestComparison
#print axioms AdalyFormal.Round3.S3Rest.massRescale
#print axioms AdalyFormal.Round3.S3Rest.ScaleWitness

/-!
Round five: exact raw/normalized reduction. The entire round-three positive
attempt above, including the pin and GoalPos2 proof, is copied verbatim.
The nonunit branch is part of the proof: multiplying a corridor matrix by a
nonzero scalar preserves its unit status, so both singular inverses are zero.
No corridor-invertibility hypothesis is imposed on any comparison below.
-/
namespace AdalyFormal.Round3.S3Rest

open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.S3Pin
open Classical

/-- Nonzero scalar multiplication preserves invertibility, even on the zero module. -/
lemma linear_isUnit_smul_iff {V : Type*} [AddCommGroup V] [Module ℝ V]
    (c : ℝ) (hc : c ≠ 0) (A : V →ₗ[ℝ] V) : IsUnit (c • A) ↔ IsUnit A := by
  simpa only [Units.smul_def, Units.val_mk0] using
    (isUnit_smul_iff (Units.mk0 c hc) A)

/-- Totalized inverse scaling. In particular, no unit hypothesis on A is needed. -/
lemma linear_inverse_smul_total {V : Type*} [AddCommGroup V] [Module ℝ V]
    (c : ℝ) (hc : c ≠ 0) (A : V →ₗ[ℝ] V) :
    Ring.inverse (c • A) = c⁻¹ • Ring.inverse A := by
  by_cases hA : IsUnit A
  · apply ring_inverse_eq_of_mul
    · rw [smul_mul_smul_comm, mul_inv_cancel₀ hc, one_smul,
        Ring.mul_inverse_cancel _ hA]
    · rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, one_smul,
        Ring.inverse_mul_cancel _ hA]
  · have hscaled : ¬ IsUnit (c • A) :=
      fun h => hA ((linear_isUnit_smul_iff c hc A).mp h)
    rw [Ring.inverse_non_unit _ hscaled, Ring.inverse_non_unit _ hA, smul_zero]

lemma raw_ell_ne (P : IngrBParams) : (P.ell : ℝ) ≠ 0 := by
  exact_mod_cast P.hell.ne'

lemma PrintedUnitQ_raw_eq_smul_normalized (P : IngrBParams) :
    PrintedUnitQ P .rawConstraint = (P.ell : ℝ) • PrintedUnitQ P .normalizedConstraint := by
  simp only [PrintedUnitQ, unitConstraintScale, one_smul, smul_smul,
    mul_inv_cancel₀ (raw_ell_ne P)]

lemma PrintedUnitRemainder_raw_eq_smul_normalized (P : IngrBParams) (B : UnitB P) :
    PrintedUnitRemainder P .rawConstraint B =
      (P.ell : ℝ) • PrintedUnitRemainder P .normalizedConstraint B := by
  simp only [PrintedUnitRemainder, unitConstraintScale, one_smul, smul_smul,
    mul_inv_cancel₀ (raw_ell_ne P)]

lemma PrintedConstraintMatrix_raw_eq_smul_normalized (P : IngrBParams) :
    PrintedConstraintMatrix P .rawConstraint =
      (P.ell : ℝ) • PrintedConstraintMatrix P .normalizedConstraint := by
  apply LinearMap.ext
  intro w
  simp only [PrintedConstraintMatrix, LinearMap.comp_apply,
    PrintedUnitQ_raw_eq_smul_normalized, LinearMap.smul_apply, map_smul]

lemma PrintedConstraintMatrix_raw_isUnit_iff (P : IngrBParams) :
    IsUnit (PrintedConstraintMatrix P .rawConstraint) ↔
      IsUnit (PrintedConstraintMatrix P .normalizedConstraint) := by
  rw [PrintedConstraintMatrix_raw_eq_smul_normalized]
  exact linear_isUnit_smul_iff _ (raw_ell_ne P) _

/-- Both independently defined matrix inverses vanish when the frozen corridor is singular. -/
lemma PrintedConstraintMatrix_inverses_singular (P : IngrBParams)
    (hs : ¬ Function.Bijective (H0 P.Lam P.Q1)) :
    Ring.inverse (PrintedConstraintMatrix P .rawConstraint) = 0 ∧
      Ring.inverse (PrintedConstraintMatrix P .normalizedConstraint) = 0 := by
  have hn : ¬ IsUnit (PrintedConstraintMatrix P .normalizedConstraint) := by
    rw [PrintedConstraintMatrix_normalized]
    exact fun h => hs ((Module.End.isUnit_iff _).mp h)
  exact ⟨Ring.inverse_non_unit _
    (fun h => hn ((PrintedConstraintMatrix_raw_isUnit_iff P).mp h)),
    Ring.inverse_non_unit _ hn⟩

lemma PrintedCorridorLift_raw_eq_smul_normalized (P : IngrBParams) :
    PrintedCorridorLift P .rawConstraint =
      (P.ell : ℝ)⁻¹ • PrintedCorridorLift P .normalizedConstraint := by
  rw [PrintedCorridorLift, PrintedConstraintMatrix_raw_eq_smul_normalized,
    linear_inverse_smul_total _ (raw_ell_ne P)]
  apply LinearMap.ext
  intro c
  simp only [PrintedCorridorLift, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]

/-- The inverse scalar in the lift cancels the scalar in the genuine second jet. -/
lemma PrintedDtilde_raw_eq_normalized (P : IngrBParams) (B : UnitB P) :
    PrintedDtilde P .rawConstraint B = PrintedDtilde P .normalizedConstraint B := by
  unfold PrintedDtilde
  rw [PrintedCorridorLift_raw_eq_smul_normalized,
    PrintedUnitRemainder_raw_eq_smul_normalized]
  simp only [LinearMap.smul_apply, map_smul, smul_smul,
    mul_inv_cancel₀ (raw_ell_ne P), one_smul]

/-- The same cancellation applies to the reconstructed independent-variable map. -/
lemma PrintedUnitC_raw_eq_normalized (P : IngrBParams) :
    PrintedUnitC P .rawConstraint = PrintedUnitC P .normalizedConstraint := by
  unfold PrintedUnitC
  rw [PrintedCorridorLift_raw_eq_smul_normalized, PrintedUnitQ_raw_eq_smul_normalized]
  apply LinearMap.ext
  intro B
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    map_smul, smul_smul, mul_inv_cancel₀ (raw_ell_ne P), one_smul]

lemma PrintedNonlinearTerm_raw_eq_normalized (P : IngrBParams) (r : Reading) (B : UnitB P) :
    PrintedNonlinearTerm P r .rawConstraint B =
      PrintedNonlinearTerm P r .normalizedConstraint B := by
  simp only [PrintedNonlinearTerm, PrintedDtilde_raw_eq_normalized]

lemma PrintedGenForm_raw_eq_normalized (P : IngrBParams) (r : Reading) (B : UnitB P) :
    PrintedGenForm P r .rawConstraint B = PrintedGenForm P r .normalizedConstraint B := by
  simp only [PrintedGenForm, PrintedNonlinearTerm_raw_eq_normalized]

lemma PrintedInstIneq_raw_iff_normalized (P : IngrBParams) (r : Reading) (gamma : ℝ) :
    PrintedInstIneq P r .rawConstraint gamma ↔
      PrintedInstIneq P r .normalizedConstraint gamma := by
  simp only [PrintedInstIneq, PrintedUnitC_raw_eq_normalized, PrintedGenForm_raw_eq_normalized]

/-- Exact unrestricted equivalence of the full comparison predicates. -/
theorem restComparison_raw_iff_normalized (P : IngrBParams) (r : Reading) :
    RestComparison P r .rawConstraint ↔ RestComparison P r .normalizedConstraint := by
  simp only [RestComparison, PrintedNonlinearTerm_raw_eq_normalized,
    PrintedGenForm_raw_eq_normalized, PrintedUnitC_raw_eq_normalized,
    PrintedInstIneq_raw_iff_normalized]

/-- Stronger than the pinned positive goal: no configuration premise is used. -/
theorem restComparison_raw (P : IngrBParams) (r : Reading)
    (hI : InversesExist P r) : RestComparison P r .rawConstraint := by
  exact (restComparison_raw_iff_normalized P r).mpr (restComparison_normalized P r hI)

/-- The primary raw goal is exactly equivalent to the normalized goal. -/
theorem GoalPos1_iff_GoalPos2 : GoalPos1 ↔ GoalPos2 := by
  simp only [GoalPos1, GoalPos2, restComparison_raw_iff_normalized]

/-- Exact pinned raw positive goal, via the verbatim normalized proof. -/
theorem goalPos1_proved : GoalPos1 :=
  GoalPos1_iff_GoalPos2.mpr goalPos2_proved

set_option pp.fullNames true

#print axioms linear_isUnit_smul_iff
#print axioms linear_inverse_smul_total
#print axioms raw_ell_ne
#print axioms PrintedUnitQ_raw_eq_smul_normalized
#print axioms PrintedUnitRemainder_raw_eq_smul_normalized
#print axioms PrintedConstraintMatrix_raw_eq_smul_normalized
#print axioms PrintedConstraintMatrix_raw_isUnit_iff
#print axioms PrintedConstraintMatrix_inverses_singular
#print axioms PrintedCorridorLift_raw_eq_smul_normalized
#print axioms PrintedDtilde_raw_eq_normalized
#print axioms PrintedUnitC_raw_eq_normalized
#print axioms PrintedNonlinearTerm_raw_eq_normalized
#print axioms PrintedGenForm_raw_eq_normalized
#print axioms PrintedInstIneq_raw_iff_normalized
#print axioms restComparison_raw_iff_normalized
#print axioms restComparison_raw
#print axioms GoalPos1_iff_GoalPos2
#print axioms goalPos1_proved

end AdalyFormal.Round3.S3Rest
