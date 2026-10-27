import ZT5A

/-!
S-3 PIN ONLY. No comparison theorem is asserted.

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

/-- Supported primary reading: exact equality, i.e. c(ell,k)=1>0,
for every admissible test field at EVERY depth k>=1. -/
def GoalPos1 : Prop :=
  ∀ P : IngrBParams, AdmissibleConfiguration P → InversesExist P .plainH →
    ∀ B : UnitB P, AdmissibleB P B →
      GenP.firstTerm P B = PrintedFirstTerm P .plainH B

/-- The equivalent source-offered dimensionless-H representation is pinned
separately, not silently substituted for the primary definition. -/
def GoalPos2 : Prop :=
  ∀ P : IngrBParams, AdmissibleConfiguration P → InversesExist P .dimensionlessH →
    ∀ B : UnitB P, AdmissibleB P B →
      GenP.firstTerm P B = PrintedFirstTerm P .dimensionlessH B

/-- Strong negative target. One genuine depth>=2 instance and two actual
admissible fields, with nonzero denominators and unequal ratios. -/
def RatioWitness (r : Reading) : Prop :=
  ∃ P : IngrBParams, AdmissibleConfiguration P ∧ 2 ≤ P.k ∧ InversesExist P r ∧
    ∃ B1 B2 : UnitB P, AdmissibleB P B1 ∧ AdmissibleB P B2 ∧
      B1 ≠ 0 ∧ B2 ≠ 0 ∧
      PrintedFirstTerm P r B1 ≠ 0 ∧ PrintedFirstTerm P r B2 ≠ 0 ∧
      GenP.firstTerm P B1 / PrintedFirstTerm P r B1 ≠
        GenP.firstTerm P B2 / PrintedFirstTerm P r B2

def GoalNeg1 : Prop := RatioWitness .plainH

def GoalNeg2 : Prop := RatioWitness .dimensionlessH

/-- Logical contract check only; NOT a proof of either open goal. -/
theorem GoalNeg1_implies_not_GoalPos1 : GoalNeg1 → ¬ GoalPos1 := by
  rintro ⟨P, hP, _, hI, B1, B2, hB1, hB2, _, _, hz1, hz2, hne⟩ hp
  apply hne
  rw [hp P hP hI B1 hB1, hp P hP hI B2 hB2, div_self hz1, div_self hz2]

theorem GoalNeg2_implies_not_GoalPos2 : GoalNeg2 → ¬ GoalPos2 := by
  rintro ⟨P, hP, _, hI, B1, B2, hB1, hB2, _, _, hz1, hz2, hne⟩ hp
  apply hne
  rw [hp P hP hI B1 hB1, hp P hP hI B2 hB2, div_self hz1, div_self hz2]

/-- A ratio witness excludes even an arbitrary configuration-dependent
scalar, so in particular excludes any scalar depending only on ell and k. -/
theorem RatioWitness_no_scalar (r : Reading) (h : RatioWitness r) :
    ∃ P : IngrBParams, AdmissibleConfiguration P ∧ 2 ≤ P.k ∧ InversesExist P r ∧
      ¬ ∃ c : ℝ, ∀ B : UnitB P, AdmissibleB P B →
        GenP.firstTerm P B = c * PrintedFirstTerm P r B := by
  obtain ⟨P, hP, hk, hI, B1, B2, hB1, hB2, _, _, hz1, hz2, hne⟩ := h
  refine ⟨P, hP, hk, hI, ?_⟩
  rintro ⟨c, hc⟩
  apply hne
  rw [hc B1 hB1, hc B2 hB2, mul_div_cancel_right₀ _ hz1, mul_div_cancel_right₀ _ hz2]

#check PrintedFirstTerm
#check AdmissibleConfiguration
#check AdmissibleB
#check InversesExist
#check GoalPos1
#check GoalNeg1
#check GoalPos2
#check GoalNeg2

end AdalyFormal.Round2.S3Pin

#print axioms AdalyFormal.Round2.S3Pin.PrintedCjBil
#print axioms AdalyFormal.Round2.S3Pin.PrintedCBil
#print axioms AdalyFormal.Round2.S3Pin.PrintedKBil
#print axioms AdalyFormal.Round2.S3Pin.PrintedG1inv
#print axioms AdalyFormal.Round2.S3Pin.PrintedFirstTerm
#print axioms AdalyFormal.Round2.S3Pin.AdmissibleConfiguration
#print axioms AdalyFormal.Round2.S3Pin.AdmissibleB
#print axioms AdalyFormal.Round2.S3Pin.InversesExist
#print axioms AdalyFormal.Round2.S3Pin.GoalPos1
#print axioms AdalyFormal.Round2.S3Pin.GoalNeg1
#print axioms AdalyFormal.Round2.S3Pin.GoalPos2
#print axioms AdalyFormal.Round2.S3Pin.GoalNeg2
#print axioms AdalyFormal.Round2.S3Pin.GoalNeg1_implies_not_GoalPos1
#print axioms AdalyFormal.Round2.S3Pin.GoalNeg2_implies_not_GoalPos2
#print axioms AdalyFormal.Round2.S3Pin.RatioWitness_no_scalar

/-! Round 1 refutation attempt. The pin above is copied verbatim.
The exact coefficient probe found no split for the linked conventions.
The following results eliminate that proposed source of a counterexample;
they do not assert either pinned negative or positive goal. -/
namespace AdalyFormal.Round2.S3Pin

open scoped RealInnerProductSpace
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneG
open Classical

theorem mesh_ne_zero (P : IngrBParams) : mesh P ≠ 0 :=
  ne_of_gt P.eta_pos

theorem spacing_ne_zero (P : IngrBParams) (j : ℕ) : spacing P j ≠ 0 := by
  unfold spacing
  have he : (P.ell : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt P.hell)
  exact mul_ne_zero (pow_ne_zero j he) (mesh_ne_zero P)

/-- The linked dimensionless C, followed by the matching H input scale,
is the plain C on the ACTUAL jets, at every level and every background. -/
theorem linked_C_cancel (P : IngrBParams) (A B : E P) :
    diagW P.G (fun p => (spacing P p.1)⁻¹)
      (PrintedCBil P .dimensionlessH A B) = PrintedCBil P .plainH A B := by
  apply PiLp.ext
  intro p
  simp only [diagW, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, WithLp.ofLp_toLp, PrintedCBil, LinearMap.mk₂_apply,
    COutputScale, CInputScale, one_smul]
  simp [map_smul, LinearMap.smul_apply, PiLp.smul_apply, smul_smul, spacing_ne_zero]

theorem linked_HC_eq (P : IngrBParams) (A B : E P) :
    PrintedHFor P .dimensionlessH (PrintedCBil P .dimensionlessH A B) =
      PrintedHFor P .plainH (PrintedCBil P .plainH A B) := by
  change PrintedH P (diagW P.G (fun p => (spacing P p.1)⁻¹)
      (PrintedCBil P .dimensionlessH A B)) = PrintedH P (PrintedCBil P .plainH A B)
  rw [linked_C_cancel]

theorem linked_KBil_eq (P : IngrBParams) :
    PrintedKBil P .dimensionlessH = PrintedKBil P .plainH := by
  ext A B
  simp only [PrintedKBil, LinearMap.mk₂_apply, linked_HC_eq]

theorem linked_G1inv_eq (P : IngrBParams) :
    PrintedG1inv P .dimensionlessH = PrintedG1inv P .plainH := by
  rw [PrintedG1inv, linked_KBil_eq, PrintedG1inv]

theorem linked_N_eq (P : IngrBParams) :
    PrintedN P .dimensionlessH = PrintedN P .plainH := by
  simp only [PrintedN, PrintedG1, linked_G1inv_eq]

theorem linked_firstTerm_eq (P : IngrBParams) (B : UnitB P) :
    PrintedFirstTerm P .dimensionlessH B = PrintedFirstTerm P .plainH B := by
  simp only [PrintedFirstTerm, linked_N_eq]

theorem linked_inverses_iff (P : IngrBParams) :
    InversesExist P .dimensionlessH ↔ InversesExist P .plainH := by
  simp only [InversesExist, linked_G1inv_eq, linked_N_eq]

/-- Furthest reduction of the actual negative targets. No witness exists
in this file; equivalence neither proves nor refutes either proposition. -/
theorem negative_goals_equivalent : GoalNeg1 ↔ GoalNeg2 := by
  simp only [GoalNeg1, GoalNeg2, RatioWitness, linked_inverses_iff,
    linked_firstTerm_eq]

/-- All-depth replacement for the rejected power-count route. This uses
actual C2rawB/D2B, not arbitrary second jets. It does not identify PrintedW
with the frozen Wop or compare either inverse chain. -/
theorem plain_C_eq_mesh_C2full (P : IngrBParams) (A : E P) :
    PrintedC P .plainH A =
      mesh P • C2fullOf P.G P.U (PrintedW P (iE P.G A)) := by
  apply PiLp.ext
  intro p
  have he : (P.ell : ℝ) ^ (p.1 : ℕ) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Nat.ne_of_gt P.hell))
  simp only [PrintedC, PrintedCBil, LinearMap.mk₂_apply, COutputScale,
    CInputScale, one_smul, PrintedCjBil, LinearMap.compl₁₂_apply,
    LinearMap.smul_apply, map_smul, PiLp.smul_apply,
    C2fullOf, C2rawB, WithLp.ofLp_toLp, smul_smul]
  congr 1
  change ((P.ell : ℝ) ^ (p.1 : ℕ) * mesh P) *
      ((((P.ell : ℝ) ^ (p.1 : ℕ))⁻¹) *
        ((((P.ell : ℝ) ^ (p.1 : ℕ))⁻¹) * (1 / 2))) =
    mesh P * ((((P.ell : ℝ) ^ (p.1 : ℕ))⁻¹) * (1 / 2))
  field_simp [he]

end AdalyFormal.Round2.S3Pin

#print axioms AdalyFormal.Round2.S3Pin.mesh_ne_zero
#print axioms AdalyFormal.Round2.S3Pin.spacing_ne_zero
#print axioms AdalyFormal.Round2.S3Pin.linked_C_cancel
#print axioms AdalyFormal.Round2.S3Pin.linked_HC_eq
#print axioms AdalyFormal.Round2.S3Pin.linked_KBil_eq
#print axioms AdalyFormal.Round2.S3Pin.linked_G1inv_eq
#print axioms AdalyFormal.Round2.S3Pin.linked_N_eq
#print axioms AdalyFormal.Round2.S3Pin.linked_firstTerm_eq
#print axioms AdalyFormal.Round2.S3Pin.linked_inverses_iff
#print axioms AdalyFormal.Round2.S3Pin.negative_goals_equivalent
#print axioms AdalyFormal.Round2.S3Pin.plain_C_eq_mesh_C2full

-- Dependency audit for every remaining local definition/helper in the copied pin.
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
#print axioms AdalyFormal.Round2.S3Pin.CInputScale
#print axioms AdalyFormal.Round2.S3Pin.COutputScale
#print axioms AdalyFormal.Round2.S3Pin.PrintedC
#print axioms AdalyFormal.Round2.S3Pin.PrintedHFor
#print axioms AdalyFormal.Round2.S3Pin.PrintedG1
#print axioms AdalyFormal.Round2.S3Pin.PrintedN
#print axioms AdalyFormal.Round2.S3Pin.PrintedB
#print axioms AdalyFormal.Round2.S3Pin.RatioWitness
