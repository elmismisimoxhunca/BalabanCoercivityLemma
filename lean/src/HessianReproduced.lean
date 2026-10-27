import SmallBackground
set_option autoImplicit false
namespace HConstruction.SmallNF.Reproduced
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap curlValueCovariant suTwo curlCovariantLM)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
variable {L : PeriodicLatticeExtent}
noncomputable def bondMatLM (b : Bond L) :
    (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Submodule.subtype suTwo) ∘ₗ (LinearMap.proj b : (Bond L → SuTwo) →ₗ[ℝ] SuTwo)

theorem bondMatLM_apply (b : Bond L) (A : Bond L → SuTwo) :
    bondMatLM b A = ((A b : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := rfl

/-- `A ↦ ↑(R(V)(A b))` — the transported bond read appearing in `AprimeYZ`/`AprimeZW`. -/
noncomputable def bondMatRLM (V : Matrix.specialUnitaryGroup (Fin 2) ℂ) (b : Bond L) :
    (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Submodule.subtype suTwo) ∘ₗ (RMap V) ∘ₗ (LinearMap.proj b : (Bond L → SuTwo) →ₗ[ℝ] SuTwo)

theorem bondMatRLM_apply (V : Matrix.specialUnitaryGroup (Fin 2) ℂ) (b : Bond L)
    (A : Bond L → SuTwo) :
    bondMatRLM V b A = ((RMap V (A b) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := rfl

/-- `A ↦ ↑((D_U A)(p))` — the covariant curl at one plaquette, into the matrices.
`curlCovariantLM` is REUSED from `CovariantOperators.lean` (LAW-19), so the linearity of the curl is
not re-proved here. -/
noncomputable def curlMatLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Submodule.subtype suTwo) ∘ₗ
    (LinearMap.proj p : (PeriodicLatticePlaquette L → SuTwo) →ₗ[ℝ] SuTwo) ∘ₗ
      (curlCovariantLM U)

theorem curlMatLM_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    curlMatLM U p A = ((curlValueCovariant U A p : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := rfl

/-- `M ↦ Complex.I • M`, as an ℝ-linear map. This is the `φ`-transport factor
`DeltaPrime.lean` §11 applies at the MATRIX level (because `i·(anti-Hermitian)` leaves `SuTwo`);
it is ℝ-linear, not ℂ-linear-in-disguise, which is why it composes with the maps above. -/
noncomputable def smulILM : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun M := Complex.I • M
  map_add' _ _ := smul_add _ _ _
  map_smul' c M := smul_comm (Complex.I) c M

theorem smulILM_apply (M : Matrix (Fin 2) (Fin 2) ℂ) : smulILM M = Complex.I • M := rfl

/-- **THE ELEMENTARY BILINEAR ATOM** `(A,B) ↦ Re tr(f A · g B · M)`, for a FIXED matrix `M` and two
bundled linear reads `f`, `g`. Every term of `Δ′`'s bilinear form is one of these or the `flip` of
one, so bilinearity is established once here and never again. -/
noncomputable def traceForm (M : Matrix (Fin 2) (Fin 2) ℂ)
    (f g : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun A B => (Matrix.trace (f A * g B * M)).re)
    (fun _ _ _ => by simp [Matrix.add_mul])
    (fun _ _ _ => by
      simp only [map_smul, Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul])
    (fun _ _ _ => by simp [Matrix.mul_add, Matrix.add_mul])
    (fun _ _ _ => by
      simp only [map_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re,
        smul_eq_mul])

theorem traceForm_apply (M : Matrix (Fin 2) (Fin 2) ℂ)
    (f g : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) (A B : Bond L → SuTwo) :
    traceForm M f g A B = (Matrix.trace (f A * g B * M)).re := rfl

#print axioms bondMatLM
#print axioms bondMatLM_apply
#print axioms bondMatRLM
#print axioms bondMatRLM_apply
#print axioms curlMatLM
#print axioms curlMatLM_apply
#print axioms smulILM
#print axioms smulILM_apply
#print axioms traceForm
#print axioms traceForm_apply

/-! ## §2 — THE FOUR `A′` COMPONENTS, PINNED TO `DeltaPrime`'s OWN DEFINITIONS BY `rfl`

Indices follow `DeltaPrime.lean`'s `≺`-order verbatim: `a₁ = A′(z,w)` (`AprimeZW`),
`a₂ = A′(w,x)` (`AprimeWX`), `a₃ = A′(x,y)` (`AprimeXY`), `a₄ = A′(y,z)` (`AprimeYZ`). The two
negations are the source's own antisymmetry sign flips (`A(z,w) = -A(w,z)`, `A(w,x) = -A(x,w)`), not
a convention introduced here.
-/

/-- `a₁ = ↑(A′(z,w)) = -↑(R(U(x,ν))·A(shift_ν x, μ))`. -/
noncomputable def a1LM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  -(bondMatRLM (U (p.1, p.2.1.2)) (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))

/-- `a₂ = ↑(A′(w,x)) = -↑(A(x,ν))`. -/
noncomputable def a2LM (p : PeriodicLatticePlaquette L) :
    (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  -(bondMatLM (p.1, p.2.1.2))

/-- `a₃ = ↑(A′(x,y)) = ↑(A(x,μ))`. -/
noncomputable def a3LM (p : PeriodicLatticePlaquette L) :
    (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  bondMatLM (p.1, p.2.1.1)

/-- `a₄ = ↑(A′(y,z)) = ↑(R(U(x,μ))·A(shift_μ x, ν))`. -/
noncomputable def a4LM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  bondMatRLM (U (p.1, p.2.1.1)) (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)

theorem a1LM_apply (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    a1LM U p A = ((AprimeZW U A p : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := rfl

theorem a2LM_apply (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    a2LM p A = ((AprimeWX A p : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := rfl

theorem a3LM_apply (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    a3LM p A = ((AprimeXY A p : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := rfl

theorem a4LM_apply (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    a4LM U p A = ((AprimeYZ U A p : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := rfl

/-- The `φ`-transported components `bᵢ = I • aᵢ`, exactly `commutatorMatrixSumTransported`'s own
`a1`-`a4` `let`-bindings. -/
noncomputable def b1LM (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  smulILM ∘ₗ a1LM U p

noncomputable def b2LM (p : PeriodicLatticePlaquette L) :
    (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ := smulILM ∘ₗ a2LM (L := L) p

noncomputable def b3LM (p : PeriodicLatticePlaquette L) :
    (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ := smulILM ∘ₗ a3LM (L := L) p

noncomputable def b4LM (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  smulILM ∘ₗ a4LM U p

#print axioms a1LM
#print axioms a2LM
#print axioms a3LM
#print axioms a4LM
#print axioms a1LM_apply
#print axioms a2LM_apply
#print axioms a3LM_apply
#print axioms a4LM_apply
#print axioms b1LM
#print axioms b2LM
#print axioms b3LM
#print axioms b4LM

/-! ## §3 — THE PER-PLAQUETTE BILINEAR FORM

`pairBil f g` is ONE of `commutatorMatrixSumTransported`'s six brackets, traced against
`imHolonomy U p`, with the two matrix orderings kept separate so that each is bilinear in `(A,B)`:
the source bracket `aᵢaⱼ - aⱼaᵢ` becomes `f(A)g(B) - g(B)f(A)`, and the second of those is a `flip`
because its `A`-dependent factor sits on the RIGHT. The formula's own leading `I` (present in
CMP99b (3.10) itself, NOT part of the `φ`-transport) is the extra `smulILM` in front of the first
argument of each `traceForm`; `Matrix.smul_mul` is what lets it be moved there, and that move is
discharged inside `secondBilPlaq_diag`, not assumed.
-/

/-- One of the six brackets, traced against `Im U(∂p)`. -/
noncomputable def pairBil
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L)
    (f g : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  traceForm (imHolonomy U p) (smulILM ∘ₗ f) g
    - (traceForm (imHolonomy U p) (smulILM ∘ₗ g) f).flip

/-- CMP99b (3.10)'s FIRST `Δ′` term, as a bilinear form. **BILLING QUALIFIED (S75, conviction
banner (1)+(3)):** this is the `η = 1` specialization of (3.10) — the printed formula carries the
weight `η^d η^{-2}` and this type has no `η` binder — and it uses RAW `Matrix.trace`, i.e. it is
`2 ×` the source-normalized term (source p.392: `tr 1 = 1`). The source-normalized object is §N's
`deltaPrimeBilNormalized`. -/
noncomputable def firstBilPlaq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  traceForm (reHolonomy U p - 1) (smulILM ∘ₗ curlMatLM U p) (smulILM ∘ₗ curlMatLM U p)

/-- CMP99b (3.10)'s SECOND `Δ′` term, as a bilinear form: all SIX pairs `i<j` of
`{1,2,3,4}` — `(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)` — in `DeltaPrime`'s own order.
**BILLING QUALIFIED exactly as `firstBilPlaq` above:** `η = 1` specialization, RAW trace (`2 ×`
source-normalized). -/
noncomputable def secondBilPlaq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  pairBil U p (b1LM U p) (b2LM p) + pairBil U p (b1LM U p) (b3LM p)
    + pairBil U p (b1LM U p) (b4LM U p) + pairBil U p (b2LM p) (b3LM p)
    + pairBil U p (b2LM p) (b4LM U p) + pairBil U p (b3LM p) (b4LM U p)

/-- The full per-plaquette bilinear summand of `Δ′`. -/
noncomputable def bilPlaq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  firstBilPlaq U p + secondBilPlaq U p

theorem pairBil_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L)
    (f g : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) (A B : Bond L → SuTwo) :
    pairBil U p f g A B
      = (Matrix.trace (smulILM (f A) * g B * imHolonomy U p)).re
        - (Matrix.trace (smulILM (g B) * f A * imHolonomy U p)).re := rfl

theorem firstBilPlaq_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    firstBilPlaq U p A B
      = (Matrix.trace (smulILM (curlMatLM U p A) * smulILM (curlMatLM U p B)
          * (reHolonomy U p - 1))).re := rfl

theorem secondBilPlaq_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    secondBilPlaq U p A B
      = pairBil U p (b1LM U p) (b2LM p) A B + pairBil U p (b1LM U p) (b3LM p) A B
        + pairBil U p (b1LM U p) (b4LM U p) A B + pairBil U p (b2LM p) (b3LM p) A B
        + pairBil U p (b2LM p) (b4LM U p) A B + pairBil U p (b3LM p) (b4LM U p) A B := rfl

theorem bilPlaq_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    bilPlaq U p A B = firstBilPlaq U p A B + secondBilPlaq U p A B := rfl

/-- **THE ATOM COUNT, KERNEL-CHECKED** (§S class 3: the docstring's "13 atoms = 1 + 6 brackets × 2
orderings" is asserted here as an identity, not only in prose). The right-hand side is written out
atom by atom: one first-term trace, then the six brackets `(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)`, each
as a DIFFERENCE of its two matrix orderings. -/
theorem bilPlaq_atoms
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    bilPlaq U p A B
      = (Matrix.trace (smulILM (curlMatLM U p A) * smulILM (curlMatLM U p B)
            * (reHolonomy U p - 1))).re
        + ((Matrix.trace (smulILM (b1LM U p A) * b2LM p B * imHolonomy U p)).re
            - (Matrix.trace (smulILM (b2LM p B) * b1LM U p A * imHolonomy U p)).re)
        + ((Matrix.trace (smulILM (b1LM U p A) * b3LM p B * imHolonomy U p)).re
            - (Matrix.trace (smulILM (b3LM p B) * b1LM U p A * imHolonomy U p)).re)
        + ((Matrix.trace (smulILM (b1LM U p A) * b4LM U p B * imHolonomy U p)).re
            - (Matrix.trace (smulILM (b4LM U p B) * b1LM U p A * imHolonomy U p)).re)
        + ((Matrix.trace (smulILM (b2LM p A) * b3LM p B * imHolonomy U p)).re
            - (Matrix.trace (smulILM (b3LM p B) * b2LM p A * imHolonomy U p)).re)
        + ((Matrix.trace (smulILM (b2LM p A) * b4LM U p B * imHolonomy U p)).re
            - (Matrix.trace (smulILM (b4LM U p B) * b2LM p A * imHolonomy U p)).re)
        + ((Matrix.trace (smulILM (b3LM p A) * b4LM U p B * imHolonomy U p)).re
            - (Matrix.trace (smulILM (b4LM U p B) * b3LM p A * imHolonomy U p)).re) := by
  rw [bilPlaq_apply, firstBilPlaq_apply, secondBilPlaq_apply]
  simp only [pairBil_apply]
  ring

/-- **DIAGONAL, first term** — definitional. -/
theorem firstBilPlaq_diag
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    firstBilPlaq U p A A = deltaPrimeFirstTermTransported U A p := rfl

/-- **DIAGONAL, commutator term.** The only non-definitional step in the whole construction: the
source writes ONE trace of `I • (Σ of six brackets) · Im U(∂p)`, this module writes TWELVE traces,
and they agree by `Matrix.smul_mul`/`Matrix.add_mul`/`Matrix.sub_mul` + additivity of `trace` and of
`Complex.re`. Nothing is dropped and nothing is added: the twelve atoms are exactly the six brackets'
two orderings. -/
theorem secondBilPlaq_diag
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    secondBilPlaq U p A A = deltaPrimeSecondTermTransported U A p := by
  show (traceForm (imHolonomy U p) (smulILM ∘ₗ b1LM U p) (b2LM p) A A
      - traceForm (imHolonomy U p) (smulILM ∘ₗ b2LM p) (b1LM U p) A A)
    + (traceForm (imHolonomy U p) (smulILM ∘ₗ b1LM U p) (b3LM p) A A
      - traceForm (imHolonomy U p) (smulILM ∘ₗ b3LM p) (b1LM U p) A A)
    + (traceForm (imHolonomy U p) (smulILM ∘ₗ b1LM U p) (b4LM U p) A A
      - traceForm (imHolonomy U p) (smulILM ∘ₗ b4LM U p) (b1LM U p) A A)
    + (traceForm (imHolonomy U p) (smulILM ∘ₗ b2LM p) (b3LM p) A A
      - traceForm (imHolonomy U p) (smulILM ∘ₗ b3LM p) (b2LM p) A A)
    + (traceForm (imHolonomy U p) (smulILM ∘ₗ b2LM p) (b4LM U p) A A
      - traceForm (imHolonomy U p) (smulILM ∘ₗ b4LM U p) (b2LM p) A A)
    + (traceForm (imHolonomy U p) (smulILM ∘ₗ b3LM p) (b4LM U p) A A
      - traceForm (imHolonomy U p) (smulILM ∘ₗ b4LM U p) (b3LM p) A A)
    = _
  simp only [traceForm_apply, LinearMap.comp_apply, deltaPrimeSecondTermTransported,
    commutatorMatrixSumTransported]
  simp only [b1LM, b2LM, b3LM, b4LM, a1LM, a2LM, a3LM, a4LM, bondMatLM, bondMatRLM,
    smulILM, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, LinearMap.neg_apply,
    LinearMap.proj_apply, Submodule.coe_subtype, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.sub_mul, Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg,
    Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_neg,
    smul_eq_mul, Matrix.mul_assoc,
    AprimeXY, AprimeYZ, AprimeZW, AprimeWX, NegMemClass.coe_neg]
  simp only [← Complex.sub_re, ← Complex.add_re]
  congr 1
  ring

/-- **DIAGONAL, per plaquette.** -/
theorem bilPlaq_diag
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    bilPlaq U p A A
      = deltaPrimeFirstTermTransported U A p + deltaPrimeSecondTermTransported U A p := by
  show firstBilPlaq U p A A + secondBilPlaq U p A A = _
  rw [firstBilPlaq_diag, secondBilPlaq_diag]

#print axioms bilPlaq_atoms
#print axioms pairBil_apply
#print axioms firstBilPlaq_apply
#print axioms secondBilPlaq_apply
#print axioms bilPlaq_apply
#print axioms pairBil
#print axioms firstBilPlaq
#print axioms secondBilPlaq
#print axioms bilPlaq
#print axioms firstBilPlaq_diag
#print axioms secondBilPlaq_diag
#print axioms bilPlaq_diag

/-! ## §4 — THE LATTICE SUM, AND THE SYMMETRIZATION

`deltaPrimeBilRaw` is the plaquette sum. It is bilinear (a finite sum in the module of bilinear
maps) and its DIAGONAL is `deltaPrimeQuadFormTransported`, but it is **not symmetric** — §9 proves
that with an explicit pair of fields, so the symmetrization below is demonstrably load-bearing
rather than defensive.
-/

/-- `Δ′`'s bilinear form, before symmetrization. -/
noncomputable def deltaPrimeBilRaw
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  ∑ p : PeriodicLatticePlaquette L, bilPlaq U p

theorem deltaPrimeBilRaw_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A B : Bond L → SuTwo) :
    deltaPrimeBilRaw U A B = ∑ p : PeriodicLatticePlaquette L, bilPlaq U p A B := by
  show (∑ p : PeriodicLatticePlaquette L, bilPlaq U p) A B = _
  rw [LinearMap.sum_apply, LinearMap.sum_apply]

/-- **THE DIAGONAL OF THE RAW FORM IS `Δ′`.** -/
theorem deltaPrimeBilRaw_diag
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    deltaPrimeBilRaw U A A = deltaPrimeQuadFormTransported U A := by
  rw [deltaPrimeBilRaw_apply, deltaPrimeQuadFormTransported]
  exact Finset.sum_congr rfl (fun p _ => bilPlaq_diag U p A)

/-- **`Δ′`'s SYMMETRIC bilinear form** — the deliverable of §1-§4. -/
noncomputable def deltaPrimeBil
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  (1 / 2 : ℝ) • (deltaPrimeBilRaw U + (deltaPrimeBilRaw U).flip)

theorem deltaPrimeBil_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A B : Bond L → SuTwo) :
    deltaPrimeBil U A B
      = (1 / 2 : ℝ) * (deltaPrimeBilRaw U A B + deltaPrimeBilRaw U B A) := rfl

/-- **SYMMETRY — proved, not assumed** (§0b). -/
theorem deltaPrimeBil_symm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A B : Bond L → SuTwo) :
    deltaPrimeBil U A B = deltaPrimeBil U B A := by
  rw [deltaPrimeBil_apply, deltaPrimeBil_apply, add_comm]

/-- **THE DIAGONAL SURVIVES SYMMETRIZATION**: `½(Q + Q) = Q`. -/
theorem deltaPrimeBil_diag
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    deltaPrimeBil U A A = deltaPrimeQuadFormTransported U A := by
  rw [deltaPrimeBil_apply, deltaPrimeBilRaw_diag]
  ring

#print axioms deltaPrimeBilRaw
#print axioms deltaPrimeBilRaw_apply
#print axioms deltaPrimeBilRaw_diag
#print axioms deltaPrimeBil
#print axioms deltaPrimeBil_apply
#print axioms deltaPrimeBil_symm
#print axioms deltaPrimeBil_diag
end HConstruction.SmallNF.Reproduced
