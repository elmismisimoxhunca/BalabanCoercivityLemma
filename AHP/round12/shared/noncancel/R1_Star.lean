import DrEquiv
/-! Finite exterior-star estimates and a whole-kernel trace criterion.
No application to a physical crossing is asserted by this file. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.Round12.Noncancel.Star
open scoped RealInnerProductSpace

/-- Two ordered charged contributions to one plaquette. -/
def pairForm (c s : ℝ) (y z : ℂ) : ℝ :=
  c * Complex.normSq (y + z) + 2 * s * (star y * z).im

/-- Three ordered charged contributions; the fourth (exterior) field is zero. -/
def tripleForm (c s : ℝ) (x y z : ℂ) : ℝ :=
  c * Complex.normSq (x + y + z) +
    2 * s * ((star x * y).im + (star x * z).im + (star y * z).im)

theorem tripleForm_zero_left (c s : ℝ) (y z : ℂ) :
    tripleForm c s 0 y z = pairForm c s y z := by
  simp [tripleForm, pairForm]

theorem tripleForm_zero_middle (c s : ℝ) (x z : ℂ) :
    tripleForm c s x 0 z = pairForm c s x z := by
  simp [tripleForm, pairForm]

theorem tripleForm_zero_right (c s : ℝ) (x y : ℂ) :
    tripleForm c s x y 0 = pairForm c s x y := by
  simp [tripleForm, pairForm]

/-- Exact completion of the square, with the two leaf mass terms retained. -/
theorem pair_completion (c s : ℝ) (hcs : c^2 + s^2 = 1) (y z : ℂ) :
    Complex.normSq y + Complex.normSq z + pairForm c s y z =
      c * (Complex.normSq y + Complex.normSq z) +
        Complex.normSq (y + ((c : ℂ) - (s : ℂ) * Complex.I) * z) := by
  simp only [pairForm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg z.re, sq_nonneg z.im,
    congrArg (fun a : ℝ => a * z.re^2) hcs,
    congrArg (fun a : ℝ => a * z.im^2) hcs]

theorem pair_mass_lower (c s : ℝ) (hcs : c^2 + s^2 = 1) (y z : ℂ) :
    c * (Complex.normSq y + Complex.normSq z) ≤
      Complex.normSq y + Complex.normSq z + pairForm c s y z := by
  rw [pair_completion c s hcs]
  exact le_add_of_nonneg_right (Complex.normSq_nonneg _)

/-- Number of arms is arbitrary. Only a positive base form and disjoint leaf masses enter. -/
theorem star_mass_lower {ι : Type*} [Fintype ι]
    (c s rest : ℝ) (hc : c ≤ 1) (hr : 0 ≤ rest) (hcs : c^2 + s^2 = 1)
    (y z : ι → ℂ) :
    c * (rest + ∑ i, (Complex.normSq (y i) + Complex.normSq (z i))) ≤
      rest + ∑ i, (Complex.normSq (y i) + Complex.normSq (z i) +
        pairForm c s (y i) (z i)) := by
  have h := Finset.sum_le_sum (fun (i : ι) (_ : i ∈ Finset.univ) =>
    pair_mass_lower c s hcs (y i) (z i))
  rw [← Finset.mul_sum] at h
  have hh : c * rest ≤ rest := by nlinarith
  nlinarith

section Kernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A single complex trace is injective on the whole kernel if its zero fiber is positive. -/
theorem trace_ne_zero (A : E →ₗ[ℝ] E) (l : E →ₗ[ℝ] ℂ)
    (hp : ∀ u, l u = 0 → u ≠ 0 → 0 < ⟪u, A u⟫)
    {u : E} (hu : A u = 0) (hne : u ≠ 0) : l u ≠ 0 := by
  intro hl
  have h := hp u hl hne
  simp only [hu, inner_zero_right, lt_self_iff_false] at h

theorem trace_kernel_injective (A : E →ₗ[ℝ] E) (l : E →ₗ[ℝ] ℂ)
    (hp : ∀ u, l u = 0 → u ≠ 0 → 0 < ⟪u, A u⟫) :
    Function.Injective (fun u : A.ker => l u) := by
  intro u v huv
  change l (u : E) = l (v : E) at huv
  apply Subtype.ext
  by_contra h
  have hne : (u : E) - v ≠ 0 := sub_ne_zero.mpr h
  have ha : A ((u : E) - v) = 0 := by
    rw [map_sub, u.property, v.property, sub_self]
  exact trace_ne_zero A l hp ha hne (by rw [map_sub, huv, sub_self])

/-- U(1) plus one injective trace gives the entire charged line; no character screen. -/
theorem kernel_line_of_trace (A J : E →ₗ[ℝ] E) (l : E →ₗ[ℝ] ℂ)
    (hcomm : ∀ u, A (J u) = J (A u))
    (htrace : ∀ u, l (J u) = Complex.I * l u)
    (hp : ∀ u, l u = 0 → u ≠ 0 → 0 < ⟪u, A u⟫)
    (u₀ : E) (hu₀ : A u₀ = 0) (hne : u₀ ≠ 0) :
    J (J u₀) = -u₀ ∧
      ∀ u, A u = 0 → u ∈ Submodule.span ℝ {u₀, J u₀} := by
  have hzero (v : E) (ha : A v = 0) (hl : l v = 0) : v = 0 := by
    by_contra hn
    exact trace_ne_zero A l hp ha hn hl
  have hJu : A (J u₀) = 0 := by rw [hcomm, hu₀, map_zero]
  have hJl : A (J (J u₀)) = 0 := by rw [hcomm, hJu, map_zero]
  have ht : l u₀ ≠ 0 := trace_ne_zero A l hp hu₀ hne
  constructor
  · apply eq_neg_of_add_eq_zero_left
    apply hzero
    · rw [map_add, hJl, hu₀, add_zero]
    · rw [map_add, htrace, htrace, ← mul_assoc, Complex.I_mul_I, neg_one_mul,
        neg_add_cancel]
  · intro u hu
    let a : ℂ := l u / l u₀
    have hac : a * l u₀ = l u := div_mul_cancel₀ _ ht
    have hlin : l (a.re • u₀ + a.im • J u₀) = l u := by
      rw [map_add, map_smul, map_smul, htrace]
      change (a.re : ℂ) * l u₀ + (a.im : ℂ) * (Complex.I * l u₀) = l u
      calc
        _ = ((a.re : ℂ) + (a.im : ℂ) * Complex.I) * l u₀ := by ring
        _ = a * l u₀ := by rw [Complex.re_add_im]
        _ = l u := hac
    have heq : u = a.re • u₀ + a.im • J u₀ := by
      apply sub_eq_zero.mp
      apply hzero
      · rw [map_sub, hu, map_add, map_smul, map_smul, hu₀, hJu,
          smul_zero, smul_zero, add_zero, sub_zero]
      · rw [map_sub, hlin, sub_self]
    rw [heq]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-- The precise local-star input sufficient for the positivity clause above. -/
theorem positive_on_trace_zero {ι : Type*} [Fintype ι]
    (A : E →ₗ[ℝ] E) (l : E →ₗ[ℝ] ℂ) (rest : E → ℝ)
    (y z : E → ι → ℂ) (c s : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hcs : c^2 + s^2 = 1) (hr : ∀ u, 0 ≤ rest u)
    (hbase : ∀ u, u ≠ 0 →
      0 < rest u + ∑ i, (Complex.normSq (y u i) + Complex.normSq (z u i)))
    (hform : ∀ u, l u = 0 → ⟪u, A u⟫ =
      rest u + ∑ i, (Complex.normSq (y u i) + Complex.normSq (z u i) +
        pairForm c s (y u i) (z u i))) :
    ∀ u, l u = 0 → u ≠ 0 → 0 < ⟪u, A u⟫ := by
  intro u hl hn
  rw [hform u hl]
  exact lt_of_lt_of_le (mul_pos hc (hbase u hn))
    (star_mass_lower c s (rest u) hc1 (hr u) hcs (y u) (z u))
end Kernel

/-- Exact rational test energy on the proposed four-arm boundary star at pi/2.
The 16 comes from four leaf masses and twelve untwisted plaquettes.
The last two terms add one tangential boundary bond. Physical identification is separate. -/
def starTrialEnergy (a b : ℝ) : ℝ := 1 + 16*a^2 - 8*a - 2*b + 4*b^2

theorem starTrial_null : starTrialEnergy (1/4) 0 = 0 := by
  norm_num [starTrialEnergy]

theorem starTrial_negative : starTrialEnergy (1/4) (1/4) = -1/4 := by
  norm_num [starTrialEnergy]

#print axioms pairForm
#print axioms tripleForm
#print axioms tripleForm_zero_left
#print axioms tripleForm_zero_middle
#print axioms tripleForm_zero_right
#print axioms pair_completion
#print axioms pair_mass_lower
#print axioms star_mass_lower
#print axioms trace_ne_zero
#print axioms trace_kernel_injective
#print axioms kernel_line_of_trace
#print axioms positive_on_trace_zero
#print axioms starTrialEnergy
#print axioms starTrial_null
#print axioms starTrial_negative
end AdalyFormal.Round12.Noncancel.Star

/-! Exact frozen per-plaquette formula. These hypotheses specify transported
bond values and holonomy entries, not a replacement operator. -/
namespace AdalyFormal.Round12.Noncancel.Plaquette
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Round12.Noncancel.Star

/-- Matrix of a charged Lie-algebra element, with its actual upper-right coordinate. -/
def chargedMat (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, z; -star z, 0]
def realHol (c : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := (c : ℂ) • 1
def imagHol (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![(s : ℂ), 0; 0, -(s : ℂ)]

theorem chargedMat_add (y z : ℂ) : chargedMat (y+z) = chargedMat y + chargedMat z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chargedMat, add_comm]

theorem chargedMat_zero : chargedMat 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chargedMat]

theorem charged_inner (X : SuTwo) (z : ℂ)
    (hX : (X : Matrix (Fin 2) (Fin 2) ℂ) = chargedMat z) :
    ⟪X, X⟫ = Complex.normSq z := by
  change hsInner X X = _
  rw [hsInner_entries, hX]
  simp [chargedMat, Complex.normSq_apply, Complex.mul_re]
  ring

theorem first_atom (c : ℝ) (z : ℂ) :
    (Matrix.trace (smulILM (chargedMat z) * smulILM (chargedMat z) *
      (realHol c - 1))).re = 2*(c-1)*Complex.normSq z := by
  simp [chargedMat, realHol, smulILM_apply, Matrix.mul_apply, Matrix.trace,
    Matrix.diag, Fin.sum_univ_two, Complex.normSq_apply]
  ring

theorem comm_atom (s : ℝ) (y z : ℂ) :
    (Matrix.trace (smulILM (smulILM (chargedMat y)) * smulILM (chargedMat z) *
      imagHol s)).re -
    (Matrix.trace (smulILM (smulILM (chargedMat z)) * smulILM (chargedMat y) *
      imagHol s)).re = 4*s*(star y*z).im := by
  simp [chargedMat, imagHol, smulILM_apply, Matrix.mul_apply, Matrix.trace,
    Matrix.diag, Fin.sum_univ_two]
  ring

variable {L : PeriodicLatticeExtent}

theorem curl_atoms (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    curlMatLM U p A = a1LM U p A + a2LM p A + a3LM p A + a4LM U p A := by
  rw [curlMatLM_apply, a1LM_apply, a2LM_apply, a3LM_apply, a4LM_apply,
    ← sum_Aprime_eq_curl]
  change (AprimeXY A p : Matrix (Fin 2) (Fin 2) ℂ) +
    (AprimeYZ U A p : Matrix (Fin 2) (Fin 2) ℂ) +
    (AprimeZW U A p : Matrix (Fin 2) (Fin 2) ℂ) +
    (AprimeWX A p : Matrix (Fin 2) (Fin 2) ℂ) = _
  abel

/-- Source normalization is exactly one half of the raw frozen diagonal bilPlaq. -/
theorem frozen_three_form
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (c s : ℝ) (x y z : ℂ)
    (hr : reHolonomy U p = realHol c) (hi : imHolonomy U p = imagHol s)
    (h1 : a1LM U p A = chargedMat x) (h2 : a2LM p A = 0)
    (h3 : a3LM p A = chargedMat y) (h4 : a4LM U p A = chargedMat z) :
    ⟪curlValueCovariant U A p, curlValueCovariant U A p⟫ +
      (1/2 : ℝ) * bilPlaq U p A A = tripleForm c s x y z := by
  have hc : curlMatLM U p A = chargedMat (x+y+z) := by
    rw [curl_atoms, h1, h2, h3, h4, add_zero, chargedMat_add, chargedMat_add]
  have hn : ⟪curlValueCovariant U A p, curlValueCovariant U A p⟫ =
      Complex.normSq (x+y+z) := charged_inner _ _ hc
  rw [hn, bilPlaq_atoms]
  simp only [b1LM, b2LM, b3LM, b4LM, LinearMap.comp_apply,
    hr, hi, hc, h1, h2, h3, h4, map_zero, mul_zero, zero_mul, Matrix.trace_zero,
    Complex.zero_re, sub_zero, add_zero]
  rw [first_atom, comm_atom, comm_atom, comm_atom]
  unfold tripleForm
  ring

/-- Right-boundary version, with the exterior (fourth) atom zero. -/
theorem frozen_three_form_right
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (c s : ℝ) (x y z : ℂ)
    (hr : reHolonomy U p = realHol c) (hi : imHolonomy U p = imagHol s)
    (h1 : a1LM U p A = chargedMat x) (h2 : a2LM p A = chargedMat y)
    (h3 : a3LM p A = chargedMat z) (h4 : a4LM U p A = 0) :
    ⟪curlValueCovariant U A p, curlValueCovariant U A p⟫ +
      (1/2 : ℝ) * bilPlaq U p A A = tripleForm c s x y z := by
  have hc : curlMatLM U p A = chargedMat (x+y+z) := by
    rw [curl_atoms, h1, h2, h3, h4, add_zero, chargedMat_add, chargedMat_add]
  have hn : ⟪curlValueCovariant U A p, curlValueCovariant U A p⟫ =
      Complex.normSq (x+y+z) := charged_inner _ _ hc
  rw [hn, bilPlaq_atoms]
  simp only [b1LM, b2LM, b3LM, b4LM, LinearMap.comp_apply,
    hr, hi, hc, h1, h2, h3, h4, map_zero, mul_zero, zero_mul, Matrix.trace_zero,
    Complex.zero_re, sub_zero, add_zero]
  rw [first_atom, comm_atom, comm_atom, comm_atom]
  unfold tripleForm
  ring

/-- Left boundary: the first normal atom and the exterior second atom vanish. -/
theorem frozen_two_form
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (c s : ℝ) (y z : ℂ)
    (hr : reHolonomy U p = realHol c) (hi : imHolonomy U p = imagHol s)
    (h1 : a1LM U p A = 0) (h2 : a2LM p A = 0)
    (h3 : a3LM p A = chargedMat y) (h4 : a4LM U p A = chargedMat z) :
    ⟪curlValueCovariant U A p, curlValueCovariant U A p⟫ +
      (1/2 : ℝ) * bilPlaq U p A A = pairForm c s y z := by
  rw [← tripleForm_zero_left]
  exact frozen_three_form U p A c s 0 y z hr hi
    (h1.trans chargedMat_zero.symm) h2 h3 h4

#print axioms chargedMat
#print axioms realHol
#print axioms imagHol
#print axioms chargedMat_add
#print axioms chargedMat_zero
#print axioms charged_inner
#print axioms first_atom
#print axioms comm_atom
#print axioms curl_atoms
#print axioms frozen_three_form
#print axioms frozen_three_form_right
#print axioms frozen_two_form
end AdalyFormal.Round12.Noncancel.Plaquette

namespace AdalyFormal.Round12.Noncancel.Trace
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.D1Literal (uθ uMat)

variable {L : PeriodicLatticeExtent}

/-- Actual charged coordinate at a physical bond, on the touching-bond carrier. -/
def bondTrace (G : TowerGeom L) (b : Bond L) : ↥(bondSupp G) →ₗ[ℝ] ℂ where
  toFun u := (((u : BondFnL2 L) b : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) 0 1
  map_add' u v := rfl
  map_smul' a u := by
    change ((a : ℂ) • (((u : BondFnL2 L) b : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) 0 1 = _
    rfl

def quarter (G : TowerGeom L) : ↥(bondSupp G) ≃ₗᵢ[ℝ] ↥(bondSupp G) :=
  adEL (fun _ => uθ (Real.pi/4)) G

theorem rotation_entry (α : ℝ) (X : SuTwo) :
    (((RMap (uθ α) X) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 =
      Complex.exp (((2*α : ℝ) : ℂ)*Complex.I) *
        (X : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := by
  rw [RMap_coe_apply]
  change (uMat α * (X : Matrix (Fin 2) (Fin 2) ℂ) * (uMat α)ᴴ) 0 1 = _
  simp [uMat, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, ← Complex.exp_conj]
  rw [mul_right_comm, ← Complex.exp_add]
  congr 2
  ring

theorem bondTrace_quarter (G : TowerGeom L) (b : Bond L) (u : ↥(bondSupp G)) :
    bondTrace G b (quarter G u) = Complex.I * bondTrace G b u := by
  change (((RMap (uθ (Real.pi/4)) ((u : BondFnL2 L) b)) : SuTwo) :
    Matrix (Fin 2) (Fin 2) ℂ) 0 1 = _
  rw [rotation_entry, show (2 : ℝ)*(Real.pi/4) = Real.pi/2 by ring]
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.exp_pi_div_two_mul_I]
  rfl

/-- Concrete frozen carrier conclusion: one positive trace-zero fiber suffices for
whole-kernel charged-line containment. The positivity hypothesis remains explicit. -/
theorem physical_kernel_line (G : TowerGeom L) (b : Bond L)
    (A : ↥(bondSupp G) →L[ℝ] ↥(bondSupp G))
    (hcomm : ∀ u, A (quarter G u) = quarter G (A u))
    (hp : ∀ u, bondTrace G b u = 0 → u ≠ 0 → 0 < ⟪u, A u⟫)
    (u₀ : ↥(bondSupp G)) (hu₀ : A u₀ = 0) (hne : u₀ ≠ 0) :
    quarter G (quarter G u₀) = -u₀ ∧
      ∀ u, A u = 0 → u ∈ Submodule.span ℝ {u₀, quarter G u₀} :=
  Star.kernel_line_of_trace A.toLinearMap (quarter G).toLinearEquiv.toLinearMap
    (bondTrace G b) hcomm (bondTrace_quarter G b) hp u₀ hu₀ hne

#print axioms bondTrace
#print axioms quarter
#print axioms rotation_entry
#print axioms bondTrace_quarter
#print axioms physical_kernel_line
end AdalyFormal.Round12.Noncancel.Trace

/-! Copies of the two original analytic-family definitions and elementary analytic
exponential lemmas, in their original namespace. -/
namespace AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Target.ClayStatement
open AdalyFormal.D1Literal (SU2m)
variable {L : PeriodicLatticeExtent}

def AnM (f : ℝ → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ (θ₀ : ℝ) (i j : Fin 2), AnalyticAt ℝ (fun θ => f θ i j) θ₀

def AnFam (U : ℝ → PeriodicLinkConfiguration SU2m L) : Prop :=
  ∀ e : PeriodicLatticeEdge L, AnM fun θ => ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)

theorem analyticAt_exp_I (s : ℝ) (θ₀ : ℝ) :
    AnalyticAt ℝ (fun θ : ℝ => Complex.exp (s * θ * Complex.I)) θ₀ := by
  have hlin : AnalyticAt ℝ (fun θ : ℝ => (s : ℂ) * (θ : ℂ) * Complex.I) θ₀ := by
    have h1 : AnalyticAt ℝ (fun θ : ℝ => ((θ : ℂ))) θ₀ :=
      (Complex.ofRealCLM.analyticAt θ₀).congr (Filter.Eventually.of_forall (fun θ => rfl))
    exact (analyticAt_const.fun_mul h1).fun_mul analyticAt_const
  have hexp : AnalyticAt ℝ Complex.exp ((fun θ : ℝ => (s : ℂ) * (θ : ℂ) * Complex.I) θ₀) :=
    (analyticAt_cexp (z := (s : ℂ) * (θ₀ : ℂ) * Complex.I)).restrictScalars
  exact AnalyticAt.comp (f := fun θ : ℝ => (s : ℂ) * (θ : ℂ) * Complex.I) hexp hlin

theorem anM_uMat : AnM fun θ => AdalyFormal.D1Literal.uMat θ := by
  intro θ₀ i j
  fin_cases i <;> fin_cases j
  · refine (analyticAt_exp_I 1 θ₀).congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp [AdalyFormal.D1Literal.uMat]
  · simp only [AdalyFormal.D1Literal.uMat]
    simp
    exact analyticAt_const
  · simp only [AdalyFormal.D1Literal.uMat]
    simp
    exact analyticAt_const
  · refine (analyticAt_exp_I (-1) θ₀).congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp [AdalyFormal.D1Literal.uMat]

#print axioms AnM
#print axioms AnFam
#print axioms analyticAt_exp_I
#print axioms anM_uMat
end AdalyFormal.Round9.Guarded.QualitativeR2

namespace AdalyFormal.Round12.Noncancel.Path
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.D1Literal
open AdalyFormal.Round9.Guarded.QualitativeR2 (AnM AnFam anM_uMat)
variable {L : PeriodicLatticeExtent}

/-- The four transverse links incident to one site (when transverse side lengths exceed two). -/
def starLinks (x : PeriodicLatticeSite L) : Set (Bond L) :=
  {e | e.2 ≠ 0 ∧ (e.1 = x ∨ periodicLatticeShift e.1 e.2 = x)}

open Classical in
/-- Equal-sign exterior star; unlike the translation-invariant twist, the support is local. -/
def starPath (x : PeriodicLatticeSite L) (t : ℝ) : Cfg L :=
  fun e => if e ∈ starLinks x then uθ t else 1

theorem starPath_zero (x : PeriodicLatticeSite L) : starPath x 0 = fun _ => 1 := by
  funext e
  simp [starPath, uθ_zero]

theorem starPath_cont (x : PeriodicLatticeSite L) : ContFam (starPath x) := by
  intro e
  by_cases h : e ∈ starLinks x
  · simp only [starPath, h, if_true]
    change Continuous fun t => uMat t
    unfold uMat
    refine continuous_matrix (fun i j => ?_)
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · simp only [starPath, h, if_false]
    exact continuous_const

theorem starPath_an (x : PeriodicLatticeSite L) : AnFam (starPath x) := by
  intro e
  by_cases h : e ∈ starLinks x
  · simp only [starPath, h, if_true]
    show AnM fun t => uMat t
    exact anM_uMat
  · intro t i j
    simp only [starPath, h, if_false]
    exact analyticAt_const

theorem starLinks_exterior (Om : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (hx : x ∉ Om)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om)) :
    starLinks x ⊆ Zb Om := by
  rintro ⟨z,ν⟩ ⟨hν,hz | hz⟩
  · change z = x at hz
    subst z
    exact ⟨hx, fun h => hx ((htrans x ν hν).mp h)⟩
  · exact ⟨fun h => hx (hz ▸ (htrans z ν hν).mpr h), fun h => hx (hz ▸ h)⟩

theorem starPath_off_exterior (Om : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (hx : x ∉ Om)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om))
    (t : ℝ) (e : Bond L) (he : e ∉ Zb Om) : starPath x t e = 1 := by
  have hh : e ∉ starLinks x := fun h => he (starLinks_exterior Om x hx htrans h)
  simp [starPath, hh]

theorem starPath_interior (Om : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (hx : x ∉ Om)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om))
    (t : ℝ) (e : Bond L) (he : e.1 ∈ Om) : starPath x t e = 1 := by
  have hh : e ∉ starLinks x := fun h => (starLinks_exterior Om x hx htrans h).1 he
  simp [starPath, hh]

theorem starPath_normal (x z : PeriodicLatticeSite L) (t : ℝ) :
    starPath x t (z,0) = 1 := by simp [starPath, starLinks]

/-- Use the exterior site immediately to the right of a frozen boundary point. -/
theorem star_holonomy1 {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hbd : BdPt Om x) (t : ℝ) (ν : {ν : Fin 3 // 0 < ν}) :
    holonomyElem (starPath (periodicLatticeShift x 0) t) (P1 x ν) = uθ t := by
  have hν : ν.1 ≠ 0 := ne_of_gt ν.2
  have h1 := starPath_normal (periodicLatticeShift x 0) x t
  have h2 : starPath (periodicLatticeShift x 0) t (periodicLatticeShift x 0,ν.1) = uθ t := by
    simp [starPath, starLinks, hν]
  have h3 := starPath_normal (periodicLatticeShift x 0) (periodicLatticeShift x ν.1) t
  have h4 := starPath_interior Om (periodicLatticeShift x 0) hbd.hx' hbd.trans t (x,ν.1) hbd.hx
  change periodicPlaquetteHolonomy _ _ = _
  unfold periodicPlaquetteHolonomy P1
  simp only
  rw [h1,h2,h3,h4]
  simp

theorem star_holonomy2 {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hbd : BdPt Om x) (t : ℝ) (ν : {ν : Fin 3 // 0 < ν}) :
    holonomyElem (starPath (periodicLatticeShift x 0) t) (P2 x ν) = uθ t := by
  have hν : ν.1 ≠ 0 := ne_of_gt ν.2
  have h1 := starPath_normal (periodicLatticeShift x 0) (periodicLatticeShiftBack x ν.1) t
  have h2 : starPath (periodicLatticeShift x 0) t
      (periodicLatticeShift (periodicLatticeShiftBack x ν.1) 0,ν.1) = uθ t := by
    have hs : periodicLatticeShift (periodicLatticeShift (periodicLatticeShiftBack x ν.1) 0) ν.1 =
        periodicLatticeShift x 0 := by
      rw [AdalyFormal.StatementLaneR8.shift_comm _ (Ne.symm hν), periodicLatticeShift_shiftBack]
    simp [starPath, starLinks, hν, hs]
  have h3 := starPath_normal (periodicLatticeShift x 0) x t
  have h4 := starPath_interior Om (periodicLatticeShift x 0) hbd.hx' hbd.trans t
    (periodicLatticeShiftBack x ν.1,ν.1) (hbd.shiftBack_mem ν)
  change periodicPlaquetteHolonomy _ _ = _
  unfold periodicPlaquetteHolonomy P2
  simp only
  rw [h1,h2,periodicLatticeShift_shiftBack,h3,h4]
  simp

/-- A genuine negative endpoint on the frozen all-plaquette carrier, for the local star.
This does not locate the first crossing below pi/2 or prove jet detection. -/
theorem star_negative_endpoint {ell M R k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell0 : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (Lam : Set (PeriodicLatticeSite Lu)) (a : ℝ)
    (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17*ell ≤ R*M)
    {x : PeriodicLatticeSite (scaleUp ell k Lu)} (hbd : BdPt (S.Om 0) x)
    (ha : 0 ≤ a) (ha4 : a < 4) (X : SuTwo) (hX : X ≠ 0) :
    ∃ v : ↥(bondSupp (geomOf ell k S)),
      ⟪v, (dataS selAll selAll (gparams ell k Lu hell0 S
        (starPath (periodicLatticeShift x 0) Real.pi) a Lam)).Ginv v⟫ < 0 := by
  let U := starPath (periodicLatticeShift x 0) Real.pi
  let P := gparams ell k Lu hell0 S U a Lam
  have hm := sing_mem_bondSupp (geomOf ell k S) hbd.hx X
  let v : ↥(bondSupp (geomOf ell k S)) := ⟨sing (x,0) X,hm⟩
  have hn : 0 < hsInner X X := by
    exact lt_of_le_of_ne (real_inner_self_nonneg (x := X))
      (fun h => hX (AdalyFormal.Balaban.SuTwoInner.hsInner_self_eq_zero h.symm))
  have hd : ⟪v, (dataS selAll selAll P).Dpi v⟫ = -4*hsInner X X := by
    have e := E0_Dpi_inner selAll (geomOf ell k S) U a v
    refine e.trans ?_
    have hw : Wop (geomOf ell k S) U a (iE (geomOf ell k S) v) = sing (x,0) X :=
      Wop_sing hS (by omega) hbd U a X
    rw [hw]
    apply delta_value U x X hbd.side
    · intro ν
      change ((holonomyElem (starPath _ Real.pi) (P1 x ν) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = -1
      rw [star_holonomy1 hbd, uθ_pi_coe]
    · intro ν
      change ((holonomyElem (starPath _ Real.pi) (P2 x ν) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = -1
      rw [star_holonomy2 hbd, uθ_pi_coe]
    · intro ν
      exact starPath_interior (S.Om 0) _ hbd.hx' hbd.trans _ _ (hbd.shiftBack_mem ν)
  have ht : (dataS selAll selAll P).T v = 0 :=
    Tfull_sing_zero hS (by omega) hbd U X
  have hmass : ⟪v, (dataS selAll selAll P).Mass v⟫ ≤ a*hsInner X X := by
    change ⟪v, ((pE (geomOf ell k S)).comp ((MassFull (geomOf ell k S) a
      (bondSectorOf (geomOf ell k S) U)).comp (iE (geomOf ell k S)))) v⟫ ≤ _
    simp only [ContinuousLinearMap.comp_apply]
    rw [pE_inner_right]
    exact Mass_sing_le hS hell (by omega) hbd U a ha X
  refine ⟨v,?_⟩
  change ⟪v, (dataS selAll selAll P).Ginv v⟫ < 0
  rw [BaseDataS.inner_Ginv,hd,ht]
  simp only [norm_zero]
  nlinarith

#print axioms starLinks
#print axioms starPath
#print axioms starPath_zero
#print axioms starPath_cont
#print axioms starPath_an
#print axioms starLinks_exterior
#print axioms starPath_off_exterior
#print axioms starPath_interior
#print axioms starPath_normal
#print axioms star_holonomy1
#print axioms star_holonomy2
#print axioms star_negative_endpoint
end AdalyFormal.Round12.Noncancel.Path

namespace AdalyFormal.Round12.Noncancel.Gauge
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Round12.Noncancel.Path

/- Verbatim frozen-operator covariance argument from R1_Dictionary.lean. -/
theorem Ginv_all_gauge {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (γ : GaugeFn (scaleUp ell k Lu))
    (x : ↥(bondSupp (geomOf ell k S))) :
    (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).Ginv
        (adEL γ (geomOf ell k S) x) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Ginv x) := by
  have hB := bondEqv_gauge (gparams ell k Lu hell S U a Lam) γ
  have hD := hB.baseEqv
  have hW : ∀ z, Wop (geomOf ell k S) (periodicGaugeTransform γ U) a (adBL γ z) =
      adBL γ (Wop (geomOf ell k S) U a z) := fun z => hB.W z
  have hΔ : ∀ z, AdalyFormal.StatementLaneR6.deltaKLocCLM (periodicGaugeTransform γ U) Set.univ
      (adBL γ z) = adBL γ (AdalyFormal.StatementLaneR6.deltaKLocCLM U Set.univ z) :=
    fun z => deltaKLocCLM_gauge γ U Set.univ z
  have hDp : ∀ z, DpiFullS selAll (geomOf ell k S) (periodicGaugeTransform γ U) a (adBL γ z) =
      adBL γ (DpiFullS selAll (geomOf ell k S) U a z) := by
    intro z
    simp only [DpiFullS, DeltaS, selAll, ContinuousLinearMap.comp_apply]
    rw [hW, hΔ]
    exact adjoint_intertwine (adBL γ) (adBL γ) hW _
  have hDpi : (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).Dpi
      (adEL γ (geomOf ell k S) x) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Dpi x) := by
    show pE (geomOf ell k S) (DpiFullS selAll (geomOf ell k S) (periodicGaugeTransform γ U) a
        (iE (geomOf ell k S) (adEL γ (geomOf ell k S) x))) =
      adEL γ (geomOf ell k S) (pE (geomOf ell k S)
        (DpiFullS selAll (geomOf ell k S) U a (iE (geomOf ell k S) x)))
    rw [iE_adEL, hDp, pE_adBL]
  have hT : (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).T
      (adEL γ (geomOf ell k S) x) =
      adSL γ ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).T x) := hD.T x
  have hTs : ∀ s, (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a
      Lam)).Ts (adSL γ s) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Ts s) :=
    hD.Ts
  have hM : (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).Mass
      (adEL γ (geomOf ell k S) x) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Mass x) :=
    hD.Mass x
  simp only [BaseDataS.Ginv, add_apply, ContinuousLinearMap.comp_apply]
  rw [hDpi, hT, hTs, hM, map_add, map_add]

theorem uθ_comm (α s : ℝ) : uθ α * uθ s = uθ s * uθ α := by
  apply Subtype.ext
  show uMat α * uMat s = uMat s * uMat α
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem starPath_fixed {L : PeriodicLatticeExtent}
    (x : PeriodicLatticeSite L) (t α : ℝ) :
    periodicGaugeTransform (fun _ => uθ α) (starPath x t) = starPath x t := by
  funext e
  change uθ α * starPath x t e * (uθ α)⁻¹ = starPath x t e
  by_cases he : e ∈ starLinks x
  · simp only [starPath,he,if_true]
    rw [uθ_comm, mul_assoc, mul_inv_cancel, mul_one]
  · simp [starPath,he]

theorem star_all_comm {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (x : PeriodicLatticeSite (scaleUp ell k Lu))
    (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (t α : ℝ)
    (u : ↥(bondSupp (geomOf ell k S))) :
    (dataS selAll selAll (gparams ell k Lu hell S (starPath x t) a Lam)).Ginv
      (adEL (fun _ => uθ α) (geomOf ell k S) u) =
      adEL (fun _ => uθ α) (geomOf ell k S)
        ((dataS selAll selAll (gparams ell k Lu hell S (starPath x t) a Lam)).Ginv u) := by
  have h := Ginv_all_gauge hell S (starPath x t) a Lam (fun _ => uθ α) u
  rwa [starPath_fixed] at h

/-- For this ACTUAL star operator, only trace-zero positivity and a nonzero kernel
vector are needed. Neither hypothesis is asserted at the actual first crossing. -/
theorem star_kernel_line {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (x : PeriodicLatticeSite (scaleUp ell k Lu))
    (b : Bond (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (t : ℝ)
    (hp : ∀ u, Trace.bondTrace (geomOf ell k S) b u = 0 → u ≠ 0 →
      0 < ⟪u, (dataS selAll selAll (gparams ell k Lu hell S (starPath x t) a Lam)).Ginv u⟫)
    (u₀ : ↥(bondSupp (geomOf ell k S)))
    (hu₀ : (dataS selAll selAll (gparams ell k Lu hell S (starPath x t) a Lam)).Ginv u₀ = 0)
    (hne : u₀ ≠ 0) :
    Trace.quarter (geomOf ell k S) (Trace.quarter (geomOf ell k S) u₀) = -u₀ ∧
      ∀ u, (dataS selAll selAll (gparams ell k Lu hell S (starPath x t) a Lam)).Ginv u = 0 →
        u ∈ Submodule.span ℝ {u₀, Trace.quarter (geomOf ell k S) u₀} :=
  Trace.physical_kernel_line (geomOf ell k S) b _
    (star_all_comm hell S x a Lam t (Real.pi/4)) hp u₀ hu₀ hne

#print axioms Ginv_all_gauge
#print axioms uθ_comm
#print axioms starPath_fixed
#print axioms star_all_comm
#print axioms star_kernel_line
end AdalyFormal.Round12.Noncancel.Gauge
