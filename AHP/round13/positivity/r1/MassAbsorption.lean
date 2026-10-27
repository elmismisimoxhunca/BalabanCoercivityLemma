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

/-! Full three-color identities: neutral values are retained, not discarded by a
vanishing charged trace. The displayed local estimates do not yet identify a
complete-carrier star decomposition. -/
namespace AdalyFormal.Round12.Noncancel.FullPlaquette
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Round12.Noncancel.Star
open AdalyFormal.Round12.Noncancel.Plaquette

/-- General su(2) matrix with neutral coordinate h and charged coordinate z. -/
def lieMat (h : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(h : ℂ)*Complex.I, z; -star z, -(h : ℂ)*Complex.I]

theorem lieMat_add (h k : ℝ) (y z : ℂ) :
    lieMat (h+k) (y+z) = lieMat h y + lieMat k z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lieMat, add_mul, add_comm]

theorem lieMat_zero : lieMat 0 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lieMat]

theorem lieMat_coordinates (X : SuTwo) :
    (X : Matrix (Fin 2) (Fin 2) ℂ) =
      lieMat ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im
        ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 1) := by
  have h00 := re_entry00_eq_zero X
  have h10 := entry_skew X.property.1 0 1
  have h11 := entry11_eq_neg_entry00 X
  ext i j
  fin_cases i <;> fin_cases j
  · apply Complex.ext <;> simp [lieMat, h00]
  · simp [lieMat]
  · simpa [lieMat] using h10
  · apply Complex.ext <;> simp [lieMat, h11, h00]

theorem full_inner (X : SuTwo) (h : ℝ) (z : ℂ)
    (hX : (X : Matrix (Fin 2) (Fin 2) ℂ) = lieMat h z) :
    ⟪X,X⟫ = Complex.normSq z + h^2 := by
  change hsInner X X = _
  rw [hsInner_self_entries,hX]
  simp [lieMat, add_comm]

theorem full_first_atom (c h : ℝ) (z : ℂ) :
    (Matrix.trace (smulILM (lieMat h z) * smulILM (lieMat h z) *
      (realHol c - 1))).re = 2*(c-1)*(Complex.normSq z+h^2) := by
  simp [lieMat, realHol, smulILM_apply, Matrix.mul_apply, Matrix.trace,
    Matrix.diag, Fin.sum_univ_two, Complex.normSq_apply]
  ring

theorem full_comm_atom (s h k : ℝ) (y z : ℂ) :
    (Matrix.trace (smulILM (smulILM (lieMat h y)) * smulILM (lieMat k z) *
      imagHol s)).re -
    (Matrix.trace (smulILM (smulILM (lieMat k z)) * smulILM (lieMat h y) *
      imagHol s)).re = 4*s*(star y*z).im := by
  simp [lieMat, imagHol, smulILM_apply, Matrix.mul_apply, Matrix.trace,
    Matrix.diag, Fin.sum_univ_two]
  ring

variable {L : PeriodicLatticeExtent}

/-- Exact neutral/charged splitting of the frozen right straddling plaquette form. -/
theorem frozen_full_three_right
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (c s h k l : ℝ) (x y z : ℂ)
    (hr : reHolonomy U p = realHol c) (hi : imHolonomy U p = imagHol s)
    (h1 : a1LM U p A = lieMat h x) (h2 : a2LM p A = lieMat k y)
    (h3 : a3LM p A = lieMat l z) (h4 : a4LM U p A = 0) :
    ⟪curlValueCovariant U A p, curlValueCovariant U A p⟫ +
      (1/2 : ℝ) * bilPlaq U p A A = tripleForm c s x y z + c*(h+k+l)^2 := by
  have hc : curlMatLM U p A = lieMat (h+k+l) (x+y+z) := by
    rw [curl_atoms,h1,h2,h3,h4,add_zero,lieMat_add,lieMat_add]
  have hn := full_inner (curlValueCovariant U A p) (h+k+l) (x+y+z) hc
  rw [hn,bilPlaq_atoms]
  simp only [b1LM,b2LM,b3LM,b4LM,LinearMap.comp_apply,hr,hi,hc,h1,h2,h3,h4,
    map_zero,mul_zero,zero_mul,Matrix.trace_zero,Complex.zero_re,sub_zero,add_zero]
  rw [full_first_atom,full_comm_atom,full_comm_atom,full_comm_atom]
  unfold tripleForm
  ring

/-- The left orientation has the same algebra but zeros its second transported atom. -/
theorem frozen_full_three_left
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (c s h k l : ℝ) (x y z : ℂ)
    (hr : reHolonomy U p = realHol c) (hi : imHolonomy U p = imagHol s)
    (h1 : a1LM U p A = lieMat h x) (h2 : a2LM p A = 0)
    (h3 : a3LM p A = lieMat k y) (h4 : a4LM U p A = lieMat l z) :
    ⟪curlValueCovariant U A p, curlValueCovariant U A p⟫ +
      (1/2 : ℝ) * bilPlaq U p A A = tripleForm c s x y z + c*(h+k+l)^2 := by
  have hc : curlMatLM U p A = lieMat (h+k+l) (x+y+z) := by
    rw [curl_atoms,h1,h2,h3,h4,add_zero,lieMat_add,lieMat_add]
  have hn := full_inner (curlValueCovariant U A p) (h+k+l) (x+y+z) hc
  rw [hn,bilPlaq_atoms]
  simp only [b1LM,b2LM,b3LM,b4LM,LinearMap.comp_apply,hr,hi,hc,h1,h2,h3,h4,
    map_zero,mul_zero,zero_mul,Matrix.trace_zero,Complex.zero_re,sub_zero,add_zero]
  rw [full_first_atom,full_comm_atom,full_comm_atom,full_comm_atom]
  unfold tripleForm
  ring

/-- Killing only the central CHARGED trace leaves a nonnegative neutral square.
The full neutral central value h is unrestricted. -/
theorem full_pair_mass_lower (c s h k l : ℝ) (y z : ℂ)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hcs : c^2+s^2=1) :
    c*(Complex.normSq y+k^2 + (Complex.normSq z+l^2)) ≤
      Complex.normSq y+k^2 + (Complex.normSq z+l^2) +
        pairForm c s y z + c*(h+k+l)^2 := by
  have hp := pair_mass_lower c s hcs y z
  have hn := mul_nonneg hc (sq_nonneg (h+k+l))
  have hk := mul_nonneg (sub_nonneg.mpr hc1) (sq_nonneg k)
  have hl := mul_nonneg (sub_nonneg.mpr hc1) (sq_nonneg l)
  nlinarith

/-- All arms may have different neutral values; no neutral/charged cross term was
silently put into the remainder. An actual whole-carrier form identity is still needed. -/
theorem full_star_mass_lower {ι : Type*} [Fintype ι]
    (c s rest : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (hr : 0 ≤ rest)
    (hcs : c^2+s^2=1) (h k l : ι → ℝ) (y z : ι → ℂ) :
    c*(rest+∑ i, (Complex.normSq (y i)+(k i)^2 +
        (Complex.normSq (z i)+(l i)^2))) ≤
      rest+∑ i, (Complex.normSq (y i)+(k i)^2 +
        (Complex.normSq (z i)+(l i)^2) + pairForm c s (y i) (z i) +
          c*(h i+k i+l i)^2) := by
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    full_pair_mass_lower c s (h i) (k i) (l i) (y i) (z i) hc hc1 hcs)
  rw [← Finset.mul_sum] at hs
  have hh : c*rest ≤ rest := by nlinarith
  nlinarith

#print axioms lieMat
#print axioms lieMat_add
#print axioms lieMat_zero
#print axioms lieMat_coordinates
#print axioms full_inner
#print axioms full_first_atom
#print axioms full_comm_atom
#print axioms frozen_full_three_right
#print axioms frozen_full_three_left
#print axioms full_pair_mass_lower
#print axioms full_star_mass_lower
end AdalyFormal.Round12.Noncancel.FullPlaquette

namespace AdalyFormal.Round12.Noncancel.Mass
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Guarded
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
variable {L : PeriodicLatticeExtent}

def rowZero (G : TowerGeom L) (e : Bond L) (he : e ∈ bondsLam G 0) : BIdx G :=
  ⟨⟨0,Nat.zero_lt_succ _⟩,e,he⟩

theorem Qfull_rowZero (G : TowerGeom L) (U : Cfg L)
    (e : Bond L) (he : e ∈ bondsLam G 0) (A : BondFnL2 L) :
    QfullOf G U A (rowZero G e he) = A e := by
  change (((G.ell : ℝ)^0)⁻¹) • (QlinB G U 0 A) e = _
  rw [QlinB_zero]
  simp

/-- Geometric membership of any touching collar bond in the actual level-zero rows. -/
theorem collar_levelZero {ell M R k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hell : 0 < ell) (e : Bond L)
    (ht : e ∈ bondsOm0 (geomOf ell k S))
    (h0 : e.1 ∉ S.Om 1) (h1 : periodicLatticeShift e.1 e.2 ∉ S.Om 1) :
    e ∈ bondsLam (geomOf ell k S) 0 := by
  by_contra h
  rcases endpoint_om1 hell hS e ht h with h | h
  · exact h0 h
  · exact h1 h

/-- Any selected finite family of DISTINCT physical level-zero bonds can be
removed from the mass, leaving a nonnegative remainder. -/
theorem leaf_mass_le (G : TowerGeom L) (U : Cfg L) (a : ℝ) (ha : 0 ≤ a)
    (leaves : Finset (Bond L)) (hl : ∀ e ∈ leaves, e ∈ bondsLam G 0)
    (A : BondFnL2 L) :
    a * ∑ e ∈ leaves, ‖A e‖^2 ≤ ⟪A,MassFull G a (bondSectorOf G U) A⟫ := by
  classical
  let f : BIdx G → ℝ := fun p => a*(G.ell : ℝ)^(p.1 : ℕ)*‖QfullOf G U A p‖^2
  let r : {e // e ∈ leaves} → BIdx G := fun e => rowZero G e.val (hl e.val e.property)
  have hinj : Function.Injective r := by
    intro e e' h
    apply Subtype.ext
    exact congrArg (fun p : BIdx G => p.2.val) h
  have hterm (e : {e // e ∈ leaves}) : f (r e) = a * ‖A e.val‖^2 := by
    change a*(G.ell : ℝ)^0*‖QfullOf G U A (rowZero G e.val (hl e.val e.property))‖^2 = _
    rw [Qfull_rowZero]
    simp
  have hsum : (∑ e : {e // e ∈ leaves}, f (r e)) = a * ∑ e ∈ leaves, ‖A e‖^2 := by
    rw [Finset.sum_congr rfl (fun e _ => hterm e), ← Finset.mul_sum]
    congr 1
    exact Finset.sum_coe_sort leaves (fun e => ‖A e‖^2)
  have hn : ∀ p, 0 ≤ f p := fun p => mul_nonneg (mul_nonneg ha (by positivity)) (sq_nonneg _)
  rw [inner_MassFull]
  change _ ≤ ∑ p, f p
  rw [← hsum, ← Finset.sum_image (fun x _ y _ h => hinj h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun p _ _ => hn p)

/-- The same estimate on the actual touching-bond carrier. -/
theorem carrier_leaf_mass_le (G : TowerGeom L) (U : Cfg L) (a : ℝ) (ha : 0 ≤ a)
    (leaves : Finset (Bond L)) (hl : ∀ e ∈ leaves, e ∈ bondsLam G 0)
    (u : ↥(bondSupp G)) :
    a * ∑ e ∈ leaves, ‖(iE G u) e‖^2 ≤
      ⟪u, pE G (MassFull G a (bondSectorOf G U) (iE G u))⟫ := by
  rw [pE_inner_right]
  exact leaf_mass_le G U a ha leaves hl (iE G u)

/-- An actual finite decomposition of the mass with a nonnegative remainder. -/
theorem mass_split (G : TowerGeom L) (U : Cfg L) (a : ℝ) (ha : 0 ≤ a)
    (leaves : Finset (Bond L)) (hl : ∀ e ∈ leaves, e ∈ bondsLam G 0)
    (A : BondFnL2 L) :
    ∃ rest : ℝ, 0 ≤ rest ∧ ⟪A,MassFull G a (bondSectorOf G U) A⟫ =
      rest + a * ∑ e ∈ leaves, ‖A e‖^2 := by
  refine ⟨⟪A,MassFull G a (bondSectorOf G U) A⟫ - a*∑ e ∈ leaves, ‖A e‖^2,
    sub_nonneg.mpr (leaf_mass_le G U a ha leaves hl A), ?_⟩
  ring

#print axioms rowZero
#print axioms Qfull_rowZero
#print axioms collar_levelZero
#print axioms leaf_mass_le
#print axioms carrier_leaf_mass_le
#print axioms mass_split
end AdalyFormal.Round12.Noncancel.Mass

namespace AdalyFormal.Round12.Noncancel.Boundary
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Guarded
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 gradValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack gradCovariantAdjointValue)
variable {L : PeriodicLatticeExtent}

/-- The exact dressing potential is zero outside the first coarse region.
This includes the whole collar and does not require an inverse-unit premise. -/
theorem potential_zero_off_om1 {ell k : ℕ} (S : Tower L) (U : Cfg L)
    (a : ℝ) (f : SiteL2 L) {x : PeriodicLatticeSite L} (hx : x ∉ S.Om 1) :
    (Gp (geomOf ell k S) U a (Rproj (geomOf ell k S) U f)) x = 0 := by
  by_cases hx0 : x ∈ S.Om 0
  · apply Gp_Rproj_lam0
    exact ⟨fun μ => by simp, hx0, by simpa using hx⟩
  · exact Gp_Rproj_out _ _ _ _ hx0

/-- W agrees pointwise with the original field on every bond with both endpoints
outside Omega_1. This is not restricted to a single-bond test field. -/
theorem Wop_eq_on_collar {ell k : ℕ} (S : Tower L) (U : Cfg L) (a : ℝ)
    (A : BondFnL2 L) (e : Bond L)
    (h0 : e.1 ∉ S.Om 1) (h1 : periodicLatticeShift e.1 e.2 ∉ S.Om 1) :
    (Wop (geomOf ell k S) U a A) e = A e := by
  have hz : (gradL2 U (Gp (geomOf ell k S) U a
      (Rproj (geomOf ell k S) U (gradAdj U A)))) e = 0 := by
    rw [gradL2_apply]
    unfold gradValueCovariant
    rw [potential_zero_off_om1 S U a _ h0, potential_zero_off_om1 S U a _ h1]
    simp
  change A e - (gradL2 U (Gp (geomOf ell k S) U a
    (Rproj (geomOf ell k S) U (gradAdj U A)))) e = A e
  rw [hz, sub_zero]

/-- Every omitted plaquette is in the collar. Therefore its four dressed atoms
are exactly the four raw atoms, for an arbitrary fine field. -/
theorem Wop_eq_on_omitted {ell M R k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (h4 : 4 ≤ R*M) (U : Cfg L) (a : ℝ)
    (A : BondFnL2 L) {p : PeriodicLatticePlaquette L}
    (hp : p ∉ plaqIn (S.Om 0)) {e : Bond L} (he : e ∈ periodicPlaquetteBoundaryEdges p) :
    (Wop (geomOf ell k S) U a A) e = A e := by
  obtain ⟨h0,h1⟩ := edge_ends_not_om1_of_notIn hS h4 hp he
  exact Wop_eq_on_collar S U a A e h0 h1

/-- A single bond of arbitrary orientation has divergence supported at its endpoints. -/
theorem gradAdj_sing_support (U : Cfg L) (e : Bond L) (X : SuTwo)
    (z : PeriodicLatticeSite L) (hz0 : z ≠ e.1)
    (hz1 : z ≠ periodicLatticeShift e.1 e.2) :
    gradAdj U (sing e X) z = 0 := by
  rw [show gradAdj U (sing e X) z = (WithLp.ofLp (gradAdj U (sing e X))) z from rfl,
    gradAdj_apply]
  unfold gradCovariantAdjointValue
  refine Finset.sum_eq_zero (fun μ _ => ?_)
  have h0 : (WithLp.ofLp (sing e X)) (z,μ) = 0 :=
    sing_apply_ne _ _ (fun h => hz0 (congrArg Prod.fst h))
  have h1 : (WithLp.ofLp (sing e X)) (periodicLatticeShiftBack z μ,μ) = 0 := by
    apply sing_apply_ne
    intro h
    have hμ : μ = e.2 := congrArg Prod.snd h
    have hx : periodicLatticeShiftBack z μ = e.1 := congrArg Prod.fst h
    apply hz1
    rw [← hx, ← hμ, periodicLatticeShift_shiftBack]
  rw [h0,h1]
  simp

/-- On a finite-radius boundary patch, a raw single-bond field has zero gauge term.
The same exterior witness can be used for any orientation, including tangential leaves. -/
theorem Tfull_sing_zero_near {ell M R k d : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hd : d+1 ≤ R*M)
    (U : Cfg L) (e : Bond L) (X : SuTwo)
    (x : PeriodicLatticeSite L) (hx : x ∉ S.Om 0)
    (h0 : pdist x e.1 ≤ d) (h1 : pdist x (periodicLatticeShift e.1 e.2) ≤ d) :
    Tfull (geomOf ell k S) U (sing e X) = 0 := by
  unfold Tfull
  simp only [ContinuousLinearMap.comp_apply]
  unfold Rproj
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
  intro u hu
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero (fun z _ => ?_)
  by_cases hz : z = e.1 ∨ z = periodicLatticeShift e.1 e.2
  · have huz : u z = 0 := by
      apply RImage_support S U hu z
      intro y hy hy1
      have hcl := hS.2.2.2.2.1 0 (Nat.zero_le _) x hx y hy1
      have hxz : pdist x z ≤ d := by
        rcases hz with rfl | rfl
        · exact h0
        · exact h1
      have hyz : pdist z y ≤ 1 := hy
      have ht := pdist_triangle x z y
      have hb : bigSide M ell 0 = M := by simp [bigSide]
      rw [hb] at hcl
      omega
    rw [huz]
    simp
  · push Not at hz
    rw [gradAdj_sing_support U e X z hz.1 hz.2]
    simp

theorem Wop_sing_near {ell M R k d : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hd : d+1 ≤ R*M)
    (U : Cfg L) (a : ℝ) (e : Bond L) (X : SuTwo)
    (x : PeriodicLatticeSite L) (hx : x ∉ S.Om 0)
    (h0 : pdist x e.1 ≤ d) (h1 : pdist x (periodicLatticeShift e.1 e.2) ≤ d) :
    Wop (geomOf ell k S) U a (sing e X) = sing e X := by
  have ht := Tfull_sing_zero_near hS hd U e X x hx h0 h1
  unfold Tfull at ht
  simp only [ContinuousLinearMap.comp_apply] at ht
  unfold Wop
  simp only [sub_apply, one_apply_eq_self,
    ContinuousLinearMap.comp_apply]
  rw [ht]
  simp

#print axioms potential_zero_off_om1
#print axioms Wop_eq_on_collar
#print axioms Wop_eq_on_omitted
#print axioms gradAdj_sing_support
#print axioms Tfull_sing_zero_near
#print axioms Wop_sing_near
end AdalyFormal.Round12.Noncancel.Boundary

namespace AdalyFormal.Round13.Positivity
open Classical
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLaneR6
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.Round12.Noncancel.Star
open AdalyFormal.Round12.Noncancel.FullPlaquette
variable {L : PeriodicLatticeExtent}

/-- The actual frozen summand, including its neutral part. -/
def plaqEnergy (U : Cfg L) (A : BondFnL2 L) (p : PeriodicLatticePlaquette L) : ℝ :=
  ⟪curlValueCovariant U (WithLp.ofLp A) p, curlValueCovariant U (WithLp.ofLp A) p⟫ +
    (1/2 : ℝ) * bilPlaq U p (WithLp.ofLp A) (WithLp.ofLp A)

/-- Exact selector version of frozen delta_form_sum. -/
theorem delta_form_sum_set (U : Cfg L) (S : Set (PeriodicLatticePlaquette L))
    (A : BondFnL2 L) :
    ⟪A, deltaKLocCLM U S A⟫ = ∑ p, if p ∈ S then plaqEnergy U A p else 0 := by
  classical
  rw [inner_deltaKLocCLM]
  have h1 : ⟪plaqMask S (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U A),
      plaqMask S (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U A)⟫ =
      ∑ p, if p ∈ S then
        ⟪curlValueCovariant U (WithLp.ofLp A) p, curlValueCovariant U (WithLp.ofLp A) p⟫ else 0 := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro p _
    simp only [plaqMask_apply]
    split_ifs
    · rfl
    · simp
  have h2 : deltaPrimeBilL2NormLoc U S A A =
      (1/2 : ℝ) * ∑ p, if p ∈ S then bilPlaq U p (WithLp.ofLp A) (WithLp.ofLp A) else 0 := by
    change deltaPrimeBilNormLoc U S (WithLp.ofLp A) (WithLp.ofLp A) = _
    simp only [deltaPrimeBilNormLoc, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.flip_apply, smul_eq_mul, deltaPrimeBilRawLoc_apply]
    ring
  rw [h1, h2, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p ∈ S <;> simp [hp, plaqEnergy]

/-- At any plaquette with identity holonomy the full summand is nonnegative. -/
theorem plaqEnergy_nonneg (U : Cfg L) (A : BondFnL2 L) (p : PeriodicLatticePlaquette L)
    (hr : reHolonomy U p = 1) (hi : imHolonomy U p = 0) :
    0 ≤ plaqEnergy U A p := by
  have hb : bilPlaq U p (WithLp.ofLp A) (WithLp.ofLp A) = 0 := by
    rw [bilPlaq_atoms, hr, hi]
    simp
  simp only [plaqEnergy, hb, mul_zero, add_zero]
  exact real_inner_self_nonneg

open Classical in
def omittedEnergy (P : IngrBParams) (x : ↥(bondSupp P.G)) : ℝ :=
  ∑ p, if p ∈ plaqIn P.G.Om0 then 0 else
    plaqEnergy P.U (Wop P.G P.U P.a (iE P.G x)) p

/-- No locality premise: the exact complete all-minus-localized carrier sum. -/
theorem carrier_form_split (P : IngrBParams) (x : ↥(bondSupp P.G)) :
    ⟪x, (dataS selAll selAll P).Ginv x⟫ =
      ⟪x, (dataS selIn selIn P).Ginv x⟫ + omittedEnergy P x := by
  classical
  have hd : ⟪x, (dataS selAll selAll P).Dpi x⟫ =
      ⟪x, (dataS selIn selIn P).Dpi x⟫ + omittedEnergy P x := by
    change ⟪x, ((pE P.G).comp ((DpiFullS selAll P.G P.U P.a).comp (iE P.G))) x⟫ =
      ⟪x, ((pE P.G).comp ((DpiFullS selIn P.G P.U P.a).comp (iE P.G))) x⟫ + _
    rw [E0_Dpi_inner, E0_Dpi_inner]
    simp only [DeltaS, selAll, selIn, delta_form_sum_set, Set.mem_univ, if_true]
    unfold omittedEnergy
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p ∈ plaqIn P.G.Om0 <;> simp [hp]
  rw [BaseDataS.inner_Ginv, BaseDataS.inner_Ginv, hd]
  have ht : (dataS selAll selAll P).T = (dataS selIn selIn P).T := rfl
  have hm : (dataS selAll selAll P).Mass = (dataS selIn selIn P).Mass := rfl
  rw [ht, hm]
  ring

/-- The localized delta term is nonnegative when its actual plaquettes are flat. -/
theorem localized_Dpi_nonneg (P : IngrBParams) (x : ↥(bondSupp P.G))
    (hr : ∀ p ∈ plaqIn P.G.Om0, reHolonomy P.U p = 1)
    (hi : ∀ p ∈ plaqIn P.G.Om0, imHolonomy P.U p = 0) :
    0 ≤ ⟪x, (dataS selIn selIn P).Dpi x⟫ := by
  classical
  change 0 ≤ ⟪x, ((pE P.G).comp ((DpiFullS selIn P.G P.U P.a).comp (iE P.G))) x⟫
  rw [E0_Dpi_inner]
  simp only [DeltaS, selIn, delta_form_sum_set]
  apply Finset.sum_nonneg
  intro p _
  split_ifs with hp
  · exact plaqEnergy_nonneg _ _ _ (hr p hp) (hi p hp)
  · exact le_rfl

/-- Mass-relative absorption. The loss is 1-c of the MASS, not a guessed
ordinary-norm constant. This retains c of the whole positive localized form. -/
theorem carrier_ge_scaled_local (P : IngrBParams) (x : ↥(bondSupp P.G))
    (c leaves : ℝ) (hc : c ≤ 1)
    (hd : 0 ≤ ⟪x, (dataS selIn selIn P).Dpi x⟫)
    (hl : leaves ≤ ⟪x, (dataS selIn selIn P).Mass x⟫)
    (ho : -(1-c)*leaves ≤ omittedEnergy P x) :
    c * ⟪x, (dataS selIn selIn P).Ginv x⟫ ≤
      ⟪x, (dataS selAll selAll P).Ginv x⟫ := by
  have hm : leaves ≤ ⟪x, (dataS selIn selIn P).Ginv x⟫ := by
    rw [BaseDataS.inner_Ginv]
    have ht : 0 ≤ ‖(dataS selIn selIn P).T x‖^2 := sq_nonneg _
    linarith
  have habs := mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr hc)
  rw [carrier_form_split]
  nlinarith

/-- Actual distinct physical level-zero rows supply the mass budget. -/
theorem carrier_ge_scaled_local_leaves (P : IngrBParams) (ha : P.a = 1)
    (x : ↥(bondSupp P.G)) (c : ℝ) (hc : c ≤ 1)
    (leaves : Finset (Bond P.Lf)) (hl : ∀ e ∈ leaves, e ∈ bondsLam P.G 0)
    (hr : ∀ p ∈ plaqIn P.G.Om0, reHolonomy P.U p = 1)
    (hi : ∀ p ∈ plaqIn P.G.Om0, imHolonomy P.U p = 0)
    (ho : -(1-c)*(∑ e ∈ leaves, ‖(iE P.G x) e‖^2) ≤ omittedEnergy P x) :
    c * ⟪x, (dataS selIn selIn P).Ginv x⟫ ≤
      ⟪x, (dataS selAll selAll P).Ginv x⟫ := by
  refine carrier_ge_scaled_local P x c _ hc (localized_Dpi_nonneg P x hr hi) ?_ ho
  have hm := AdalyFormal.Round12.Noncancel.Mass.leaf_mass_le P.G P.U P.a
    (by rw [ha]; norm_num) leaves hl (iE P.G x)
  change _ ≤ ⟪x, pE P.G (MassFull P.G P.a (bondSectorOf P.G P.U) (iE P.G x))⟫
  rw [pE_inner_right]
  rw [ha, one_mul] at hm
  simpa only [ha] using hm

/-- Positive localization now suffices; no independent strict remainder premise. -/
theorem carrier_positive_of_absorption (P : IngrBParams) (x : ↥(bondSupp P.G))
    (c leaves : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hd : 0 ≤ ⟪x, (dataS selIn selIn P).Dpi x⟫)
    (hl : leaves ≤ ⟪x, (dataS selIn selIn P).Mass x⟫)
    (ho : -(1-c)*leaves ≤ omittedEnergy P x)
    (hp : 0 < ⟪x, (dataS selIn selIn P).Ginv x⟫) :
    0 < ⟪x, (dataS selAll selAll P).Ginv x⟫ :=
  lt_of_lt_of_le (mul_pos hc0 hp) (carrier_ge_scaled_local P x c leaves hc1 hd hl ho)

/-- The exact scalar contribution of each arm is bounded by its two leaf masses;
the central NEUTRAL value h is unrestricted. -/
theorem full_pair_loss_bound (c s h k l : ℝ) (y z : ℂ)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hcs : c^2+s^2=1) :
    -(1-c)*(Complex.normSq y+k^2+(Complex.normSq z+l^2)) ≤
      pairForm c s y z + c*(h+k+l)^2 := by
  have hp := full_pair_mass_lower c s h k l y z hc hc1 hcs
  nlinarith

/-- Summation creates no cardinality loss. Eight DISTINCT leaves can pay the
four negative arms exactly once, irrespective of q and R. -/
theorem full_star_loss_bound {ι : Type*} [Fintype ι]
    (c s : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (hcs : c^2+s^2=1)
    (h k l : ι → ℝ) (y z : ι → ℂ) :
    -(1-c)*(∑ i, (Complex.normSq (y i)+(k i)^2+(Complex.normSq (z i)+(l i)^2))) ≤
      ∑ i, (pairForm c s (y i) (z i)+c*(h i+k i+l i)^2) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => full_pair_loss_bound c s _ _ _ _ _ hc hc1 hcs)

/-- Whole omitted-sum identification is still an explicit PHYSICAL hypothesis. -/
theorem omitted_loss_of_arm_decomposition {ι : Type*} [Fintype ι]
    (P : IngrBParams) (x : ↥(bondSupp P.G)) (c s rest leaves : ℝ)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hcs : c^2+s^2=1) (hr : 0 ≤ rest)
    (h k l : ι → ℝ) (y z : ι → ℂ)
    (hm : leaves = ∑ i, (Complex.normSq (y i)+(k i)^2+(Complex.normSq (z i)+(l i)^2)))
    (he : omittedEnergy P x = rest +
      ∑ i, (pairForm c s (y i) (z i)+c*(h i+k i+l i)^2)) :
    -(1-c)*leaves ≤ omittedEnergy P x := by
  rw [hm, he]
  have hp := full_star_loss_bound c s hc hc1 hcs h k l y z
  linarith

/-- Scale-independent relative loss on ANY closed prefix below half pi. -/
theorem cos_prefix_loss (T t : ℝ) (hT0 : 0 ≤ T) (hT : T < Real.pi/2)
    (ht0 : 0 ≤ t) (ht : t ≤ T) :
    0 < Real.cos T ∧ Real.cos T ≤ Real.cos t ∧
      0 ≤ 1-Real.cos t ∧ 1-Real.cos t ≤ 1-Real.cos T ∧ 1-Real.cos T < 1 := by
  have hpos : 0 < Real.cos T := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hT⟩
  have hmono : Real.cos T ≤ Real.cos t :=
    Real.cos_le_cos_of_nonneg_of_le_pi ht0 (by linarith [Real.pi_pos]) ht
  exact ⟨hpos, hmono, sub_nonneg.mpr (Real.cos_le_one t), by linarith, by linarith⟩

/-- The unmassaged zero-central charged arm can be negative. -/
theorem zero_central_arm_negative : tripleForm 0 1 0 1 (-Complex.I) = -2 := by
  norm_num [tripleForm, Complex.normSq_apply]

/-- Sharpness: no coefficient strictly below one absorbs every half-pi arm
using ONLY its own leaf masses. This does not refute physical P2. -/
theorem halfpi_no_strict_mass_fraction (rho : ℝ) (hrho : rho < 1) :
    ¬ (∀ y z : ℂ, -rho*(Complex.normSq y+Complex.normSq z) ≤ pairForm 0 1 y z) := by
  intro h
  have hh := h 1 (-Complex.I)
  norm_num [pairForm, Complex.normSq_apply] at hh
  linarith

set_option pp.fullNames true
#print axioms delta_form_sum_set
#print axioms plaqEnergy_nonneg
#print axioms carrier_form_split
#print axioms localized_Dpi_nonneg
#print axioms carrier_ge_scaled_local
#print axioms carrier_ge_scaled_local_leaves
#print axioms carrier_positive_of_absorption
#print axioms full_pair_loss_bound
#print axioms full_star_loss_bound
#print axioms omitted_loss_of_arm_decomposition
#print axioms cos_prefix_loss
#print axioms zero_central_arm_negative
#print axioms halfpi_no_strict_mass_fraction
end AdalyFormal.Round13.Positivity

namespace AdalyFormal.Round13.Positivity
open Classical
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLaneR6
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Round12.Noncancel.Star
open AdalyFormal.Round12.Noncancel.FullPlaquette
open AdalyFormal.Round12.Noncancel.Plaquette
variable {L : PeriodicLatticeExtent}

/-- Pointwise input locality, for the complete frozen charged+neutral summand. -/
theorem plaqEnergy_congr_field (U : Cfg L) (A B : BondFnL2 L)
    (p : PeriodicLatticePlaquette L)
    (h : ∀ e ∈ periodicPlaquetteBoundaryEdges p, A e = B e) :
    plaqEnergy U A p = plaqEnergy U B p := by
  have h1 := h _ ((edge_mem p _).mpr (Or.inl rfl))
  have h2 := h _ ((edge_mem p _).mpr (Or.inr (Or.inl rfl)))
  have h3 := h _ ((edge_mem p _).mpr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 := h _ ((edge_mem p _).mpr (Or.inr (Or.inr (Or.inr rfl))))
  have hc : curlValueCovariant U (WithLp.ofLp A) p =
      curlValueCovariant U (WithLp.ofLp B) p := by
    unfold curlValueCovariant
    rw [h1,h2,h3,h4]
  have ha1 : a1LM U p (WithLp.ofLp A) = a1LM U p (WithLp.ofLp B) := by
    simp only [a1LM_apply, AprimeZW, h3]
  have ha2 : a2LM p (WithLp.ofLp A) = a2LM p (WithLp.ofLp B) := by
    simp only [a2LM_apply, AprimeWX, h4]
  have ha3 : a3LM p (WithLp.ofLp A) = a3LM p (WithLp.ofLp B) := by
    simp only [a3LM_apply, AprimeXY, h1]
  have ha4 : a4LM U p (WithLp.ofLp A) = a4LM U p (WithLp.ofLp B) := by
    simp only [a4LM_apply, AprimeYZ, h2]
  unfold plaqEnergy
  rw [hc, bilPlaq_atoms, bilPlaq_atoms]
  simp only [b1LM,b2LM,b3LM,b4LM,LinearMap.comp_apply,
    ha1,ha2,ha3,ha4,curlMatLM_apply,hc]

/-- The complete boundary remainder is a sum in the RAW physical input,
without a site-inverse-unit premise. -/
theorem omittedEnergy_eq_raw (P : IngrBParams) {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) (h4 : 4 ≤ R*M)
    (x : ↥(bondSupp P.G)) :
    omittedEnergy P x = ∑ p, if p ∈ plaqIn P.G.Om0 then 0 else
      plaqEnergy P.U (iE P.G x) p := by
  unfold omittedEnergy
  apply Finset.sum_congr rfl
  intro p _
  split_ifs with hp
  · rfl
  · apply plaqEnergy_congr_field
    intro e he
    exact AdalyFormal.Round12.Noncancel.Boundary.Wop_eq_on_omitted hS h4 P.U P.a _ hp he

/-- Full localized positivity needs no numerical lower constant when a genuine
localized unit is available. All colors are retained. -/
theorem localized_positive_of_unit (P : IngrBParams) (ha : 0 ≤ P.a)
    (hr : ∀ p ∈ plaqIn P.G.Om0, reHolonomy P.U p = 1)
    (hi : ∀ p ∈ plaqIn P.G.Om0, imHolonomy P.U p = 0)
    (hu : IsUnit (dataS selIn selIn P).Ginv)
    (x : ↥(bondSupp P.G)) (hx : x ≠ 0) :
    0 < ⟪x, (dataS selIn selIn P).Ginv x⟫ := by
  have hp : PSD (dataS selIn selIn P).Ginv := by
    intro y
    rw [BaseDataS.inner_Ginv]
    have hd := localized_Dpi_nonneg P y hr hi
    have hm : 0 ≤ ⟪y, (dataS selIn selIn P).Mass y⟫ := by
      change 0 ≤ ⟪y, pE P.G (MassFull P.G P.a P.sector (iE P.G y))⟫
      rw [pE_inner_right, inner_MassFull]
      exact Finset.sum_nonneg (fun p _ => by positivity)
    have ht : 0 ≤ ‖(dataS selIn selIn P).T y‖^2 := sq_nonneg _
    linarith
  apply lt_of_le_of_ne (hp x)
  intro hz
  have hk := psd_kernel _ ((dataS selIn selIn P).Ginv_symm (dataS_laws selIn selIn P)) hp x hz.symm
  exact hx ((injective_iff_map_eq_zero _).mp (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1 x hk)

/-- Direct sufficient interface for P2: only actual geometric leaf-loss data
and the localized unit remain as premises. It is NOT an unconditional P2 theorem. -/
theorem physical_positive_of_leaf_loss (P : IngrBParams) (ha : P.a = 1)
    (x : ↥(bondSupp P.G)) (hx : x ≠ 0) (t : ℝ)
    (ht0 : 0 ≤ t) (ht : t < Real.pi/2)
    (leaves : Finset (Bond P.Lf)) (hl : ∀ e ∈ leaves, e ∈ bondsLam P.G 0)
    (hr : ∀ p ∈ plaqIn P.G.Om0, reHolonomy P.U p = 1)
    (hi : ∀ p ∈ plaqIn P.G.Om0, imHolonomy P.U p = 0)
    (hu : IsUnit (dataS selIn selIn P).Ginv)
    (ho : -(1-Real.cos t)*(∑ e ∈ leaves, ‖(iE P.G x) e‖^2) ≤ omittedEnergy P x) :
    0 < ⟪x, (dataS selAll selAll P).Ginv x⟫ := by
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],ht⟩
  exact lt_of_lt_of_le (mul_pos hc (localized_positive_of_unit P (by rw [ha]; norm_num)
    hr hi hu x hx)) (carrier_ge_scaled_local_leaves P ha x (Real.cos t)
      (Real.cos_le_one t) leaves hl hr hi ho)

/-- Atom-order faithful right-plaquette estimate when the FIRST charged atom
vanishes. The central neutral h is not set to zero. -/
theorem frozen_right_zero_first_lower (U : Cfg L) (A : BondFnL2 L)
    (p : PeriodicLatticePlaquette L) (c s h k l : ℝ) (y z : ℂ)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hcs : c^2+s^2=1)
    (hr : reHolonomy U p = realHol c) (hi : imHolonomy U p = imagHol s)
    (h1 : a1LM U p (WithLp.ofLp A) = lieMat h 0)
    (h2 : a2LM p (WithLp.ofLp A) = lieMat k y)
    (h3 : a3LM p (WithLp.ofLp A) = lieMat l z)
    (h4 : a4LM U p (WithLp.ofLp A) = 0) :
    -(1-c)*(Complex.normSq y+k^2+(Complex.normSq z+l^2)) ≤ plaqEnergy U A p := by
  unfold plaqEnergy
  rw [frozen_full_three_right U p _ c s h k l 0 y z hr hi h1 h2 h3 h4,
    tripleForm_zero_left]
  exact full_pair_loss_bound c s h k l y z hc hc1 hcs

/-- P1 of the right star has its central charged coordinate in the THIRD atom. -/
theorem frozen_right_zero_third_lower (U : Cfg L) (A : BondFnL2 L)
    (p : PeriodicLatticePlaquette L) (c s h k l : ℝ) (y z : ℂ)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hcs : c^2+s^2=1)
    (hr : reHolonomy U p = realHol c) (hi : imHolonomy U p = imagHol s)
    (h1 : a1LM U p (WithLp.ofLp A) = lieMat k y)
    (h2 : a2LM p (WithLp.ofLp A) = lieMat l z)
    (h3 : a3LM p (WithLp.ofLp A) = lieMat h 0)
    (h4 : a4LM U p (WithLp.ofLp A) = 0) :
    -(1-c)*(Complex.normSq y+k^2+(Complex.normSq z+l^2)) ≤ plaqEnergy U A p := by
  unfold plaqEnergy
  rw [frozen_full_three_right U p _ c s k l h y z 0 hr hi h1 h2 h3 h4,
    tripleForm_zero_right]
  convert full_pair_loss_bound c s h k l y z hc hc1 hcs using 1
  ring

/-- A complete finite injection lemma: every non-star omitted plaquette is kept
as nonnegative, and no plaquette is counted twice. -/
theorem omitted_loss_of_injective_arms {ι : Type*} [Fintype ι]
    (P : IngrBParams) {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (h4 : 4 ≤ R*M)
    (x : ↥(bondSupp P.G)) (c : ℝ)
    (arm : ι → PeriodicLatticePlaquette P.Lf) (ha : Function.Injective arm)
    (hout : ∀ i, arm i ∉ plaqIn P.G.Om0) (budget : ι → ℝ)
    (hbad : ∀ i, -(1-c)*budget i ≤ plaqEnergy P.U (iE P.G x) (arm i))
    (hgood : ∀ p, p ∉ plaqIn P.G.Om0 → (∀ i, p ≠ arm i) →
      0 ≤ plaqEnergy P.U (iE P.G x) p) :
    -(1-c)*(∑ i, budget i) ≤ omittedEnergy P x := by
  rw [omittedEnergy_eq_raw P hS h4 x, Finset.mul_sum]
  let f : PeriodicLatticePlaquette P.Lf → ℝ := fun p =>
    if p ∈ plaqIn P.G.Om0 then 0 else plaqEnergy P.U (iE P.G x) p
  have hb : (∑ i, -(1-c)*budget i) ≤ ∑ i, f (arm i) := by
    apply Finset.sum_le_sum
    intro i _
    simpa only [f, if_neg (hout i)] using hbad i
  apply hb.trans
  rw [← Finset.sum_image (fun i _ j _ h => ha h)]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro p _ hp
  change 0 ≤ if p ∈ plaqIn P.G.Om0 then 0 else plaqEnergy P.U (iE P.G x) p
  split_ifs with hin
  · exact le_rfl
  · apply hgood p hin
    intro i heq
    apply hp
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i,heq.symm⟩

set_option pp.fullNames true
#print axioms plaqEnergy_congr_field
#print axioms omittedEnergy_eq_raw
#print axioms localized_positive_of_unit
#print axioms physical_positive_of_leaf_loss
#print axioms frozen_right_zero_first_lower
#print axioms frozen_right_zero_third_lower
#print axioms omitted_loss_of_injective_arms
end AdalyFormal.Round13.Positivity
