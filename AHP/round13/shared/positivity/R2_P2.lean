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

namespace AdalyFormal.Round2.Guarded.Pin

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-! Verbatim operative declarations from D1Lit.lean:29-101. -/
abbrev PlaqSel : Type := ∀ (L : PeriodicLatticeExtent), TowerGeom L → Set (PeriodicLatticePlaquette L)

def selIn : PlaqSel := fun _ G => plaqIn G.Om0

def selAll : PlaqSel := fun _ _ => Set.univ

section Selectors
variable (sD sJ : PlaqSel)

noncomputable def DeltaS {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  AdalyFormal.StatementLaneR6.deltaKLocCLM U (sD L G)

noncomputable def DpiFullS {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (a : ℝ) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  (ContinuousLinearMap.adjoint (Wop G U a)).comp ((DeltaS sD G U).comp (Wop G U a))

theorem DpiFullS_symm {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (a : ℝ) (x y : BondFnL2 L) :
    ⟪DpiFullS sD G U a x, y⟫ = ⟪x, DpiFullS sD G U a y⟫ := by
  simp only [DpiFullS, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]
  exact AdalyFormal.StatementLaneR6.deltaKLocCLM_symm U _ _ _

section Ops
variable (P : IngrBParams)

noncomputable def JfS : BondFnL2 (scaleUp P.ell P.k P.Lu) :=
  WithLp.toLp 2 (fun b => -(AdalyFormal.IngredientFamily.JSU2Loc 1 (sJ _ P.G) P.U b))

noncomputable def dataS : BaseDataS ↥(bondSupp P.G) (SiteL2 (scaleUp P.ell P.k P.Lu)) (FSp P.G) :=
  { baseData P.G P.U P.a P.sector (JfS sJ P) with
    Dpi := (pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G)) }

theorem dataS_laws : (dataS sD sJ P).Laws := by
  refine ⟨fun x y => ?_, P.data_laws.C2_quad⟩
  show ⟪((pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G))) x, y⟫ = ⟪x, ((pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G))) y⟫
  simp only [ContinuousLinearMap.comp_apply]
  rw [pE_inner_left, pE_inner_right]
  exact DpiFullS_symm sD P.G P.U P.a _ _



end Ops
end Selectors
end AdalyFormal.Round2.Guarded.Pin


namespace AdalyFormal.Round4.Guarded.RefuteR1
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin

open Classical

def dilLu (q R : ℕ) : PeriodicLatticeExtent :=
  fun μ => if μ = 0 then 6 * (R * q) + 8 * q - 1 else 4 * q - 1

def dilTower (q R : ℕ) : Tower (scaleUp 2 1 (dilLu q R)) where
  Om j := if j = 0 then {x | 4 * q ≤ (x 0).val ∧ (x 0).val < 12 * (R * q) + 12 * q}
    else if j = 1 then {x | 2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q}
    else ∅

def dilLam (q R : ℕ) : Set (PeriodicLatticeSite (dilLu q R)) :=
  {x | 3 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 3 * (R * q) + 6 * q}

theorem dil_unit_size {q : ℕ} (hq : 0 < q) (R : ℕ) (μ : Fin 3) :
    dilLu q R μ + 1 = if μ = 0 then 6 * (R * q) + 8 * q else 4 * q := by
  by_cases h : μ = 0 <;> simp [dilLu, h] <;> omega

theorem dil_fine_size {q : ℕ} (hq : 0 < q) (R : ℕ) (μ : Fin 3) :
    scaleUp 2 1 (dilLu q R) μ + 1 = if μ = 0 then 12 * (R * q) + 16 * q else 8 * q := by
  simp only [scaleUp, dil_unit_size hq]
  by_cases h : μ = 0 <;> simp [h] <;> omega

def dilPattern (q R : ℕ) (e : Bond (scaleUp 2 1 (dilLu q R))) : Prop :=
  (e.1 0).val = 2*(R*q)+4*q ∧ (e.1 1).val % 2 = 0 ∧ (e.1 2).val % 2 = 0 ∧ e.2 = 1

noncomputable def dilU (q R : ℕ) (ε : ℝ) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun e => if e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) then V e
    else Ug (if dilPattern q R e then ε else 0)

end AdalyFormal.Round4.Guarded.RefuteR1


namespace AdalyFormal.Round5.Guarded.IVTR1
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1

noncomputable def twistU (q R : ℕ) (ε t : ℝ) : LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  dilU q R ε (AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0) t)

end AdalyFormal.Round5.Guarded.IVTR1


namespace AdalyFormal.Round5.Guarded.IVTR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1

open Classical

noncomputable def maskedU (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) : LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun e => if e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) then V e else Ug (f e)

end AdalyFormal.Round5.Guarded.IVTR2


namespace AdalyFormal.Round9.Guarded.Qualitative
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2

open Classical

noncomputable def pathU (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε t : ℝ) : LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  maskedU q R (fun e => ε * f e) (V t)

noncomputable def pathP (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) : IngrBParams :=
  gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (pathU q R V f ε t) a (dilLam q R)

noncomputable def pathA (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selAll selAll (pathP q R V f ε a t)).Ginv

noncomputable def uthPath (q R : ℕ) : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun t => AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0) t

noncomputable def dilMask (q R : ℕ) : Bond (scaleUp 2 1 (dilLu q R)) → ℝ :=
  fun e => if dilPattern q R e then 1 else 0

noncomputable def vacA (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (a t : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  pathA q R V (fun _ => 0) 0 a t

end AdalyFormal.Round9.Guarded.Qualitative



namespace AdalyFormal.Round3.Guarded.RefuteR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
theorem zero_coord_le_pdist {L : PeriodicLatticeExtent} (x y : PeriodicLatticeSite L) :
    pcd (L 0 + 1) (x 0).val (y 0).val ≤ pdist x y :=
  Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (x μ).val (y μ).val)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)


end AdalyFormal.Round3.Guarded.RefuteR2

namespace AdalyFormal.Round4.Guarded.RefuteR1
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round3.Guarded.RefuteR2 (zero_coord_le_pdist)
open AdalyFormal.NonVac (iv_block pcd_clamp pcd_near pcd_self')
theorem dil_fine_bound {q : ℕ} (hq : 0 < q) (R : ℕ)
    (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    (x 0).val < 12 * (R * q) + 16 * q := by
  have h := (x 0).isLt
  simpa only [dil_fine_size hq, ↓reduceIte] using h

theorem dil_admissible {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) :
    Admissible 2 (2*q) R 1 (dilTower q R) := by
  have hp : 4*q ∣ 2*(R*q)+4*q := by
    obtain ⟨t, rfl⟩ := hR; exact ⟨t+1, by ring⟩
  have hq' : 4*q ∣ 10*(R*q)+12*q := by
    obtain ⟨t, rfl⟩ := hR; exact ⟨5*t+3, by ring⟩
  have hlo : 2*q ∣ 4*q := ⟨2, by ring⟩
  have hhi : 2*q ∣ 12*(R*q)+12*q := ⟨6*R+6, by ring⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    by_cases h0 : j = 0
    · subst j
      change (2*(R*q)+4*q ≤ (x 0).val ∧ (x 0).val < 10*(R*q)+12*q) at hx
      change 4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q
      omega
    · simp [dilTower, h0] at hx
  · intro j hj
    simp [dilTower, show j ≠ 0 by omega, show j ≠ 1 by omega]
  · intro j hj μ
    rw [dil_fine_size hq]
    interval_cases j <;> by_cases hμ : μ = 0 <;> simp only [bigSide, pow_zero, pow_one, mul_one, hμ, ↓reduceIte]
    · exact ⟨6*R+8, by ring⟩
    · exact ⟨4, by ring⟩
    · exact ⟨3*R+4, by ring⟩
    · exact ⟨2, by ring⟩
  · intro j hj x hx y hy
    interval_cases j
    · change (4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q) at hx
      change 4*q ≤ (y 0).val ∧ (y 0).val < 12*(R*q)+12*q
      apply iv_block (by omega : 0 < 2*q) hlo hhi _ hx
      simpa [bigSide] using hy 0
    · change (2*(R*q)+4*q ≤ (x 0).val ∧ (x 0).val < 10*(R*q)+12*q) at hx
      change 2*(R*q)+4*q ≤ (y 0).val ∧ (y 0).val < 10*(R*q)+12*q
      apply iv_block (by omega : 0 < 4*q) hp hq' _ hx
      simpa [bigSide, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hy 0
  · intro j hj x hx y hy
    interval_cases j
    · change ¬ (4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q) at hx
      change (2*(R*q)+4*q ≤ (y 0).val ∧ (y 0).val < 10*(R*q)+12*q) at hy
      have hxb := dil_fine_bound hq R x
      have hpd := zero_coord_le_pdist x y
      simp only [dil_fine_size hq, ↓reduceIte] at hpd
      have hcoord : 2*(R*q) < pcd (12*(R*q)+16*q) (x 0).val (y 0).val := by
        unfold pcd; split_ifs <;> omega
      have heq : R * bigSide (2*q) 2 0 = 2*(R*q) := by simp [bigSide]; ring
      rw [heq]; exact lt_of_lt_of_le hcoord hpd
    · simp [dilTower] at hy
  · intro x
    change (4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q) ↔ _
    have hrm : R*(2*q) = 2*(R*q) := by ring
    constructor
    · intro hx
      let v := if (x 0).val < 2*(R*q)+4*q then 2*(R*q)+4*q
        else if (x 0).val < 10*(R*q)+12*q then (x 0).val else 10*(R*q)+12*q-1
      have hv : v < scaleUp 2 1 (dilLu q R) 0 + 1 := by
        rw [dil_fine_size hq, if_pos rfl]
        dsimp [v]; split_ifs <;> omega
      refine ⟨Function.update x 0 ⟨v, hv⟩, ?_, x, fun μ => rfl, ?_⟩
      · change 2*(R*q)+4*q ≤ v ∧ v < 10*(R*q)+12*q
        dsimp [v]; split_ifs <;> omega
      · unfold pdist
        rw [Finset.sum_eq_single (0 : Fin 3)]
        · simp only [Function.update_self, dil_fine_size hq, ↓reduceIte, hrm]
          have hc := pcd_clamp (N := 12*(R*q)+16*q) (a := (x 0).val)
            (lo := 2*(R*q)+4*q) (hi := 10*(R*q)+12*q) (D := 2*(R*q))
            (by omega) (by omega) (dil_fine_bound hq R x) (by omega)
          simpa [v] using hc
        · intro μ _ hμ; rw [Function.update_of_ne hμ, pcd_self']
        · intro h; exact (h (Finset.mem_univ _)).elim
    · rintro ⟨y, hy, z, hz, hd⟩
      change (2*(R*q)+4*q ≤ (y 0).val ∧ (y 0).val < 10*(R*q)+12*q) at hy
      have hcoord := le_trans (zero_coord_le_pdist z y) hd
      simp only [dil_fine_size hq, ↓reduceIte, hrm] at hcoord
      have hn := pcd_near (dil_fine_bound hq R z) hy
        (show 2*(R*q) ≤ 2*(R*q)+4*q by omega)
        (show 10*(R*q)+12*q+2*(R*q) ≤ 12*(R*q)+16*q by omega) hcoord
      have hzmem : 4*q ≤ (z 0).val ∧ (z 0).val < 12*(R*q)+12*q := by omega
      exact iv_block (by omega : 0 < 2*q) hlo hhi (hz 0).symm hzmem

theorem dil_shift_zero {q : ℕ} (hq : 0 < q) (R : ℕ)
    (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (μ : Fin 3) :
    ((periodicLatticeShift x μ) 0).val =
      if μ = 0 then ((x 0).val+1) % (12*(R*q)+16*q) else (x 0).val := by
  by_cases h : μ = 0
  · subst μ
    simp only [periodicLatticeShift, Function.update_self, Fin.val_add, Fin.val_one',
      dil_fine_size hq, ↓reduceIte]
    rw [Nat.mod_eq_of_lt (by omega : 1 < 12*(R*q)+16*q)]
  · simp [periodicLatticeShift, Function.update_of_ne (Ne.symm h), h]


#print axioms dil_admissible
end AdalyFormal.Round4.Guarded.RefuteR1

namespace AdalyFormal.Round5.Guarded.IVTR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.D1Literal (BdPt)
def rightSite {q : ℕ} (hq : 0 < q) (R : ℕ) :
    PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) :=
  fun μ => ⟨if μ = 0 then 12*(R*q)+12*q-1 else 0,
    by rw [dil_fine_size hq]; split_ifs <;> omega⟩

theorem rightSite_bd {q : ℕ} (hq : 0 < q) (R : ℕ) :
    BdPt ((dilTower q R).Om 0) (rightSite hq R) := by
  have hv : ((rightSite hq R) 0).val = 12*(R*q)+12*q-1 := by simp [rightSite]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 4*q ≤ _ ∧ _ < 12*(R*q)+12*q
    rw [hv]; omega
  · change ¬ (4*q ≤ _ ∧ _ < 12*(R*q)+12*q)
    rw [dil_shift_zero hq R, if_pos rfl, hv, Nat.mod_eq_of_lt (by omega)]
    omega
  · intro z ν hν
    change (4*q ≤ _ ∧ _ < 12*(R*q)+12*q) ↔ (4*q ≤ _ ∧ _ < 12*(R*q)+12*q)
    rw [dil_shift_zero hq R, if_neg hν]
  · intro ν heq
    have hn : 1 < scaleUp 2 1 (dilLu q R) ν + 1 := by
      rw [dil_fine_size hq]; split_ifs <;> omega
    have hh := congrArg (fun y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) => (y ν).val) heq
    simp only [periodicLatticeShift, Function.update_self, Fin.val_add, Fin.val_one'] at hh
    rw [Nat.mod_eq_of_lt hn] at hh
    have hw := ((rightSite hq R) ν).isLt
    rcases Nat.lt_or_ge (((rightSite hq R) ν).val+1) (scaleUp 2 1 (dilLu q R) ν+1) with h | h
    · rw [Nat.mod_eq_of_lt h] at hh; omega
    · have he : ((rightSite hq R) ν).val+1 = scaleUp 2 1 (dilLu q R) ν+1 := by omega
      rw [he, Nat.mod_self] at hh; omega


#print axioms rightSite_bd
end AdalyFormal.Round5.Guarded.IVTR2

namespace AdalyFormal.Round12.Noncancel.RightFamily
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2 (AnFam)
open AdalyFormal.Round12.Noncancel.Path

/-- One consistently chosen family: the right exterior star, never reflected from a left computation. -/
def rightStar {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  starPath (periodicLatticeShift (rightSite hq R) 0)

theorem rightStar_zero {q : ℕ} (hq : 0 < q) (R : ℕ) :
    rightStar hq R 0 = fun _ => 1 := starPath_zero _

theorem rightStar_cont {q : ℕ} (hq : 0 < q) (R : ℕ) :
    AdalyFormal.D1Literal.ContFam (rightStar hq R) := starPath_cont _

theorem rightStar_an {q : ℕ} (hq : 0 < q) (R : ℕ) :
    AnFam (rightStar hq R) := starPath_an _

theorem rightStar_off_exterior {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ)
    (e : Bond (scaleUp 2 1 (dilLu q R)))
    (he : e ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)) :
    rightStar hq R t e = 1 :=
  starPath_off_exterior _ _ (rightSite_bd hq R).hx' (rightSite_bd hq R).trans t e he

/-- The exterior masking in the ORIGINAL pathU is exactly transparent to this star. -/
theorem pathU_rightStar {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    pathU q R (rightStar hq R) f 0 t = rightStar hq R t := by
  classical
  funext e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp [pathU,maskedU,he]
  · rw [rightStar_off_exterior hq R t e he]
    simp [pathU,maskedU,he,Ug_zero]

theorem dilU_rightStar {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ) :
    dilU q R 0 (rightStar hq R t) = rightStar hq R t := by
  classical
  funext e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp [dilU,he]
  · rw [rightStar_off_exterior hq R t e he]
    simp [dilU,he,Ug_zero]

/-- Exact equality with the original vacuum carrier, not just a same-shaped matrix. -/
theorem vacA_rightStar {q : ℕ} (hq : 0 < q) (R : ℕ) (a t : ℝ) :
    vacA q R (rightStar hq R) a t =
      (AdalyFormal.D1Literal.dataS AdalyFormal.D1Literal.selAll AdalyFormal.D1Literal.selAll
        (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
          (rightStar hq R t) a (dilLam q R))).Ginv := by
  unfold vacA pathA pathP
  rw [pathU_rightStar]
  rfl

/-- Actual negative pi endpoint for EVERY positive scale and even radius >=18. -/
theorem rightStar_negative {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    ∃ w, ⟪w, vacA q R (rightStar hq R) 1 Real.pi w⟫ < 0 := by
  rw [vacA_rightStar]
  exact star_negative_endpoint (by norm_num) (dilTower q R) (dilLam q R) 1
    (dil_admissible hq hR) (by norm_num) (by nlinarith)
    (rightSite_bd hq R) (by norm_num) (by norm_num) suTwoWitness suTwoWitness_ne_zero

/-- The nested dyadic/even quantifiers and ALL path-validity clauses are now
proved for this right-star family. Response noncancellation is deliberately absent. -/
theorem cofinal_rightStar_paths :
    ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
      ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)),
        AdalyFormal.D1Literal.ContFam V ∧ AnFam V ∧ V 0 = (fun _ => 1) ∧
        (∃ w, ⟪w, vacA (2^j) R V 1 Real.pi w⟫ < 0) := by
  intro j₀
  refine ⟨j₀,le_rfl,?_⟩
  intro R₀
  let R := 2*(R₀+18)
  have hR : 2 ∣ R := dvd_mul_right _ _
  have hR18 : 18 ≤ R := by dsimp [R]; omega
  have hq : 0 < 2^j₀ := by positivity
  exact ⟨R,by dsimp [R]; omega,hR,hR18,rightStar hq R,
    rightStar_cont hq R,rightStar_an hq R,rightStar_zero hq R,
    rightStar_negative hq hR hR18⟩

#print axioms rightStar
#print axioms rightStar_zero
#print axioms rightStar_cont
#print axioms rightStar_an
#print axioms rightStar_off_exterior
#print axioms pathU_rightStar
#print axioms dilU_rightStar
#print axioms vacA_rightStar
#print axioms rightStar_negative
#print axioms cofinal_rightStar_paths
end AdalyFormal.Round12.Noncancel.RightFamily

namespace AdalyFormal.Round13.Positivity.Leaves
open Classical
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.Mass

/-- Four normal neighbors and four tangents, in the actual fine periodic lattice. -/
def leaf {q : ℕ} (hq : 0 < q) (R : ℕ) : Fin 8 → Bond (scaleUp 2 1 (dilLu q R)) :=
  ![(periodicLatticeShift (rightSite hq R) 1,0),
    (periodicLatticeShiftBack (rightSite hq R) 1,0),
    (periodicLatticeShift (rightSite hq R) 2,0),
    (periodicLatticeShiftBack (rightSite hq R) 2,0),
    (rightSite hq R,1),
    (periodicLatticeShiftBack (rightSite hq R) 1,1),
    (rightSite hq R,2),
    (periodicLatticeShiftBack (rightSite hq R) 2,2)]

def code {L : PeriodicLatticeExtent} (e : Bond L) : ℕ × ℕ × ℕ :=
  (e.2.val,(e.1 1).val,(e.1 2).val)

private theorem transverse_sizes {q : ℕ} (hq : 0 < q) (R : ℕ) :
    (scaleUp 2 1 (dilLu q R) 1 + 1 = 8*q) ∧
    (scaleUp 2 1 (dilLu q R) 2 + 1 = 8*q) := by
  constructor <;> simp [dil_fine_size hq]

private theorem right_coord {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ((rightSite hq R) 1).val = 0 ∧ ((rightSite hq R) 2).val = 0 := by
  simp [rightSite]

/-- No numerical lattice assumption: all eight exact codes at every positive q. -/
theorem leaf_code {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 8) :
    code (leaf hq R i) =
      ![(0,1,0),(0,8*q-1,0),(0,0,1),(0,0,8*q-1),
        (1,0,0),(1,8*q-1,0),(2,0,0),(2,0,8*q-1)] i := by
  have hs := transverse_sizes hq R
  have hz := right_coord hq R
  fin_cases i <;>
    simp [leaf,code,periodicLatticeShift,periodicLatticeShiftBack,
      Fin.val_add,Fin.val_sub,hz.1,hz.2,hs.1,hs.2,
      Nat.mod_eq_of_lt (show 1 < 8*q by omega),
      Nat.mod_eq_of_lt (show 8*q-1 < 8*q by omega)]

/-- Eight distinct physical bonds, not an indexed multiset recycling leaf mass. -/
theorem leaf_injective {q : ℕ} (hq : 0 < q) (R : ℕ) : Function.Injective (leaf hq R) := by
  intro i j h
  have hc := congrArg code h
  rw [leaf_code hq R i,leaf_code hq R j] at hc
  clear h
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals norm_num at hc
  all_goals omega

/-- Every leaf starts at the rightmost interior coordinate. -/
theorem leaf_zero_coord {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 8) :
    (((leaf hq R i).1) 0).val = 12*(R*q)+12*q-1 := by
  fin_cases i <;> simp [leaf,periodicLatticeShift,periodicLatticeShiftBack,rightSite]

/-- The second endpoint is at most one step further in the normal direction. -/
theorem leaf_end_zero_coord {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 8) :
    ((periodicLatticeShift (leaf hq R i).1 (leaf hq R i).2) 0).val =
      if i.val < 4 then 12*(R*q)+12*q else 12*(R*q)+12*q-1 := by
  rw [dil_shift_zero hq R, leaf_zero_coord]
  have hf : (12*(R*q)+12*q-1+1) % (12*(R*q)+16*q) = 12*(R*q)+12*q := by
    rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt (by omega)]
  fin_cases i <;> simp [leaf,hf]

/-- Both endpoints avoid Omega_1, uniformly at every radius at least one. -/
theorem leaf_collar {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) (i : Fin 8) :
    (leaf hq R i).1 ∉ (dilTower q R).Om 1 ∧
    periodicLatticeShift (leaf hq R i).1 (leaf hq R i).2 ∉ (dilTower q R).Om 1 := by
  have hprod : 1 ≤ R*q := by nlinarith
  constructor
  · change ¬ (2*(R*q)+4*q ≤ _ ∧ _ < 10*(R*q)+12*q)
    rw [leaf_zero_coord]
    omega
  · change ¬ (2*(R*q)+4*q ≤ _ ∧ _ < 10*(R*q)+12*q)
    rw [leaf_end_zero_coord]
    split_ifs <;> omega

/-- Every leaf is a touching carrier bond; its initial site is in Omega_0. -/
theorem leaf_touching {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 8) :
    leaf hq R i ∈ bondsOm0 (geomOf 2 1 (dilTower q R)) := by
  apply Or.inl
  change 4*q ≤ _ ∧ _ < 12*(R*q)+12*q
  rw [leaf_zero_coord]
  omega

/-- All eight actual rows have the genuine level-zero mass weight one. -/
theorem leaf_level_zero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR1 : 1 ≤ R)
    (i : Fin 8) : leaf hq R i ∈ bondsLam (geomOf 2 1 (dilTower q R)) 0 :=
  collar_levelZero (dil_admissible hq hR) (by norm_num) _
    (leaf_touching hq R i) (leaf_collar hq hR1 i).1 (leaf_collar hq hR1 i).2

/-- The eight-row set, with no multiplicities. -/
def leafSet {q : ℕ} (hq : 0 < q) (R : ℕ) : Finset (Bond (scaleUp 2 1 (dilLu q R))) :=
  Finset.univ.image (leaf hq R)

theorem leafSet_card {q : ℕ} (hq : 0 < q) (R : ℕ) : (leafSet hq R).card = 8 := by
  rw [leafSet,Finset.card_image_of_injective _ (leaf_injective hq R)]
  simp

open scoped RealInnerProductSpace in
/-- Unconditional physical eight-leaf mass extraction for this exact right star's
geometry, with an arbitrary background and an arbitrary full fine input. -/
theorem eight_leaf_mass {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR1 : 1 ≤ R)
    (U : Cfg (scaleUp 2 1 (dilLu q R)))
    (A : AdalyFormal.Balaban.CovariantOperators.BondFnL2 (scaleUp 2 1 (dilLu q R))) :
    (∑ i : Fin 8, ‖A (leaf hq R i)‖^2) ≤
      ⟪A,MassFull (geomOf 2 1 (dilTower q R)) 1
        (bondSectorOf (geomOf 2 1 (dilTower q R)) U) A⟫ := by
  have hh := leaf_mass_le (geomOf 2 1 (dilTower q R)) U 1 (by norm_num)
    (leafSet hq R) (by
      intro e he
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      exact leaf_level_zero hq hR hR1 i) A
  simpa only [one_mul,leafSet,
    Finset.sum_image (fun i _ j _ h => leaf_injective hq R h)] using hh

set_option pp.fullNames true
#print axioms leaf_code
#print axioms leaf_injective
#print axioms leaf_zero_coord
#print axioms leaf_end_zero_coord
#print axioms leaf_collar
#print axioms leaf_touching
#print axioms leaf_level_zero
#print axioms leafSet_card
#print axioms eight_leaf_mass
end AdalyFormal.Round13.Positivity.Leaves

namespace AdalyFormal.Round13.Positivity.Physical
open Classical
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLaneR6
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift)
open AdalyFormal.Round12.Noncancel.Path
open AdalyFormal.Round12.Noncancel.Plaquette
open AdalyFormal.Round12.Noncancel.FullPlaquette
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round13.Positivity.Leaves
variable {L : PeriodicLatticeExtent}

/-- Two exterior normal layers; transverse shifts preserve this property. -/
def exteriorPair (Om : Set (PeriodicLatticeSite L)) (z : PeriodicLatticeSite L) : Prop :=
  z ∉ Om ∧ periodicLatticeShift z 0 ∉ Om

theorem exteriorPair_shift {Om : Set (PeriodicLatticeSite L)} {x z : PeriodicLatticeSite L}
    (hb : BdPt Om x) (hz : exteriorPair Om z) {ν : Fin 3} (hν : ν ≠ 0) :
    exteriorPair Om (periodicLatticeShift z ν) := by
  constructor
  · exact fun h => hz.1 ((hb.trans z ν hν).mp h)
  · rw [shift_comm z hν]
    exact fun h => hz.2 ((hb.trans _ ν hν).mp h)

theorem exteriorPair_back {Om : Set (PeriodicLatticeSite L)} {x z : PeriodicLatticeSite L}
    (hb : BdPt Om x) (hz : exteriorPair Om z) {ν : Fin 3} (hν : ν ≠ 0) :
    exteriorPair Om (periodicLatticeShiftBack z ν) := by
  have hz0 : periodicLatticeShiftBack z ν ∉ Om := by
    intro h
    exact hz.1 (by simpa only [periodicLatticeShift_shiftBack] using
      (hb.trans _ ν hν).mpr h)
  refine ⟨hz0, ?_⟩
  intro h
  have hh := (hb.trans _ ν hν).mpr h
  rw [shift_comm _ (Ne.symm hν), periodicLatticeShift_shiftBack] at hh
  exact hz.2 hh

/-- Any plaquette based on two exterior layers has four exterior vertices. -/
theorem exteriorPair_vertices {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hb : BdPt Om x) (p : PeriodicLatticePlaquette L) (hp : exteriorPair Om p.1) :
    ∀ e ∈ periodicPlaquetteBoundaryEdges p,
      e.1 ∉ Om ∧ periodicLatticeShift e.1 e.2 ∉ Om := by
  have hν : p.2.1.2 ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) p.2.2)
  have hμ : periodicLatticeShift p.1 p.2.1.1 ∉ Om := by
    by_cases h : p.2.1.1 = 0
    · simpa only [h] using hp.2
    · exact (exteriorPair_shift hb hp h).1
  have hμν : periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2 ∉ Om :=
    fun h => hμ ((hb.trans _ _ hν).mp h)
  have hν' := (exteriorPair_shift hb hp hν).1
  intro e he
  rcases (edge_mem p e).mp he with rfl | rfl | rfl | rfl
  · exact ⟨hp.1,hμ⟩
  · exact ⟨hμ,hμν⟩
  · refine ⟨hν', ?_⟩
    rw [shift_comm _ (ne_of_gt p.2.2)]
    exact hμν
  · exact ⟨hp.1,hν'⟩

/-- A curved plaquette touching the star is either one of its FOUR arms or is
entirely exterior. The latter may be curved, but its supported input is zero. -/
theorem star_edge_cases {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hb : BdPt Om x) (hf : periodicLatticeShift (periodicLatticeShift x 0) 0 ∉ Om)
    (p : PeriodicLatticePlaquette L) (e : Bond L)
    (he : e ∈ periodicPlaquetteBoundaryEdges p)
    (hs : e ∈ starLinks (periodicLatticeShift x 0)) :
    (∃ ν : {ν : Fin 3 // 0 < ν}, p = P1 x ν ∨ p = P2 x ν) ∨
      exteriorPair Om p.1 := by
  have hx : exteriorPair Om (periodicLatticeShift x 0) := ⟨hb.hx',hf⟩
  have hsites : e.1 = periodicLatticeShift x 0 ∨
      e.1 = periodicLatticeShiftBack (periodicLatticeShift x 0) e.2 := by
    rcases hs.2 with h | h
    · exact Or.inl h
    · right
      have := congrArg (fun z => periodicLatticeShiftBack z e.2) h
      simpa only [periodicLatticeShiftBack_shift] using this
  have hext : exteriorPair Om e.1 := by
    rcases hsites with h | h
    · rw [h]; exact hx
    · rw [h]; exact exteriorPair_back hb hx hs.1
  rcases (edge_mem p e).mp he with he | he | he | he
  · right
    have hsite := congrArg Prod.fst he
    simpa only [hsite] using hext
  · have hsite := congrArg Prod.fst he
    have hdir := congrArg Prod.snd he
    by_cases hμ : p.2.1.1 = 0
    · left
      have hν : 0 < p.2.1.2 := lt_of_le_of_lt (Fin.zero_le _) p.2.2
      refine ⟨⟨p.2.1.2,hν⟩, ?_⟩
      have hh : periodicLatticeShift p.1 0 = e.1 := by simpa only [hμ] using hsite.symm
      rcases hsites with hx | hx
      · left
        have hbase : p.1 = x := by
          have := congrArg (fun z => periodicLatticeShiftBack z 0) (hh.trans hx)
          simpa only [periodicLatticeShiftBack_shift] using this
        apply Prod.ext hbase
        apply Subtype.ext
        exact Prod.ext hμ rfl
      · right
        have hscomm : periodicLatticeShiftBack (periodicLatticeShift x 0) p.2.1.2 =
            periodicLatticeShift (periodicLatticeShiftBack x p.2.1.2) 0 := by
          have hh : periodicLatticeShift
              (periodicLatticeShift (periodicLatticeShiftBack x p.2.1.2) 0) p.2.1.2 =
              periodicLatticeShift x 0 := by
            rw [shift_comm _ (Ne.symm (ne_of_gt hν)), periodicLatticeShift_shiftBack]
          have := congrArg (fun z => periodicLatticeShiftBack z p.2.1.2) hh
          simpa only [periodicLatticeShiftBack_shift] using this.symm
        rw [hdir,hscomm] at hx
        have hbase : p.1 = periodicLatticeShiftBack x p.2.1.2 := by
          have := congrArg (fun z => periodicLatticeShiftBack z 0) (hh.trans hx)
          simpa only [periodicLatticeShiftBack_shift] using this
        apply Prod.ext hbase
        apply Subtype.ext
        exact Prod.ext hμ rfl
    · right
      have hh := exteriorPair_back hb hext hμ
      simpa only [hsite,periodicLatticeShiftBack_shift] using hh
  · right
    have hsite := congrArg Prod.fst he
    have hν : p.2.1.2 ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) p.2.2)
    have hh := exteriorPair_back hb hext hν
    simpa only [hsite,periodicLatticeShiftBack_shift] using hh
  · right
    have hsite := congrArg Prod.fst he
    simpa only [hsite] using hext

end AdalyFormal.Round13.Positivity.Physical
#print axioms AdalyFormal.Round13.Positivity.Physical.exteriorPair
#print axioms AdalyFormal.Round13.Positivity.Physical.exteriorPair_shift
#print axioms AdalyFormal.Round13.Positivity.Physical.exteriorPair_back
#print axioms AdalyFormal.Round13.Positivity.Physical.exteriorPair_vertices
#print axioms AdalyFormal.Round13.Positivity.Physical.star_edge_cases

namespace AdalyFormal.Round13.Positivity.Physical
open Classical
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLaneR6
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift)
open AdalyFormal.Round12.Noncancel.Path
open AdalyFormal.Round12.Noncancel.Plaquette
open AdalyFormal.Round12.Noncancel.FullPlaquette
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round13.Positivity.Leaves
variable {L : PeriodicLatticeExtent}

theorem plaqEnergy_zero_input (U : Cfg L) (A : BondFnL2 L)
    (p : PeriodicLatticePlaquette L)
    (hz : ∀ e ∈ periodicPlaquetteBoundaryEdges p, A e = 0) : plaqEnergy U A p = 0 := by
  rw [plaqEnergy_congr_field U A 0 p (by simpa using hz)]
  simp [plaqEnergy, curlValueCovariant]

theorem hol_flat_components (U : Cfg L) (p : PeriodicLatticePlaquette L)
    (h : holonomyElem U p = 1) : reHolonomy U p = 1 ∧ imHolonomy U p = 0 := by
  constructor
  · simp [reHolonomy,holonomyElemInv,h]
    ext i j
    by_cases hij : i=j <;> norm_num [Matrix.one_apply,hij]
  · simp [imHolonomy,holonomyElemInv,h]

theorem plaqEnergy_nonneg_links (U : Cfg L) (A : BondFnL2 L)
    (p : PeriodicLatticePlaquette L)
    (hU : ∀ e ∈ periodicPlaquetteBoundaryEdges p, U e = 1) : 0 ≤ plaqEnergy U A p := by
  have hh : holonomyElem U p = 1 := by
    unfold holonomyElem periodicPlaquetteHolonomy
    dsimp only
    rw [hU _ ((edge_mem p _).mpr (Or.inl rfl)),
      hU _ ((edge_mem p _).mpr (Or.inr (Or.inl rfl))),
      hU _ ((edge_mem p _).mpr (Or.inr (Or.inr (Or.inl rfl)))),
      hU _ ((edge_mem p _).mpr (Or.inr (Or.inr (Or.inr rfl))))]
    simp
  exact plaqEnergy_nonneg U A p (hol_flat_components U p hh).1 (hol_flat_components U p hh).2

/-- The ENTIRE non-star remainder is nonnegative on the true touching space. -/
theorem nonstar_nonneg {G : TowerGeom L} {x : PeriodicLatticeSite L}
    (hb : BdPt G.Om0 x) (hf : periodicLatticeShift (periodicLatticeShift x 0) 0 ∉ G.Om0)
    (t : ℝ) (u : ↥(bondSupp G)) (p : PeriodicLatticePlaquette L)
    (hnot : ∀ ν : {ν : Fin 3 // 0 < ν}, p ≠ P1 x ν ∧ p ≠ P2 x ν) :
    0 ≤ plaqEnergy (starPath (periodicLatticeShift x 0) t) (iE G u) p := by
  by_cases he : ∃ e ∈ periodicPlaquetteBoundaryEdges p, e ∈ starLinks (periodicLatticeShift x 0)
  · obtain ⟨e,he,hs⟩ := he
    rcases star_edge_cases hb hf p e he hs with ⟨ν,h | h⟩ | hp
    · exact False.elim ((hnot ν).1 h)
    · exact False.elim ((hnot ν).2 h)
    · rw [plaqEnergy_zero_input]
      intro e he
      have hz := exteriorPair_vertices hb p hp e he
      exact u.property e (fun h => h.elim hz.1 hz.2)
  · apply plaqEnergy_nonneg_links
    intro e he'
    have hs : e ∉ starLinks (periodicLatticeShift x 0) := fun hs => he ⟨e,he',hs⟩
    simp [starPath,hs]

/-- The second exterior normal layer does not wrap into the slab. -/
theorem right_forward_out {q : ℕ} (hq : 0 < q) (R : ℕ) :
    periodicLatticeShift (periodicLatticeShift (rightSite hq R) 0) 0 ∉ (dilTower q R).Om 0 := by
  change ¬ (4*q ≤ _ ∧ _ < 12*(R*q)+12*q)
  have hcoord : ((rightSite hq R) 0).val = 12*(R*q)+12*q-1 := by simp [rightSite]
  simp only [dil_shift_zero hq R,hcoord,ite_true]
  have ha : 12*(R*q)+12*q-1+1 = 12*(R*q)+12*q := Nat.sub_add_cancel (by omega)
  have hb : (12*(R*q)+12*q) % (12*(R*q)+16*q) = 12*(R*q)+12*q :=
    Nat.mod_eq_of_lt (by omega)
  have hc : (12*(R*q)+12*q+1) % (12*(R*q)+16*q) = 12*(R*q)+12*q+1 :=
    Nat.mod_eq_of_lt (by omega)
  rw [ha,hb,hc]
  omega

theorem hol_phase_components (U : Cfg L) (p : PeriodicLatticePlaquette L) (t : ℝ)
    (hh : holonomyElem U p = uθ t) :
    reHolonomy U p = realHol (Real.cos t) ∧ imHolonomy U p = imagHol (Real.sin t) := by
  have hinv : (holonomyElemInv U p : Matrix (Fin 2) (Fin 2) ℂ) = star (uMat t) := by
    change star (holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [hh]
    rfl
  have hcoe : (holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) = uMat t := by rw [hh]; rfl
  have hexp (r : ℝ) : Complex.exp ((r : ℂ)*Complex.I) =
      (Real.cos r : ℂ) + (Real.sin r : ℂ)*Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hneg : Complex.exp (-((t : ℂ)*Complex.I)) =
      (Real.cos t : ℂ) - (Real.sin t : ℂ)*Complex.I := by
    rw [← neg_mul, ← Complex.ofReal_neg,hexp]
    simp [Real.cos_neg,Real.sin_neg,sub_eq_add_neg]
  simp only [reHolonomy, imHolonomy, hcoe,hinv]
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [uMat,realHol,imagHol,Matrix.star_apply,hexp,hneg,
      Complex.ext_iff] <;> ring

theorem norm_coordinates (X : SuTwo) :
    Complex.normSq ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 1) +
      (((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im)^2 = ‖X‖^2 := by
  rw [← real_inner_self_eq_norm_sq]
  exact (full_inner X _ _ (lieMat_coordinates X)).symm

/-- The local lower bound in genuine SuTwo norms, with neutral center retained. -/
theorem right_first_norm_lower (U : Cfg L) (A : BondFnL2 L)
    (p : PeriodicLatticePlaquette L) (t : ℝ) (ht : 0 ≤ Real.cos t)
    (X Y Z : SuTwo) (hX : (X : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0)
    (hh : holonomyElem U p = uθ t)
    (h1 : a1LM U p (WithLp.ofLp A) = (X : Matrix (Fin 2) (Fin 2) ℂ))
    (h2 : a2LM p (WithLp.ofLp A) = (Y : Matrix (Fin 2) (Fin 2) ℂ))
    (h3 : a3LM p (WithLp.ofLp A) = (Z : Matrix (Fin 2) (Fin 2) ℂ))
    (h4 : a4LM U p (WithLp.ofLp A) = 0) :
    -(1-Real.cos t)*(‖Y‖^2+‖Z‖^2) ≤ plaqEnergy U A p := by
  have hx := lieMat_coordinates X
  rw [hX] at hx
  have hh' := hol_phase_components U p t hh
  have hp := frozen_right_zero_first_lower U A p (Real.cos t) (Real.sin t)
    _ _ _ _ _ ht (Real.cos_le_one t) (by nlinarith [Real.sin_sq_add_cos_sq t])
    hh'.1 hh'.2 (h1.trans hx) (h2.trans (lieMat_coordinates Y))
    (h3.trans (lieMat_coordinates Z)) h4
  simpa only [norm_coordinates] using hp

theorem right_third_norm_lower (U : Cfg L) (A : BondFnL2 L)
    (p : PeriodicLatticePlaquette L) (t : ℝ) (ht : 0 ≤ Real.cos t)
    (X Y Z : SuTwo) (hZ : (Z : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0)
    (hh : holonomyElem U p = uθ t)
    (h1 : a1LM U p (WithLp.ofLp A) = (X : Matrix (Fin 2) (Fin 2) ℂ))
    (h2 : a2LM p (WithLp.ofLp A) = (Y : Matrix (Fin 2) (Fin 2) ℂ))
    (h3 : a3LM p (WithLp.ofLp A) = (Z : Matrix (Fin 2) (Fin 2) ℂ))
    (h4 : a4LM U p (WithLp.ofLp A) = 0) :
    -(1-Real.cos t)*(‖X‖^2+‖Y‖^2) ≤ plaqEnergy U A p := by
  have hz := lieMat_coordinates Z
  rw [hZ] at hz
  have hh' := hol_phase_components U p t hh
  have hp := frozen_right_zero_third_lower U A p (Real.cos t) (Real.sin t)
    _ _ _ _ _ ht (Real.cos_le_one t) (by nlinarith [Real.sin_sq_add_cos_sq t])
    hh'.1 hh'.2 (h1.trans (lieMat_coordinates X)) (h2.trans (lieMat_coordinates Y))
    (h3.trans hz) h4
  simpa only [norm_coordinates] using hp
end AdalyFormal.Round13.Positivity.Physical
#print axioms AdalyFormal.Round13.Positivity.Physical.hol_flat_components
#print axioms AdalyFormal.Round13.Positivity.Physical.plaqEnergy_nonneg_links
#print axioms AdalyFormal.Round13.Positivity.Physical.norm_coordinates
#print axioms AdalyFormal.Round13.Positivity.Physical.plaqEnergy_zero_input
#print axioms AdalyFormal.Round13.Positivity.Physical.nonstar_nonneg
#print axioms AdalyFormal.Round13.Positivity.Physical.right_forward_out
#print axioms AdalyFormal.Round13.Positivity.Physical.hol_phase_components
#print axioms AdalyFormal.Round13.Positivity.Physical.right_first_norm_lower
#print axioms AdalyFormal.Round13.Positivity.Physical.right_third_norm_lower

namespace AdalyFormal.Round13.Positivity.Physical
open Classical
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLaneR6
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant RMap_one)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift)
open AdalyFormal.Round12.Noncancel.Path
open AdalyFormal.Round12.Noncancel.Plaquette
open AdalyFormal.Round12.Noncancel.FullPlaquette
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round13.Positivity.Leaves
variable {L : PeriodicLatticeExtent}

/-- Atom order P1 = (-normal-neighbor,-tangent,central,0). -/
theorem arm1_lower {G : TowerGeom L} {x : PeriodicLatticeSite L}
    (hb : BdPt G.Om0 x) (t : ℝ) (ht : 0 ≤ Real.cos t) (u : ↥(bondSupp G))
    (hu : (((iE G u) (x,0) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0)
    (ν : {ν : Fin 3 // 0 < ν}) :
    -(1-Real.cos t)*(‖(iE G u) (periodicLatticeShift x ν.1,0)‖^2 +
      ‖(iE G u) (x,ν.1)‖^2) ≤
    plaqEnergy (starPath (periodicLatticeShift x 0) t) (iE G u) (P1 x ν) := by
  let A := iE G u
  let U := starPath (periodicLatticeShift x 0) t
  have hU : U (x,ν.1) = 1 := starPath_interior _ _ hb.hx' hb.trans t _ hb.hx
  have hzero : A (periodicLatticeShift x 0,ν.1) = 0 := by
    apply u.property
    intro h
    rcases h with h | h
    · exact hb.hx' h
    · exact hb.hx' ((hb.trans _ ν.1 (ne_of_gt ν.2)).mp h)
  have h := right_third_norm_lower U A (P1 x ν) t ht
    (-A (periodicLatticeShift x ν.1,0)) (-A (x,ν.1)) (A (x,0)) hu
    (star_holonomy1 hb t ν)
    (by simp [a1LM_apply,AprimeZW,AdalyFormal.D1Literal.P1,hU,RMap_one])
    (by rfl) (by rfl)
    (by simp [a4LM_apply,AprimeYZ,AdalyFormal.D1Literal.P1,hzero])
  simpa only [norm_neg] using h

/-- Atom order P2 = (-central,-back-tangent,back-normal,0). -/
theorem arm2_lower {G : TowerGeom L} {x : PeriodicLatticeSite L}
    (hb : BdPt G.Om0 x) (t : ℝ) (ht : 0 ≤ Real.cos t) (u : ↥(bondSupp G))
    (hu : (((iE G u) (x,0) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0)
    (ν : {ν : Fin 3 // 0 < ν}) :
    -(1-Real.cos t)*(‖(iE G u) (periodicLatticeShiftBack x ν.1,0)‖^2 +
      ‖(iE G u) (periodicLatticeShiftBack x ν.1,ν.1)‖^2) ≤
    plaqEnergy (starPath (periodicLatticeShift x 0) t) (iE G u) (P2 x ν) := by
  let A := iE G u
  let U := starPath (periodicLatticeShift x 0) t
  have hU : U (periodicLatticeShiftBack x ν.1,ν.1) = 1 :=
    starPath_interior _ _ hb.hx' hb.trans t _ (hb.shiftBack_mem ν)
  have hsh : periodicLatticeShift (periodicLatticeShift (periodicLatticeShiftBack x ν.1) 0) ν.1 =
      periodicLatticeShift x 0 := by
    rw [shift_comm _ (Ne.symm (ne_of_gt ν.2)),periodicLatticeShift_shiftBack]
  have hzero : A (periodicLatticeShift (periodicLatticeShiftBack x ν.1) 0,ν.1) = 0 := by
    apply u.property
    intro h
    rcases h with h | h
    · exact hb.hx' (by rw [← hsh]; exact (hb.trans _ ν.1 (ne_of_gt ν.2)).mpr h)
    · exact hb.hx' (by simpa only [hsh] using h)
  have h := right_first_norm_lower U A (P2 x ν) t ht
    (-A (x,0)) (-A (periodicLatticeShiftBack x ν.1,ν.1)) (A (periodicLatticeShiftBack x ν.1,0))
    (by change -_ = 0; rw [hu,neg_zero])
    (star_holonomy2 hb t ν)
    (by simp [a1LM_apply,AprimeZW,P2,hU,RMap_one,periodicLatticeShift_shiftBack])
    (by rfl) (by rfl)
    (by simp [a4LM_apply,AprimeYZ,P2,hzero])
  simpa only [norm_neg,add_comm] using h

/-- No arm is in the localized selector. -/
theorem arm1_omitted {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hb : BdPt Om x) (ν : {ν : Fin 3 // 0 < ν}) : P1 x ν ∉ plaqIn Om := by
  intro h
  exact hb.hx' (h (x,0) ((edge_mem _ _).mpr (Or.inl rfl))).2

theorem arm2_omitted {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hb : BdPt Om x) (ν : {ν : Fin 3 // 0 < ν}) : P2 x ν ∉ plaqIn Om := by
  intro h
  have he := h (periodicLatticeShift (periodicLatticeShiftBack x ν.1) ν.1,0)
    ((edge_mem _ _).mpr (Or.inr (Or.inr (Or.inl rfl))))
  rw [periodicLatticeShift_shiftBack] at he
  exact hb.hx' he.2

end AdalyFormal.Round13.Positivity.Physical
#print axioms AdalyFormal.Round13.Positivity.Physical.arm1_lower
#print axioms AdalyFormal.Round13.Positivity.Physical.arm2_lower
#print axioms AdalyFormal.Round13.Positivity.Physical.arm1_omitted
#print axioms AdalyFormal.Round13.Positivity.Physical.arm2_omitted

namespace AdalyFormal.Round13.Positivity.Physical
open Classical
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLaneR6
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)
open AdalyFormal.Round12.Noncancel.Path
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round13.Positivity.Leaves
variable {L : PeriodicLatticeExtent}

/-- The four actual star plaquettes, not a surrogate stencil. -/
def arm (x : PeriodicLatticeSite L) : Fin 4 → PeriodicLatticePlaquette L :=
  ![P1 x ⟨1,by decide⟩,P2 x ⟨1,by decide⟩,P1 x ⟨2,by decide⟩,P2 x ⟨2,by decide⟩]

theorem arm_injective {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hb : BdPt Om x) : Function.Injective (arm x) := by
  intro i j h
  have hd := congrArg (fun p : PeriodicLatticePlaquette L => p.2.1.2.val) h
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals norm_num [arm,AdalyFormal.D1Literal.P1,P2] at hd
  all_goals first
    | exact False.elim (P1_ne_P2 x hb.side ⟨1,by decide⟩ ⟨1,by decide⟩ h)
    | exact False.elim (P1_ne_P2 x hb.side ⟨1,by decide⟩ ⟨1,by decide⟩ h.symm)
    | exact False.elim (P1_ne_P2 x hb.side ⟨2,by decide⟩ ⟨2,by decide⟩ h)
    | exact False.elim (P1_ne_P2 x hb.side ⟨2,by decide⟩ ⟨2,by decide⟩ h.symm)

def armBudget {q : ℕ} (hq : 0 < q) (R : ℕ)
    (A : BondFnL2 (scaleUp 2 1 (dilLu q R))) : Fin 4 → ℝ :=
  ![‖A (leaf hq R 0)‖^2+‖A (leaf hq R 4)‖^2,
    ‖A (leaf hq R 1)‖^2+‖A (leaf hq R 5)‖^2,
    ‖A (leaf hq R 2)‖^2+‖A (leaf hq R 6)‖^2,
    ‖A (leaf hq R 3)‖^2+‖A (leaf hq R 7)‖^2]

theorem armBudget_sum {q : ℕ} (hq : 0 < q) (R : ℕ)
    (A : BondFnL2 (scaleUp 2 1 (dilLu q R))) :
    (∑ i, armBudget hq R A i) = ∑ i : Fin 8, ‖A (leaf hq R i)‖^2 := by
  simp only [Fin.sum_univ_succ]
  change (‖A (leaf hq R 0)‖^2+‖A (leaf hq R 4)‖^2) +
    ((‖A (leaf hq R 1)‖^2+‖A (leaf hq R 5)‖^2) +
    ((‖A (leaf hq R 2)‖^2+‖A (leaf hq R 6)‖^2) +
    ((‖A (leaf hq R 3)‖^2+‖A (leaf hq R 7)‖^2) + 0))) =
    ‖A (leaf hq R 0)‖^2 + (‖A (leaf hq R 1)‖^2 + (‖A (leaf hq R 2)‖^2 +
    (‖A (leaf hq R 3)‖^2 + (‖A (leaf hq R 4)‖^2 + (‖A (leaf hq R 5)‖^2 +
    (‖A (leaf hq R 6)‖^2 + (‖A (leaf hq R 7)‖^2 + 0)))))))
  ring

/-- The previously missing COMPLETE physical omitted-sum bound. Every curved
exterior plaquette is handled by input vanishing, not falsely called flat. -/
theorem rightStar_omitted_loss {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (t : ℝ) (ht : 0 ≤ Real.cos t)
    (u : ↥(bondSupp (geomOf 2 1 (dilTower q R))))
    (hu : (((iE (geomOf 2 1 (dilTower q R)) u) (rightSite hq R,0) : SuTwo) :
      Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0) :
    -(1-Real.cos t)*(∑ i : Fin 8,
      ‖(iE (geomOf 2 1 (dilTower q R)) u) (leaf hq R i)‖^2) ≤
    omittedEnergy (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (rightStar hq R t) 1 (dilLam q R)) u := by
  let P := gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
    (rightStar hq R t) 1 (dilLam q R)
  have hb := rightSite_bd hq R
  have hPG : P.G = geomOf 2 1 (dilTower q R) := rfl
  have hPU : P.U = starPath (periodicLatticeShift (rightSite hq R) 0) t := rfl
  have hh := omitted_loss_of_injective_arms P (dil_admissible hq hR) (by nlinarith)
    u (Real.cos t) (arm (rightSite hq R)) (arm_injective hb)
    (by
      intro i
      fin_cases i
      · exact arm1_omitted hb ⟨1,by decide⟩
      · exact arm2_omitted hb ⟨1,by decide⟩
      · exact arm1_omitted hb ⟨2,by decide⟩
      · exact arm2_omitted hb ⟨2,by decide⟩)
    (armBudget hq R (iE P.G u))
    (by
      intro i
      fin_cases i
      · simpa [arm,armBudget,leaf,hPG,hPU] using arm1_lower hb t ht u hu ⟨1,by decide⟩
      · simpa [arm,armBudget,leaf,hPG,hPU] using arm2_lower hb t ht u hu ⟨1,by decide⟩
      · simpa [arm,armBudget,leaf,hPG,hPU] using arm1_lower hb t ht u hu ⟨2,by decide⟩
      · simpa [arm,armBudget,leaf,hPG,hPU] using arm2_lower hb t ht u hu ⟨2,by decide⟩)
    (by
      intro p _ hn
      apply nonstar_nonneg hb (right_forward_out hq R) t u p
      intro ν
      have hν : ν.1 = 1 ∨ ν.1 = 2 := by have := ν.2; omega
      rcases hν with hν | hν
      · have heq : ν = ⟨1,by decide⟩ := Subtype.ext hν
        subst ν
        exact ⟨hn 0,hn 1⟩
      · have heq : ν = ⟨2,by decide⟩ := Subtype.ext hν
        subst ν
        exact ⟨hn 2,hn 3⟩)
  rw [armBudget_sum] at hh
  exact hh

/-- Raw-field version of the physical loss; no dressing or inverse premise. -/
theorem rightStar_raw_omitted_loss {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (t : ℝ) (ht : 0 ≤ Real.cos t)
    (u : ↥(bondSupp (geomOf 2 1 (dilTower q R))))
    (hu : (((iE (geomOf 2 1 (dilTower q R)) u) (rightSite hq R,0) : SuTwo) :
      Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0) :
    -(1-Real.cos t)*(∑ i : Fin 8,
      ‖(iE (geomOf 2 1 (dilTower q R)) u) (leaf hq R i)‖^2) ≤
      ∑ p, if p ∈ plaqIn ((dilTower q R).Om 0) then 0 else
        plaqEnergy (rightStar hq R t) (iE (geomOf 2 1 (dilTower q R)) u) p := by
  have h := rightStar_omitted_loss hq hR hR18 t ht u hu
  rw [omittedEnergy_eq_raw _ (dil_admissible hq hR) (by nlinarith)] at h
  exact h

end AdalyFormal.Round13.Positivity.Physical
#print axioms AdalyFormal.Round13.Positivity.Physical.arm
#print axioms AdalyFormal.Round13.Positivity.Physical.armBudget
#print axioms AdalyFormal.Round13.Positivity.Physical.arm_injective
#print axioms AdalyFormal.Round13.Positivity.Physical.armBudget_sum
#print axioms AdalyFormal.Round13.Positivity.Physical.rightStar_omitted_loss
#print axioms AdalyFormal.Round13.Positivity.Physical.rightStar_raw_omitted_loss

namespace AdalyFormal.Round9.Guarded.AnalyticR2
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.QjComposite (stepAverage)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
variable {L : PeriodicLatticeExtent}
theorem Qcomposite_one' (bg : ℕ → Cfg L) (ell : ℕ) (lam : PeriodicLatticeSite L → SuTwo) :
    AdalyFormal.Balaban.QjComposite.Qcomposite bg ell 1 lam = stepAverage (ell ^ 0) (bg 0) ell lam :=
  rfl

theorem bgTower_zero' (G : TowerGeom L) (U : Cfg L) : bgTower G U 0 = U := rfl

theorem QfullOf_apply (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L) (p : BIdx G) :
    WithLp.ofLp (QfullOf G U A) p
      = (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (QlinB G U p.1 A)) p.2.1 := rfl

theorem dil_G_k (q R : ℕ) : (geomOf 2 1 (dilTower q R)).k = 1 := rfl
theorem dil_G_ell (q R : ℕ) : (geomOf 2 1 (dilTower q R)).ell = 2 := rfl

theorem delW_zero (ell k : ℕ) (hell : 0 < ell) : AdalyFormal.W6.delW ell k (fun _ => 0) = 0 := by
  unfold AdalyFormal.W6.delW AdalyFormal.W6.SS
  simp [AdalyFormal.BondComposite.thetaOf_zero ell hell]

theorem dil_Qs_inj {q R : ℕ} (hq : 0 < q) (hR16 : 16 ≤ R) (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    Function.Injective (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (trivialU (scaleUp 2 1 (dilLu q R))) 1 (dilLam q R)).data.Qs :=
  AdalyFormal.W6.qs_injective_strat (by norm_num) (le_refl 2) hS (by omega) (by omega)
    (trivialU _) 1 (dilLam q R) (fun _ => 0) (AdalyFormal.W6.regTower_triv (by norm_num))
    (AdalyFormal.W6.towerClass_triv (by norm_num)) (fun _ _ => le_rfl)
    (fun _ _ => AdalyFormal.W6.rhoOf_zero_lt 2) (by rw [delW_zero 2 1 (by norm_num)]; norm_num)


end AdalyFormal.Round9.Guarded.AnalyticR2
namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## J. The flat localized carrier of the dilated tower is positive definite

At the trivial background `⟪x, B x⟫ = ‖χ curl x‖² + ‖T x‖² + Σ a ℓʲ ‖Q x‖²` (`B` the localized
carrier).  If it vanishes, `x` is curl-free on the plaquettes of `Ω₀`, vanishes on every bond not
touching `Ω₁` (level-0 rows of `Q`), and has vanishing level-1 rows.  Integrating `x` along the
longitudinal lines from the left boundary gives a site field `ξ` with `x = D ξ` on the bonds
before the right edge; the level-1 rows telescope along the longitudinal chain of blocks from the
left collar (where `ξ = 0`) to the right collar (where `ξ` is a transverse constant), so the
constant is `0`, `ξ ∈ N(Q')` and `x = D ξ` everywhere; then `T (D ξ) = 0` forces `D ξ = 0`
(the frozen `final_step` argument, copied). -/
section FlatKernel

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dil_fine_size)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_one curlValueCovariant
  gradValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf stepAverage)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open Fin.NatCast

/-! ### Frozen `NsPtD2.final_step` (outside the `DrEquiv` closure), copied verbatim. -/

theorem siteMask_eq_self_of_supp' {L : PeriodicLatticeExtent} (S : Set (PeriodicLatticeSite L))
    (ξ : SiteL2 L) (h : ∀ x, x ∉ S → ξ x = 0) : siteMask S ξ = ξ := by
  classical
  ext x
  rw [siteMask_apply]
  by_cases hx : x ∈ S
  · rw [if_pos hx]
  · rw [if_neg hx, h x hx]

theorem lapDir_eq_mask_lap' {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (ξ : SiteL2 L)
    (h : ∀ x, x ∉ G.Om0 → ξ x = 0) : lapDir G U ξ = siteMask G.Om0 (lapFull U ξ) := by
  unfold lapDir
  simp only [ContinuousLinearMap.comp_apply]
  rw [siteMask_eq_self_of_supp' _ _ h]

theorem final_step' {L : PeriodicLatticeExtent} (G : TowerGeom L) (ξ : SiteL2 L)
    (hξ : ξ ∈ NQp G (flatCfg : Cfg L))
    (hT : Tfull G (flatCfg : Cfg L) (gradL2 (flatCfg : Cfg L) ξ) = 0) :
    gradL2 (flatCfg : Cfg L) ξ = 0 := by
  have hsupp := hξ.1
  have hlap := lapDir_eq_mask_lap' G flatCfg ξ hsupp
  have hmem : lapDir G (flatCfg : Cfg L) ξ ∈ RImage G (flatCfg : Cfg L) :=
    Submodule.mem_map.mpr ⟨ξ, hξ, rfl⟩
  have hR : Rproj G (flatCfg : Cfg L) (lapFull (flatCfg : Cfg L) ξ) = 0 := by
    have : Tfull G (flatCfg : Cfg L) (gradL2 (flatCfg : Cfg L) ξ) =
        Rproj G (flatCfg : Cfg L) (lapFull (flatCfg : Cfg L) ξ) := rfl
    rw [← this]; exact hT
  have horth : lapFull (flatCfg : Cfg L) ξ ∈ (RImage G (flatCfg : Cfg L))ᗮ := by
    have := hR
    unfold Rproj at this
    exact (Submodule.starProjection_apply_eq_zero_iff _).mp this
  have h1 : ⟪lapDir G (flatCfg : Cfg L) ξ, lapFull (flatCfg : Cfg L) ξ⟫ = 0 :=
    (Submodule.mem_orthogonal _ _).mp horth _ hmem
  have h2 : ⟪lapDir G (flatCfg : Cfg L) ξ, lapFull (flatCfg : Cfg L) ξ⟫ =
      ‖lapDir G (flatCfg : Cfg L) ξ‖ ^ 2 := by
    have e : ⟪siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ), lapFull (flatCfg : Cfg L) ξ⟫
        = ⟪siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ),
            siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ)⟫ := by
      calc ⟪siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ), lapFull (flatCfg : Cfg L) ξ⟫
          = ⟪siteMask G.Om0 (siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ)),
              lapFull (flatCfg : Cfg L) ξ⟫ := by rw [siteMask_idem]
        _ = _ := siteMask_symm _ _ _
    rw [hlap, e, real_inner_self_eq_norm_sq]
  have h3 : lapDir G (flatCfg : Cfg L) ξ = 0 := by
    rw [h2] at h1
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)
  have h4 : ⟪ξ, lapFull (flatCfg : Cfg L) ξ⟫ = 0 := by
    have : ⟪ξ, lapFull (flatCfg : Cfg L) ξ⟫ = ⟪siteMask G.Om0 ξ, lapFull (flatCfg : Cfg L) ξ⟫ := by
      rw [siteMask_eq_self_of_supp' _ _ hsupp]
    rw [this, siteMask_symm, ← hlap, h3, inner_zero_right]
  have h5 : ⟪ξ, lapFull (flatCfg : Cfg L) ξ⟫ = ‖gradL2 (flatCfg : Cfg L) ξ‖ ^ 2 := by
    simp only [lapFull, ContinuousLinearMap.comp_apply, gradAdj, ContinuousLinearMap.adjoint_inner_right]
    rw [real_inner_self_eq_norm_sq]
  rw [h5] at h4
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h4)

/-! ### Coordinates of the dilated tower -/

variable {q R : ℕ}

theorem dsize0 (hq : 0 < q) : scaleUp 2 1 (dilLu q R) 0 + 1 = 12 * (R * q) + 16 * q := by
  have h := dil_fine_size hq R 0
  simpa using h

theorem dsizeT (hq : 0 < q) {μ : Fin 3} (hμ : μ ≠ 0) : scaleUp 2 1 (dilLu q R) μ + 1 = 8 * q := by
  rw [dil_fine_size hq R μ, if_neg hμ]

theorem x0_lt (hq : 0 < q) (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    (x 0).val < 12 * (R * q) + 16 * q := by
  have h1 := (x 0).isLt
  have h2 := dsize0 (R := R) hq
  omega

theorem xT_lt (hq : 0 < q) (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0) :
    (x μ).val < 8 * q := by
  have h1 := (x μ).isLt
  have h2 := dsizeT (R := R) hq hμ
  omega

theorem mem_Om0 (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    x ∈ (dilTower q R).Om 0 ↔ 4 * q ≤ (x 0).val ∧ (x 0).val < 12 * (R * q) + 12 * q := Iff.rfl

theorem mem_Om1 (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    x ∈ (dilTower q R).Om 1 ↔
      2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q := Iff.rfl

theorem not_mem_Om2 (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    x ∉ (dilTower q R).Om 2 := by
  simp [dilTower]

theorem shift_coord_ne {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) {μ ν : Fin 3}
    (h : ν ≠ μ) : (periodicLatticeShift x μ) ν = x ν := by
  unfold periodicLatticeShift
  rw [Function.update_of_ne h]

theorem shift_self_coord {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) (μ : Fin 3) :
    (periodicLatticeShift x μ) μ = x μ + 1 := by
  unfold periodicLatticeShift
  rw [Function.update_self]

theorem shift0_val_lt {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L)
    (h : (x 0).val + 1 < L 0 + 1) : ((periodicLatticeShift x 0) 0).val = (x 0).val + 1 := by
  rw [shift_self_coord, Fin.val_add_one, if_neg]
  intro hc
  rw [hc, Fin.val_last] at h
  omega

theorem shift0_val_last {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L)
    (h : (x 0).val + 1 = L 0 + 1) : ((periodicLatticeShift x 0) 0).val = 0 := by
  rw [shift_self_coord, Fin.val_add_one, if_pos]
  ext
  rw [Fin.val_last]
  omega

/-! ### The kernel argument -/

section Kernel
variable (hq : 0 < q) (hR : 1 ≤ R) (A : BondFnL2 (scaleUp 2 1 (dilLu q R)))
  (hsupp : ∀ b, b ∉ bondsOm0 (geomOf 2 1 (dilTower q R)) → A b = 0)
  (hQ : QfullOf (geomOf 2 1 (dilTower q R)) flatCfg A = 0)

theorem OmGe1_mem {x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))}
    (h : OmGe (geomOf 2 1 (dilTower q R)) 1 x) : x ∈ (dilTower q R).Om 1 := by
  obtain ⟨i, hi1, hik, y, hy, hxy⟩ := h
  have hi : i = 1 := by
    have : i ≤ 1 := hik
    omega
  subst hi
  obtain ⟨hdiv, hyOm, -⟩ := hy
  rw [mem_Om1] at hyOm ⊢
  have h0 := hxy 0
  have hd := hdiv 0
  have hell : (geomOf 2 1 (dilTower q R)).ell = 2 := rfl
  simp only [pow_one, hell] at hd h0
  have hb : 2 ∣ 10 * (R * q) + 12 * q := ⟨5 * (R * q) + 6 * q, by ring⟩
  omega

include hsupp hQ in
theorem A_zero_off {b : Bond (scaleUp 2 1 (dilLu q R))} (h1 : b.1 ∉ (dilTower q R).Om 1)
    (h2 : periodicLatticeShift b.1 b.2 ∉ (dilTower q R).Om 1) : A b = 0 := by
  by_cases hb : b ∈ bondsOm0 (geomOf 2 1 (dilTower q R))
  · have hL : b ∈ bondsLam (geomOf 2 1 (dilTower q R)) 0 := by
      refine ⟨?_, ?_⟩
      · rcases hb with hb | hb
        · exact Or.inl ⟨fun μ => by simp, hb, h1⟩
        · exact Or.inr ⟨fun μ => by simp, hb, h2⟩
      · rintro (h | h)
        · exact h1 (OmGe1_mem h)
        · exact h2 (OmGe1_mem h)
    have h := congrArg (fun v : FSp (geomOf 2 1 (dilTower q R)) => WithLp.ofLp v ⟨0, ⟨b, hL⟩⟩) hQ
    have h' : WithLp.ofLp (QfullOf (geomOf 2 1 (dilTower q R)) flatCfg A) ⟨0, ⟨b, hL⟩⟩ = A b := by
      rw [QfullOf_apply]
      show (((geomOf 2 1 (dilTower q R)).ell : ℝ) ^ 0)⁻¹ •
        (WithLp.ofLp (QlinB (geomOf 2 1 (dilTower q R)) flatCfg 0 A)) b = A b
      rw [QlinB_zero, pow_zero, inv_one, one_smul]
    simp only at h
    rw [h'] at h
    exact h
  · exact hsupp b hb

/-- the site with longitudinal coordinate replaced by `u`. -/
def sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) :
    PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) :=
  Function.update z 0 ((u : ℕ) : Fin (scaleUp 2 1 (dilLu q R) 0 + 1))

omit hq A in
theorem sitex_val (hq : 0 < q) (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {u : ℕ}
    (hu : u < 12 * (R * q) + 16 * q) : ((sitex z u) 0).val = u := by
  unfold sitex
  rw [Function.update_self, Fin.val_natCast, dsize0 hq]
  exact Nat.mod_eq_of_lt hu

omit A in
theorem sitex_coord (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) {ν : Fin 3}
    (hν : ν ≠ 0) : (sitex z u) ν = z ν := by
  unfold sitex
  rw [Function.update_of_ne hν]

omit A in
theorem sitex_self (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : sitex z (z 0).val = z := by
  unfold sitex
  rw [Fin.cast_val_eq_self, Function.update_eq_self]

omit A in
theorem sitex_sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u v : ℕ) :
    sitex (sitex z v) u = sitex z u := by
  unfold sitex
  rw [Function.update_idem]

omit A in
theorem shift_sitex0 (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) :
    periodicLatticeShift (sitex z u) 0 = sitex z (u + 1) := by
  unfold periodicLatticeShift sitex
  rw [Function.update_idem, Function.update_self, Nat.cast_succ]

omit A in
theorem shift_sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) {μ : Fin 3}
    (hμ : μ ≠ 0) : periodicLatticeShift (sitex z u) μ = sitex (periodicLatticeShift z μ) u := by
  unfold periodicLatticeShift sitex
  rw [Function.update_of_ne hμ, Function.update_comm (Ne.symm hμ)]

omit A in
theorem sitex_of_shift0 (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) :
    sitex (periodicLatticeShift z 0) u = sitex z u := by
  unfold periodicLatticeShift sitex
  rw [Function.update_idem]

/-- the longitudinal potential. -/
noncomputable def xi (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : SuTwo :=
  ∑ u ∈ Finset.range (z 0).val, A (sitex z u, 0)

include hq in
/-- longitudinal step. -/
theorem xi_shift0 (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (h : (z 0).val + 1 < 12 * (R * q) + 16 * q) :
    xi A (periodicLatticeShift z 0) = xi A z + A (z, 0) := by
  unfold xi
  have hz : ((periodicLatticeShift z 0) 0).val = (z 0).val + 1 :=
    shift0_val_lt z (by have h2 := dsize0 (R := R) hq; omega)
  rw [hz, Finset.sum_range_succ]
  simp only [sitex_of_shift0]
  rw [sitex_self]

include hq hR hsupp hQ in
/-- the plaquette identity in the `(0, μ)` plane, from curl-freeness or vanishing of all bonds. -/
theorem trans_step
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (w : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0)
    (hw : (w 0).val + 1 < 12 * (R * q) + 16 * q) :
    A (periodicLatticeShift w μ, 0) - A (w, 0) = A (periodicLatticeShift w 0, μ) - A (w, μ) := by
  classical
  have h0μ : (0 : Fin 3) < μ := by
    rcases Fin.pos_iff_ne_zero.mpr hμ with h
    exact h
  have hw0 : ((periodicLatticeShift w 0) 0).val = (w 0).val + 1 :=
    shift0_val_lt w (by have h2 := dsize0 (R := R) hq; omega)
  have hwμ : (periodicLatticeShift w μ) 0 = w 0 := shift_coord_ne w (Ne.symm hμ)
  have hw0μ : ((periodicLatticeShift (periodicLatticeShift w 0) μ) 0).val = (w 0).val + 1 := by
    rw [shift_coord_ne _ (Ne.symm hμ), hw0]
  have hwμ0 : ((periodicLatticeShift (periodicLatticeShift w μ) 0) 0).val = (w 0).val + 1 := by
    rw [shift0_val_lt _ (by have h2 := dsize0 (R := R) hq; rw [hwμ]; omega), hwμ]
  by_cases hin : 4 * q ≤ (w 0).val ∧ (w 0).val + 1 < 12 * (R * q) + 12 * q
  · let p : PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)) := (w, ⟨(0, μ), h0μ⟩)
    have hp : p ∈ plaqIn ((dilTower q R).Om 0) := by
      intro e he
      simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton, p] at he
      rcases he with rfl | rfl | rfl | rfl
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
    have hc := hcurl p hp
    simp only [curlValueCovariant, p, flatCfg, RMap_one, LinearMap.id_apply] at hc
    have e : A (periodicLatticeShift w μ, 0) - A (w, 0) - (A (periodicLatticeShift w 0, μ) - A (w, μ)) = 0 := by
      rw [← neg_eq_zero, ← hc]; abel
    exact sub_eq_zero.mp e
  · have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
    have hR1 : ∀ x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)),
        ((x 0).val = (w 0).val ∨ (x 0).val = (w 0).val + 1) → x ∉ (dilTower q R).Om 1 := by
      intro x hx hxm
      rw [mem_Om1] at hxm
      rcases hx with hx | hx <;> rw [hx] at hxm <;>
        (by_cases h4 : 4 * q ≤ (w 0).val
         · have h5 : ¬ ((w 0).val + 1 < 12 * (R * q) + 12 * q) := fun h => hin ⟨h4, h⟩
           omega
         · omega)
    have z1 := A_zero_off A hsupp hQ (b := (w, 0)) (hR1 w (Or.inl rfl)) (hR1 _ (Or.inr hw0))
    have z2 := A_zero_off A hsupp hQ (b := (periodicLatticeShift w 0, μ)) (hR1 _ (Or.inr hw0))
      (hR1 _ (Or.inr hw0μ))
    have z3 := A_zero_off A hsupp hQ (b := (periodicLatticeShift w μ, 0))
      (hR1 (periodicLatticeShift w μ) (Or.inl (by rw [hwμ]))) (hR1 _ (Or.inr hwμ0))
    have z4 := A_zero_off A hsupp hQ (b := (w, μ)) (hR1 w (Or.inl rfl))
      (hR1 (periodicLatticeShift w μ) (Or.inl (by rw [hwμ])))
    rw [z1, z2, z3, z4]

include hq hR hsupp hQ in
/-- transverse step. -/
theorem xi_shiftT
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0) :
    xi A (periodicLatticeShift z μ) = xi A z + (A (z, μ) - A (sitex z 0, μ)) := by
  unfold xi
  rw [shift_coord_ne z (Ne.symm hμ)]
  have hz := x0_lt hq z
  have e : ∀ u ∈ Finset.range (z 0).val, A (sitex (periodicLatticeShift z μ) u, 0)
      = A (sitex z u, 0) + (A (sitex z (u + 1), μ) - A (sitex z u, μ)) := by
    intro u hu
    rw [Finset.mem_range] at hu
    have hval : ((sitex z u) 0).val = u := sitex_val hq z (by omega)
    have ht := trans_step hq hR A hsupp hQ hcurl (sitex z u) hμ (by rw [hval]; omega)
    rw [shift_sitex z u hμ, shift_sitex0] at ht
    rw [← sub_eq_iff_eq_add', ht]
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_range_sub (fun u => A (sitex z u, μ)),
    sitex_self]

include hq hsupp hQ in
theorem xi_left (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (h : (z 0).val < 2 * (R * q) + 4 * q) : xi A z = 0 := by
  unfold xi
  refine Finset.sum_eq_zero (fun u hu => ?_)
  rw [Finset.mem_range] at hu
  have hz := x0_lt hq z
  have hv : ((sitex z u) 0).val = u := sitex_val hq z (by omega)
  refine A_zero_off A hsupp hQ ?_ ?_
  · rw [mem_Om1, hv]; omega
  · rw [mem_Om1, shift_sitex0, sitex_val hq z (by omega)]; omega

include hq hsupp hQ in
/-- beyond the right edge of `Ω₁` the potential equals its value at the right edge. -/
theorem xi_right (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (h : 10 * (R * q) + 12 * q ≤ (z 0).val) :
    xi A z = xi A (sitex z (10 * (R * q) + 12 * q)) := by
  have hz := x0_lt hq z
  have key : ∀ n, 10 * (R * q) + 12 * q + n < 12 * (R * q) + 16 * q →
      xi A (sitex z (10 * (R * q) + 12 * q + n)) = xi A (sitex z (10 * (R * q) + 12 * q)) := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      have hv : ((sitex z (10 * (R * q) + 12 * q + n)) 0).val = 10 * (R * q) + 12 * q + n :=
        sitex_val hq z (by omega)
      rw [← ih (by omega)]
      have e := xi_shift0 hq A (sitex z (10 * (R * q) + 12 * q + n)) (by rw [hv]; omega)
      rw [shift_sitex0] at e
      rw [show 10 * (R * q) + 12 * q + (n + 1) = 10 * (R * q) + 12 * q + n + 1 by ring, e]
      have h0 : A (sitex z (10 * (R * q) + 12 * q + n), 0) = 0 := by
        refine A_zero_off A hsupp hQ ?_ ?_
        · show sitex z _ ∉ _
          rw [mem_Om1, hv]; omega
        · show periodicLatticeShift (sitex z _) 0 ∉ _
          rw [mem_Om1, shift_sitex0, sitex_val hq z (by omega)]; omega
      rw [h0, add_zero]
  have hk := key ((z 0).val - (10 * (R * q) + 12 * q)) (by omega)
  rw [Nat.add_sub_cancel' h, sitex_self] at hk
  exact hk

/-- the right-edge value of the potential, a function of the transverse coordinates. -/
noncomputable def Iv (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : SuTwo :=
  xi A (sitex z (10 * (R * q) + 12 * q))

include hq hR hsupp hQ in
theorem Iv_shiftT
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0) :
    Iv A (periodicLatticeShift z μ) = Iv A z := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  unfold Iv
  rw [← shift_sitex z _ hμ, xi_shiftT hq hR A hsupp hQ hcurl _ hμ]
  have hv : ((sitex z (10 * (R * q) + 12 * q)) 0).val = 10 * (R * q) + 12 * q :=
    sitex_val hq z (by omega)
  have e1 : A (sitex z (10 * (R * q) + 12 * q), μ) = 0 := by
    refine A_zero_off A hsupp hQ ?_ ?_
    · show sitex z _ ∉ _
      rw [mem_Om1, hv]; omega
    · show periodicLatticeShift (sitex z _) μ ∉ _
      rw [mem_Om1, shift_coord_ne _ (Ne.symm hμ), hv]; omega
  have e2 : A (sitex (sitex z (10 * (R * q) + 12 * q)) 0, μ) = 0 := by
    rw [sitex_sitex]
    have hv0 : ((sitex z 0) 0).val = 0 := sitex_val hq z (by omega)
    refine A_zero_off A hsupp hQ ?_ ?_
    · show sitex z 0 ∉ _
      rw [mem_Om1, hv0]; omega
    · show periodicLatticeShift (sitex z 0) μ ∉ _
      rw [mem_Om1, shift_coord_ne _ (Ne.symm hμ), hv0]; omega
  rw [e1, e2, sub_zero, add_zero]

omit hq hR A in
theorem update_shift_succ {L : PeriodicLatticeExtent} (w : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) :
    Function.update w μ (w μ + ((n + 1 : ℕ) : Fin (L μ + 1))) =
      periodicLatticeShift (Function.update w μ (w μ + ((n : ℕ) : Fin (L μ + 1)))) μ := by
  unfold periodicLatticeShift
  rw [Function.update_idem, Function.update_self, Nat.cast_succ, add_assoc]

include hq hR hsupp hQ in
theorem Iv_update
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0)
    (v : Fin (scaleUp 2 1 (dilLu q R) μ + 1)) :
    Iv A (Function.update z μ v) = Iv A z := by
  have hn : ∀ n : ℕ, Iv A (Function.update z μ (z μ + ((n : ℕ) : Fin _))) = Iv A z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [update_shift_succ, Iv_shiftT hq hR A hsupp hQ hcurl _ hμ, ih]
  have h := hn (v - z μ).val
  rw [Fin.cast_val_eq_self, add_sub_cancel] at h
  exact h

omit hq hR A in
theorem Iv_update0 (A : BondFnL2 (scaleUp 2 1 (dilLu q R))) (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (v : Fin (scaleUp 2 1 (dilLu q R) 0 + 1)) : Iv A (Function.update z 0 v) = Iv A z := by
  unfold Iv sitex
  rw [Function.update_idem]

include hq hR hsupp hQ in
theorem Iv_const
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : Iv A z = Iv A (fun _ => 0) := by
  have e : (fun _ => (0 : Fin _) : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) =
      Function.update (Function.update (Function.update z 0 0) 1 0) 2 0 := by
    funext ν
    fin_cases ν <;> simp [Function.update] <;> rfl
  rw [e, Iv_update hq hR A hsupp hQ hcurl _ (by decide), Iv_update hq hR A hsupp hQ hcurl _ (by decide),
    Iv_update0]

omit hq hR A in
theorem coarseShift_sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (t : ℕ) :
    coarseShift (sitex z t) 2 0 = sitex z (t + 2) := by
  show periodicLatticeShift (periodicLatticeShift (sitex z t) 0) 0 = _
  rw [shift_sitex0, shift_sitex0]

include hq hR hQ in
/-- one level-1 row along direction `0`: the block sums of the potential agree. -/
theorem row_step (y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (hy1 : 2 ∣ (y 1).val) (hy2 : 2 ∣ (y 2).val) (hy0 : 2 ∣ (y 0).val)
    (hlo : 2 * (R * q) + 4 * q ≤ (y 0).val + 2) (hhi : (y 0).val + 2 ≤ 10 * (R * q) + 12 * q) :
    ∑ w ∈ stepBlockOf (coarseShift y 2 0) 1 2, xi A w = ∑ w ∈ stepBlockOf y 1 2, xi A w := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  have hy0' : ((periodicLatticeShift y 0) 0).val = (y 0).val + 1 := shift0_val_lt y (by omega)
  have hcs0 : ((coarseShift y 2 0) 0).val = (y 0).val + 2 := by
    show ((periodicLatticeShift (periodicLatticeShift y 0) 0) 0).val = _
    rw [shift0_val_lt _ (by rw [hy0']; omega), hy0']
  have hcsT : ∀ ν : Fin 3, ν ≠ 0 → (coarseShift y 2 0) ν = y ν := by
    intro ν hν
    show (periodicLatticeShift (periodicLatticeShift y 0) 0) ν = y ν
    rw [shift_coord_ne _ hν, shift_coord_ne _ hν]
  have hc : (y, (0 : Fin 3)) ∈ bondsLam (geomOf 2 1 (dilTower q R)) 1 := by
    refine ⟨?_, ?_⟩
    · by_cases hya : 2 * (R * q) + 4 * q ≤ (y 0).val
      · left
        show y ∈ (geomOf 2 1 (dilTower q R)).Lam 1
        refine ⟨fun μ => ?_, (mem_Om1 _).mpr ⟨hya, by omega⟩, not_mem_Om2 _⟩
        show 2 ^ 1 ∣ (y μ).val
        fin_cases μ
        · simpa using hy0
        · simpa using hy1
        · simpa using hy2
      · right
        have e1 : coarseShift (y, (0 : Fin 3)).1 ((geomOf 2 1 (dilTower q R)).ell ^ 1) (y, (0 : Fin 3)).2 =
            coarseShift y 2 0 := rfl
        rw [e1]
        show coarseShift y 2 0 ∈ (geomOf 2 1 (dilTower q R)).Lam 1
        refine ⟨fun μ => ?_, (mem_Om1 _).mpr ⟨by rw [hcs0]; omega, by rw [hcs0]; omega⟩, not_mem_Om2 _⟩
        show 2 ^ 1 ∣ ((coarseShift y 2 0) μ).val
        fin_cases μ
        · show 2 ^ 1 ∣ ((coarseShift y 2 0) 0).val
          rw [hcs0]; simpa using (Nat.dvd_add hy0 (dvd_refl 2))
        · show 2 ^ 1 ∣ ((coarseShift y 2 0) 1).val
          rw [hcsT 1 (by decide)]; simpa using hy1
        · show 2 ^ 1 ∣ ((coarseShift y 2 0) 2).val
          rw [hcsT 2 (by decide)]; simpa using hy2
    · rintro (h | h) <;>
        exact not_OmGe_of_lt (G := geomOf 2 1 (dilTower q R)) (lt_of_eq_of_lt (dil_G_k q R) (by norm_num)) _ h
  let p : BIdx (geomOf 2 1 (dilTower q R)) := ⟨1, ⟨(y, 0), hc⟩⟩
  have hrow : WithLp.ofLp (QfullOf (geomOf 2 1 (dilTower q R)) flatCfg A) p = 0 := by
    rw [hQ]; rfl
  have hQrow := AdalyFormal.W6.Qflat_row (ell := 2) (k := 1) (Lu := dilLu q R) (S := dilTower q R)
    (by norm_num) A p
  have hline : AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictSuTwo (2 ^ (p.1 : ℕ))
      (WithLp.ofLp A) (AdalyFormal.W6.rowCB (by norm_num) p) = 0 := by
    rw [← hQrow]; exact hrow
  have hline' : (1 / ((2 : ℕ) : ℝ) ^ 4) • ∑ x ∈ blockOf y 2, ∑ i ∈ Finset.range 2,
      A (pathSite x 0 i, 0) = 0 := hline
  have hsum : ∑ x ∈ blockOf y 2, ∑ i ∈ Finset.range 2, A (pathSite x 0 i, 0) = 0 := by
    rcases smul_eq_zero.mp hline' with h | h
    · norm_num at h
    · exact h
  have hpt : ∀ x ∈ blockOf y 2, ∑ i ∈ Finset.range 2, A (pathSite x 0 i, 0) =
      xi A (coarseShift x 2 0) - xi A x := by
    intro x hx
    have hxb := (mem_blockOf.mp hx) 0
    have hx0 : (x 0).val + 1 < 12 * (R * q) + 16 * q := by omega
    have hsx : ((periodicLatticeShift x 0) 0).val = (x 0).val + 1 := shift0_val_lt x (by omega)
    have e1 := xi_shift0 hq A x hx0
    have e2 := xi_shift0 hq A (periodicLatticeShift x 0) (by rw [hsx]; omega)
    show _ = xi A (periodicLatticeShift (periodicLatticeShift x 0) 0) - xi A x
    rw [e2, e1, Finset.sum_range_succ, Finset.sum_range_one]
    show A (x, 0) + A (periodicLatticeShift x 0, 0) = _
    abel
  have hfit : ∀ ν : Fin 3, (y ν).val + 1 * 2 ≤ scaleUp 2 1 (dilLu q R) ν + 1 := by
    intro ν
    by_cases hν : ν = 0
    · subst hν; omega
    · have := xT_lt hq y hν
      have h8 := dsizeT (R := R) hq hν
      have hev : 2 ∣ (y ν).val := by
        fin_cases ν
        · exact absurd rfl hν
        · exact hy1
        · exact hy2
      omega
  have hfit' : ∀ ν : Fin 3, ((coarseShift y 2 0) ν).val + 1 * 2 ≤ scaleUp 2 1 (dilLu q R) ν + 1 := by
    intro ν
    by_cases hν : ν = 0
    · subst hν; rw [hcs0]; omega
    · rw [hcsT ν hν]; exact hfit ν
  have hshift := AdalyFormal.CurvBlock.block_sum_shift 1 2 2 0 hfit hfit' (xi A)
  rw [← hshift]
  rw [AdalyFormal.Balaban.QjComposite.stepBlockOf_one] at *
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib] at hsum
  exact sub_eq_zero.mp hsum

include hq hR hsupp hQ in
/-- the block sums vanish along the whole longitudinal chain of blocks. -/
theorem chain_zero (y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (hy1 : 2 ∣ (y 1).val) (hy2 : 2 ∣ (y 2).val) :
    ∀ m : ℕ, 2 * m ≤ 8 * (R * q) + 8 * q + 2 →
      ∑ w ∈ stepBlockOf (sitex y (2 * (R * q) + 4 * q - 2 + 2 * m)) 1 2, xi A w = 0 := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  intro m
  induction m with
  | zero =>
    intro _
    refine Finset.sum_eq_zero (fun w hw => ?_)
    have hb := ((AdalyFormal.Balaban.QjComposite.mem_stepBlockOf).mp hw) 0
    have hv : ((sitex y (2 * (R * q) + 4 * q - 2 + 2 * 0)) 0).val = 2 * (R * q) + 4 * q - 2 + 2 * 0 :=
      sitex_val hq y (by omega)
    rw [hv] at hb
    exact xi_left hq A hsupp hQ w (by omega)
  | succ m ih =>
    intro hm
    have hv : ((sitex y (2 * (R * q) + 4 * q - 2 + 2 * m)) 0).val = 2 * (R * q) + 4 * q - 2 + 2 * m :=
      sitex_val hq y (by omega)
    have e : sitex y (2 * (R * q) + 4 * q - 2 + 2 * (m + 1)) =
        coarseShift (sitex y (2 * (R * q) + 4 * q - 2 + 2 * m)) 2 0 := by
      rw [coarseShift_sitex]
      congr 1
    rw [e, row_step hq hR A hQ _ (by rw [sitex_coord _ _ (by decide)]; exact hy1)
      (by rw [sitex_coord _ _ (by decide)]; exact hy2) (by rw [hv]; omega) (by rw [hv]; omega)
      (by rw [hv]; omega)]
    exact ih (by omega)

include hq hR hsupp hQ in
theorem Iv_zero
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0) :
    Iv A (fun _ => 0) = 0 := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  let y0 : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) := fun _ => 0
  have hb := chain_zero hq hR A hsupp hQ y0 (by simp [y0]) (by simp [y0])
    (4 * (R * q) + 4 * q + 1) (by omega)
  have hv : ((sitex y0 (2 * (R * q) + 4 * q - 2 + 2 * (4 * (R * q) + 4 * q + 1))) 0).val =
      10 * (R * q) + 12 * q := by
    rw [sitex_val hq y0 (by omega)]; omega
  have e : ∀ w ∈ stepBlockOf (sitex y0 (2 * (R * q) + 4 * q - 2 + 2 * (4 * (R * q) + 4 * q + 1))) 1 2,
      xi A w = Iv A (fun _ => 0) := by
    intro w hw
    have hwb := ((AdalyFormal.Balaban.QjComposite.mem_stepBlockOf).mp hw) 0
    rw [hv] at hwb
    rw [xi_right hq A hsupp hQ w (by omega)]
    exact Iv_const hq hR A hsupp hQ hcurl w
  have hfit : ∀ ν : Fin 3, ((sitex y0 (2 * (R * q) + 4 * q - 2 + 2 * (4 * (R * q) + 4 * q + 1))) ν).val
      + 1 * 2 ≤ scaleUp 2 1 (dilLu q R) ν + 1 := by
    intro ν
    by_cases hν : ν = 0
    · subst hν; rw [hv]; omega
    · rw [sitex_coord _ _ hν]
      have h8 := dsizeT (R := R) hq hν
      show ((0 : Fin _) : ℕ) + 1 * 2 ≤ _
      simp only [Fin.val_zero]
      omega
  rw [Finset.sum_congr rfl e, Finset.sum_const,
    AdalyFormal.Balaban.QjComposite.card_stepBlockOf _ 1 2 one_pos hfit] at hb
  have h8 : (8 : ℝ) • Iv A (fun _ => 0) = 0 := by
    rw [show (8 : ℝ) = ((2 ^ 3 : ℕ) : ℝ) by norm_num, Nat.cast_smul_eq_nsmul]
    exact hb
  rcases smul_eq_zero.mp h8 with h | h
  · norm_num at h
  · exact h

include hq hR hsupp hQ in
theorem xi_mem_NQp
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0) :
    (WithLp.toLp 2 (xi A) : SiteL2 (scaleUp 2 1 (dilLu q R))) ∈
      NQp (geomOf 2 1 (dilTower q R)) flatCfg := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  have hzero : ∀ x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)),
      ¬ ((dilTower q R).Om 1 x) → xi A x = 0 := by
    intro x hx
    have hx' : ¬ (2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q) := hx
    by_cases h : (x 0).val < 2 * (R * q) + 4 * q
    · exact xi_left hq A hsupp hQ x h
    · rw [xi_right hq A hsupp hQ x (by omega)]
      show Iv A x = 0
      rw [Iv_const hq hR A hsupp hQ hcurl x, Iv_zero hq hR A hsupp hQ hcurl]
  refine ⟨fun x hx => ?_, fun j hj y hy => ?_⟩
  · show xi A x = 0
    refine hzero x (fun h1 => hx ?_)
    have h1' : 2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q := h1
    show 4 * q ≤ (x 0).val ∧ (x 0).val < 12 * (R * q) + 12 * q
    omega
  · have hj1 : j = 0 ∨ j = 1 := by
      have : j ≤ 1 := hj
      omega
    rcases hj1 with rfl | rfl
    · rw [Qlev_apply, AdalyFormal.Balaban.QjComposite.Qcomposite_zero]
      show xi A y = 0
      exact hzero y hy.2.2
    · rw [Qlev_apply, Qcomposite_one', bgTower_zero']
      show stepAverage (2 ^ 0) (trivialU _) 2 (xi A) y = 0
      rw [AdalyFormal.Balaban.QjComposite.stepAverage_trivialU, pow_zero]
      obtain ⟨hdiv, hy1, -⟩ := hy
      have hy1' : 2 * (R * q) + 4 * q ≤ (y 0).val ∧ (y 0).val < 10 * (R * q) + 12 * q := hy1
      have hd0 : 2 ∣ (y 0).val := by simpa using hdiv 0
      have hd1 : 2 ∣ (y 1).val := by simpa using hdiv 1
      have hd2 : 2 ∣ (y 2).val := by simpa using hdiv 2
      obtain ⟨m, hm⟩ : ∃ m, (y 0).val = 2 * (R * q) + 4 * q - 2 + 2 * m := by
        obtain ⟨t, ht⟩ := hd0
        refine ⟨t - (R * q) - 2 * q + 1, ?_⟩
        omega
      have hc := chain_zero hq hR A hsupp hQ y hd1 hd2 m (by omega)
      rw [← hm, sitex_self] at hc
      rw [hc, smul_zero]

include hq hR hsupp hQ in
theorem A_eq_grad
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0) :
    A = gradL2 flatCfg (WithLp.toLp 2 (xi A)) := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  refine PiLp.ext (fun e => ?_)
  obtain ⟨z, μ⟩ := e
  show A (z, μ) = gradValueCovariant flatCfg (xi A) (z, μ)
  simp only [gradValueCovariant, flatCfg, RMap_one, LinearMap.id_apply]
  have hz := x0_lt hq z
  by_cases hμ : μ = 0
  · subst hμ
    by_cases hz1 : (z 0).val + 1 < 12 * (R * q) + 16 * q
    · rw [xi_shift0 hq A z hz1]; abel
    · have hzl : (z 0).val + 1 = scaleUp 2 1 (dilLu q R) 0 + 1 := by omega
      have h0 : ((periodicLatticeShift z 0) 0).val = 0 := shift0_val_last z hzl
      have e1 : xi A (periodicLatticeShift z 0) = 0 := xi_left hq A hsupp hQ _ (by rw [h0]; omega)
      have e2 : xi A z = 0 := by
        rw [xi_right hq A hsupp hQ z (by omega)]
        show Iv A z = 0
        rw [Iv_const hq hR A hsupp hQ hcurl z, Iv_zero hq hR A hsupp hQ hcurl]
      have e3 : A (z, 0) = 0 := by
        refine A_zero_off A hsupp hQ ?_ ?_
        · show z ∉ _
          rw [mem_Om1]; omega
        · show periodicLatticeShift z 0 ∉ _
          rw [mem_Om1, h0]; omega
      rw [e1, e2, e3, sub_zero]
  · rw [xi_shiftT hq hR A hsupp hQ hcurl z hμ]
    have hv0 : ((sitex z 0) 0).val = 0 := sitex_val hq z (by omega)
    have e3 : A (sitex z 0, μ) = 0 := by
      refine A_zero_off A hsupp hQ ?_ ?_
      · show sitex z 0 ∉ _
        rw [mem_Om1, hv0]; omega
      · show periodicLatticeShift (sitex z 0) μ ∉ _
        rw [mem_Om1, shift_coord_ne _ (Ne.symm hμ), hv0]; omega
    rw [e3]; abel

include hq hR hsupp hQ in
/-- **The flat kernel of the dilated tower is trivial.** -/
theorem dil_flat_kernel
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (hT : Tfull (geomOf 2 1 (dilTower q R)) flatCfg A = 0) : A = 0 := by
  have hg := A_eq_grad hq hR A hsupp hQ hcurl
  have hmem := xi_mem_NQp hq hR A hsupp hQ hcurl
  rw [hg] at hT ⊢
  exact final_step' _ _ hmem hT

end Kernel

end FlatKernel

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## K. Assembly: the soft premise `InteriorSoft` of round 1 holds -/
section FlatCarrier

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilU)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantCLM_L2_toLp)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply)

/-- The flat localized carrier form is a sum of three squares (frozen `NsPtD1.flat_ginv_form`,
outside the `DrEquiv` closure, restated for the pinned localized assembly). -/
theorem flat_ginv_form_in (P : IngrBParams) (hU : P.U = flatCfg) (x : ↥(bondSupp P.G)) :
    ⟪x, (dataS selIn selIn P).Ginv x⟫ =
      ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖ ^ 2
      + ‖Tfull P.G P.U (iE P.G x)‖ ^ 2
      + ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 := by
  rw [BaseDataS.inner_Ginv]
  have hD : ⟪x, (dataS selIn selIn P).Dpi x⟫ =
      ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖ ^ 2 := by
    have : ⟪x, (dataS selIn selIn P).Dpi x⟫ = ⟪iE P.G x, DpiFull P.G P.U P.a (iE P.G x)⟫ := by
      show ⟪x, (pE P.G) (DpiFull P.G P.U P.a (iE P.G x))⟫ = _
      rw [pE_inner_right]
    rw [this, hU]
    exact AdalyFormal.StatementLaneG.inner_DpiFull_flat P.G P.a (iE P.G x)
  have hM : ⟪x, (dataS selIn selIn P).Mass x⟫ =
      ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 := by
    have : ⟪x, (dataS selIn selIn P).Mass x⟫ = ⟪iE P.G x, MassFull P.G P.a P.sector (iE P.G x)⟫ := by
      show ⟪x, (pE P.G) (MassFull P.G P.a P.sector (iE P.G x))⟫ = _
      rw [pE_inner_right]
    rw [this, inner_MassFull]
    rfl
  rw [hD, hM]
  rfl

/-- The flat localized carrier of the dilated tower is positive definite. -/
theorem dil_flat_pos {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (x : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) (hx : x ≠ 0) :
    0 < ⟪x, (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R))).Ginv x⟫ := by
  set P := gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (fun _ => 1) 1 (dilLam q R) with hP
  have hform := flat_ginv_form_in P rfl x
  have t1 := sq_nonneg ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖
  have t2 := sq_nonneg ‖Tfull P.G P.U (iE P.G x)‖
  have hell : (0 : ℝ) < P.ell := by show (0 : ℝ) < (2 : ℕ); norm_num
  have t3 : 0 ≤ ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 :=
    Finset.sum_nonneg (fun p _ => by
      have : (0 : ℝ) < P.a := by show (0 : ℝ) < 1; norm_num
      positivity)
  rcases (add_nonneg (add_nonneg t1 t2) t3).lt_or_eq with h | h
  · rw [hform]; exact h
  · exfalso
    apply hx
    have h1 : ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖ ^ 2 = 0 := by
      linarith
    have h2 : ‖Tfull P.G P.U (iE P.G x)‖ ^ 2 = 0 := by linarith
    have h3 : ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 = 0 := by
      linarith
    have hm : plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x)) = 0 :=
      norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)
    have hT : Tfull P.G P.U (iE P.G x) = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
    have hQ : QfullOf (geomOf 2 1 (dilTower q R)) flatCfg (iE P.G x) = 0 := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => by
        have : (0 : ℝ) < P.a := by show (0 : ℝ) < 1; norm_num
        positivity)).mp h3
      refine PiLp.ext (fun p => ?_)
      have h1 := hz p (Finset.mem_univ p)
      have hp : 0 < P.a * (P.ell : ℝ) ^ (p.1 : ℕ) := by
        have : (0 : ℝ) < P.a := by show (0 : ℝ) < 1; norm_num
        positivity
      have h2 : ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact absurd h hp.ne'
        · exact h
      have := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
      exact this
    have hsupp : ∀ b, b ∉ bondsOm0 (geomOf 2 1 (dilTower q R)) → (iE P.G x) b = 0 :=
      fun b hb => x.2 b hb
    have hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0),
        curlValueCovariant flatCfg (WithLp.ofLp (iE P.G x)) p = 0 := by
      intro p hp
      have h := congrArg (fun v : AdalyFormal.Balaban.CovariantHjMinimizer.PlaqFnL2 P.Lf => WithLp.ofLp v p) hm
      simp only [plaqMask_apply, PiLp.zero_apply] at h
      rw [if_pos (show p ∈ plaqIn P.G.Om0 from hp)] at h
      have e : curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x) =
          WithLp.toLp 2 (curlValueCovariant flatCfg (WithLp.ofLp (iE P.G x))) :=
        curlCovariantCLM_L2_toLp _ _
      rw [e] at h
      exact h
    have hA := dil_flat_kernel hq hR (iE P.G x) hsupp hQ hcurl hT
    exact Subtype.ext hA

theorem dil_flat_unit {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) :
    IsUnit (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R))).Ginv := by
  set M : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
    (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R))).Ginv with hMdef
  have hinj : Function.Injective M := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hne
    have := dil_flat_pos hq hR x hne
    rw [hx, inner_zero_right] at this
    exact lt_irrefl _ this
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (M : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →ₗ[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))))).mp hinj⟩

end FlatCarrier

end AdalyFormal.Round9.Guarded.AnalyticR2

namespace AdalyFormal.Round13.Positivity.Local
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round12.Noncancel.Path
open AdalyFormal.Round2.Guarded.Pin

/-- The localized data are EXACTLY flat at every angle of this right star. -/
theorem rightStar_local_data_flat {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (a t : ℝ) :
    dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (rightStar hq R t) a (dilLam q R)) =
    dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) a (dilLam q R)) := by
  let P := gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
    (fun _ => 1) a (dilLam q R)
  have hroom : 17*2 ≤ R*(2*q) := by nlinarith
  have hbd := rightSite_bd hq R
  have hboth : ∀ e : Bond (scaleUp 2 1 (dilLu q R)),
      BothIn ((dilTower q R).Om 0) e → P.U e = rightStar hq R t e := by
    intro e he
    symm
    exact starPath_interior _ _ hbd.hx' hbd.trans t e he.1
  exact AdalyFormal.StatementLaneR8.data_congr P (dil_admissible hq hR)
    (by norm_num) hroom (rightStar hq R t) hboth

/-- Unconditional localized strict positivity for every q>0, even R>=18 and
EVERY real angle. This is the localized carrier, not the all-plaquette P2 claim. -/
theorem rightStar_local_positive {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (t : ℝ) (x : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) (hx : x ≠ 0) :
    0 < ⟪x, (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (rightStar hq R t) 1 (dilLam q R))).Ginv x⟫ := by
  rw [rightStar_local_data_flat hq hR hR18]
  exact AdalyFormal.Round9.Guarded.AnalyticR2.dil_flat_pos hq (by omega) x hx

/-- Nested cofinal localized positivity, not a reversed forall/exists order. -/
theorem cofinal_rightStar_local_positive :
    ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
      ∀ t : ℝ, ∀ x : ↥(bondSupp (geomOf 2 1 (dilTower (2^j) R))), x ≠ 0 →
        0 < ⟪x, (dataS selIn selIn (gparams 2 1 (dilLu (2^j) R) (by norm_num)
          (dilTower (2^j) R) (rightStar (by positivity) R t) 1
          (dilLam (2^j) R))).Ginv x⟫ := by
  intro j₀
  refine ⟨j₀,le_rfl,?_⟩
  intro R₀
  let R := 2*(R₀+18)
  have hR : 2 ∣ R := ⟨R₀+18,rfl⟩
  have hR18 : 18 ≤ R := by dsimp [R]; omega
  refine ⟨R,by dsimp [R]; omega,hR,hR18,?_⟩
  intro t x hx
  exact rightStar_local_positive (by positivity) hR hR18 t x hx

set_option pp.fullNames true
#print axioms rightStar_local_data_flat
#print axioms rightStar_local_positive
#print axioms cofinal_rightStar_local_positive
end AdalyFormal.Round13.Positivity.Local

namespace AdalyFormal.Round9.Guarded.AnalyticR1
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative

abbrev TwistSpace (q R : ℕ) : Type := ↥(bondSupp (geomOf 2 1 (dilTower q R)))

end AdalyFormal.Round9.Guarded.AnalyticR1

namespace AdalyFormal.Round12.Kernel.Actual
open AdalyFormal.Target.ClayStatement AdalyFormal.StatementLane
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
/-- The physical charged entry at one actual touching-bond coordinate. -/
def chargedCoordinate (q R : ℕ) (b : Bond (scaleUp 2 1 (dilLu q R))) :
    TwistSpace q R →ₗ[ℝ] ℂ where
  toFun u := ((u : BondFnL2 (scaleUp 2 1 (dilLu q R))) b : Matrix (Fin 2) (Fin 2) ℂ) 0 1
  map_add' u v := rfl
  map_smul' c u := by
    change ((c : ℂ) * _) = _
    rfl

end AdalyFormal.Round12.Kernel.Actual

namespace AdalyFormal.Round13.Positivity.Physical
open Classical
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLaneR6
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Round12.Noncancel.Path
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round13.Positivity.Leaves
open AdalyFormal.Round13.Positivity.Local
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round12.Kernel.Actual (chargedCoordinate)

/-- Every localized right-star plaquette really is flat. -/
theorem rightStar_local_hol {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ)
    (p : PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)))
    (hp : p ∈ plaqIn ((dilTower q R).Om 0)) :
    reHolonomy (rightStar hq R t) p = 1 ∧ imHolonomy (rightStar hq R t) p = 0 := by
  have hU : ∀ e ∈ periodicPlaquetteBoundaryEdges p, rightStar hq R t e = 1 := by
    intro e he
    exact starPath_interior _ _ (rightSite_bd hq R).hx' (rightSite_bd hq R).trans t e (hp e he).1
  apply hol_flat_components
  unfold holonomyElem periodicPlaquetteHolonomy
  dsimp only
  rw [hU _ ((edge_mem p _).mpr (Or.inl rfl)),
    hU _ ((edge_mem p _).mpr (Or.inr (Or.inl rfl))),
    hU _ ((edge_mem p _).mpr (Or.inr (Or.inr (Or.inl rfl)))),
    hU _ ((edge_mem p _).mpr (Or.inr (Or.inr (Or.inr rfl))))]
  simp

/-- UNCONDITIONAL physical comparison on the central-charged-zero subspace.
The multiplicative constant cos(t) is independent of scale and radius. -/
theorem rightStar_carrier_lower {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (t : ℝ) (ht : 0 ≤ Real.cos t) (u : TwistSpace q R)
    (hu : chargedCoordinate q R (rightSite hq R,(0 : Fin 3)) u = 0) :
    Real.cos t * ⟪u, (dataS selIn selIn
      (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
        (rightStar hq R t) 1 (dilLam q R))).Ginv u⟫ ≤
      ⟪u, vacA q R (rightStar hq R) 1 t u⟫ := by
  rw [vacA_rightStar]
  let P := gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
    (rightStar hq R t) 1 (dilLam q R)
  apply carrier_ge_scaled_local P u (Real.cos t)
    (∑ i : Fin 8, ‖(iE P.G u) (leaf hq R i)‖^2) (Real.cos_le_one t)
  · apply localized_Dpi_nonneg
    · intro p hp; exact (rightStar_local_hol hq R t p hp).1
    · intro p hp; exact (rightStar_local_hol hq R t p hp).2
  · change _ ≤ ⟪u,pE P.G (MassFull P.G P.a (bondSectorOf P.G P.U) (iE P.G u))⟫
    rw [pE_inner_right]
    exact eight_leaf_mass hq hR (by omega) P.U (iE P.G u)
  · exact rightStar_omitted_loss hq hR hR18 t ht u hu

/-- Strict positivity includes t=0 and every strict half-pi prefix. -/
theorem rightStar_zero_coordinate_positive {q R : ℕ}
    (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (t : ℝ) (ht0 : 0 ≤ t) (ht : t < Real.pi/2)
    (u : TwistSpace q R) (hu : u ≠ 0)
    (hz : chargedCoordinate q R (rightSite hq R,(0 : Fin 3)) u = 0) :
    0 < ⟪u, vacA q R (rightStar hq R) 1 t u⟫ := by
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],ht⟩
  exact lt_of_lt_of_le (mul_pos hc (rightStar_local_positive hq hR hR18 t u hu))
    (rightStar_carrier_lower hq hR hR18 t hc.le u hz)

/-- A single scale/radius-independent positive factor works on every closed
prefix [0,T] below half pi, relative to the genuine FLAT localized form. -/
theorem rightStar_prefix_lower {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (T t : ℝ) (hT0 : 0 ≤ T) (hT : T < Real.pi/2) (ht0 : 0 ≤ t) (ht : t ≤ T)
    (u : TwistSpace q R)
    (hu : chargedCoordinate q R (rightSite hq R,(0 : Fin 3)) u = 0) :
    0 < Real.cos T ∧
    Real.cos T * ⟪u, (dataS selIn selIn
      (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
        (fun _ => 1) 1 (dilLam q R))).Ginv u⟫ ≤
      ⟪u, vacA q R (rightStar hq R) 1 t u⟫ := by
  have hc := cos_prefix_loss T t hT0 hT ht0 ht
  have hflat : dataS selIn selIn
      (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
        (rightStar hq R t) 1 (dilLam q R)) =
      dataS selIn selIn
      (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
        (fun _ => 1) 1 (dilLam q R)) := rightStar_local_data_flat hq hR hR18 1 t
  have hb := rightStar_carrier_lower hq hR hR18 t (hc.1.le.trans hc.2.1) u hu
  rw [hflat] at hb
  refine ⟨hc.1, (mul_le_mul_of_nonneg_right hc.2.1 ?_).trans hb⟩
  by_cases hz : u = 0
  · simp [hz]
  · have hp : 0 < ⟪u,(dataS selIn selIn
        (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
          (rightStar hq R t) 1 (dilLam q R))).Ginv u⟫ :=
        rightStar_local_positive hq hR hR18 t u hz
    rw [hflat] at hp
    exact hp.le

set_option linter.unusedVariables false in
/-- P2 VERBATIM, no extra analytic, geometric, inverse or spectral hypothesis. -/
theorem rightStar_P2 :
    ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
      (t : ℝ), 0 < t → t < Real.pi/2 →
      ∀ x : TwistSpace q R, x ≠ 0 →
        AdalyFormal.Round12.Kernel.Actual.chargedCoordinate q R
          (rightSite hq R, (0 : Fin 3)) x = 0 →
        0 < ⟪x, vacA q R (rightStar hq R) 1 t x⟫ := by
  intro q R hq hR hR18 t ht0 ht x hx hz
  exact rightStar_zero_coordinate_positive hq hR hR18 t ht0.le ht x hx hz

/-- Nested cofinal scales/radii, with the interval and ALL full carrier fields
quantified after the SAME chosen radius. -/
theorem cofinal_rightStar_P2 :
    ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
      ∀ (t : ℝ), 0 < t → t < Real.pi/2 →
        ∀ x : TwistSpace (2^j) R, x ≠ 0 →
          chargedCoordinate (2^j) R (rightSite (by positivity) R, (0 : Fin 3)) x = 0 →
          0 < ⟪x, vacA (2^j) R (rightStar (by positivity) R) 1 t x⟫ := by
  intro j₀
  refine ⟨j₀,le_rfl,?_⟩
  intro R₀
  refine ⟨2*(R₀+18),by omega,⟨R₀+18,rfl⟩,by omega,?_⟩
  exact rightStar_P2 (by positivity) ⟨R₀+18,rfl⟩ (by omega)

end AdalyFormal.Round13.Positivity.Physical
#print axioms AdalyFormal.Round13.Positivity.Physical.rightStar_local_hol
#print axioms AdalyFormal.Round13.Positivity.Physical.rightStar_carrier_lower
#print axioms AdalyFormal.Round13.Positivity.Physical.rightStar_zero_coordinate_positive
#print axioms AdalyFormal.Round13.Positivity.Physical.rightStar_prefix_lower
#print axioms AdalyFormal.Round13.Positivity.Physical.rightStar_P2
#print axioms AdalyFormal.Round13.Positivity.Physical.cofinal_rightStar_P2
#check @AdalyFormal.Round13.Positivity.Physical.rightStar_P2
#check @AdalyFormal.Round13.Positivity.Physical.cofinal_rightStar_P2
