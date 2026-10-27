
/-! Round 15 seed R2: complex two-layer seed algebra, an arbitrary-remainder
vector-limit interface, and a fixed finite leading-constant computation. -/

namespace AdalyFormal.Round14.Cancellation

open scoped ComplexConjugate

/-- Complex phase/amplitude scaling of the genuine charged form, copied from the
compiled round-14 cancellation algebra so it is available in this compact file. -/
theorem chargedArea_smul {ι : Type*} [Fintype ι] (K : ι → ι → ℝ) (z : ι → ℂ) (c : ℂ) :
    chargedArea K (fun e => c * z e) = Complex.normSq c * chargedArea K z := by
  have ht (e d : ι) : (c * z e * conj (c * z d)).im * K e d =
      Complex.normSq c * ((z e * conj (z d)).im * K e d) := by
    have h : c * z e * conj (c * z d) =
        (Complex.normSq c : ℂ) * (z e * conj (z d)) := by
      rw [map_mul]
      calc
        _ = (c * conj c) * (z e * conj (z d)) := by ring
        _ = _ := by rw [Complex.mul_conj]
    rw [h]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  unfold chargedArea
  simp_rw [ht]
  calc
    _ = ∑ e : ι, Complex.normSq c * ∑ d : ι, (z e * conj (z d)).im * K e d := by
      apply Finset.sum_congr rfl
      intro e _
      exact (Finset.mul_sum Finset.univ _ _).symm
    _ = _ := (Finset.mul_sum Finset.univ _ _).symm

#print axioms chargedArea_smul

end AdalyFormal.Round14.Cancellation

/-! The two sparse-mode definitions from dictionary R1 needed by the fixed
finite leading-constant check.  No physical identification is added here. -/
namespace AdalyFormal.Round15.Dictionary

noncomputable section

def phase : ℂ := (1+Complex.I)/(Real.sqrt 2:ℂ)

def mode0 : Fin 8 → ℂ
  | 0 => 1 | 1 => phase | 2 => 1 | 3 => phase | _ => 0

end

end AdalyFormal.Round15.Dictionary

noncomputable section
namespace AdalyFormal.Round15.Seed

open scoped RealInnerProductSpace Matrix Topology ComplexConjugate
open Filter
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round10.Assembly.R2 (KernelLine)
open AdalyFormal.Round10.Nonvanishing.DilatedFlux (blockCount G L)
open AdalyFormal.Round12.Noncancel.RightFamily (rightStar)
open AdalyFormal.Round13.Detection.PhysicalArea
open AdalyFormal.Round14.Cancellation
open AdalyFormal.Round14.Transfer

/-- Real scaling is the `normSq` scaling theorem specialized to a real scalar. -/
theorem chargedArea_real_smul {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (z : ι → ℂ) (c : ℝ) :
    chargedArea K (c • z) = c^2 * chargedArea K z := by
  have h := AdalyFormal.Round14.Cancellation.chargedArea_smul K z (c : ℂ)
  change chargedArea K (fun e => (c : ℂ) * z e) = c^2 * chargedArea K z
  simpa only [Complex.normSq_ofReal, pow_two] using h

/-- The real sesquilinear summand before taking its diagonal. -/
def chargedBilin {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (z w : ι → ℂ) : ℝ :=
  ∑ e : ι, ∑ d : ι, (z e * conj (w d)).im * K e d

/-- The symmetric cross term in a two-branch expansion. -/
def chargedMixed {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (z w : ι → ℂ) : ℝ :=
  chargedBilin K z w + chargedBilin K w z

theorem chargedArea_eq_chargedBilin {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (z : ι → ℂ) :
    chargedArea K z = chargedBilin K z z := rfl

theorem chargedBilin_add_left {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (x y z : ι → ℂ) :
    chargedBilin K (x + y) z = chargedBilin K x z + chargedBilin K y z := by
  unfold chargedBilin
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  simp only [Pi.add_apply, add_mul, Complex.add_im]

theorem chargedBilin_add_right {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (x y z : ι → ℂ) :
    chargedBilin K x (y + z) = chargedBilin K x y + chargedBilin K x z := by
  unfold chargedBilin
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  simp only [Pi.add_apply, map_add, mul_add, Complex.add_im]
  ring

theorem chargedBilin_real_smul_left {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (z w : ι → ℂ) (c : ℝ) :
    chargedBilin K (c • z) w = c * chargedBilin K z w := by
  have ht (e d : ι) : ((c • z) e * conj (w d)).im * K e d =
      c * ((z e * conj (w d)).im * K e d) := by
    simp only [Pi.smul_apply, Complex.real_smul,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  unfold chargedBilin
  simp_rw [ht]
  calc
    _ = ∑ e : ι, c * ∑ d : ι, (z e * conj (w d)).im * K e d := by
      apply Finset.sum_congr rfl
      intro e _
      exact (Finset.mul_sum Finset.univ _ _).symm
    _ = _ := (Finset.mul_sum Finset.univ _ _).symm

theorem chargedBilin_real_smul_right {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (z w : ι → ℂ) (c : ℝ) :
    chargedBilin K z (c • w) = c * chargedBilin K z w := by
  have ht (e d : ι) : (z e * conj ((c • w) d)).im * K e d =
      c * ((z e * conj (w d)).im * K e d) := by
    simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  unfold chargedBilin
  simp_rw [ht]
  calc
    _ = ∑ e : ι, c * ∑ d : ι, (z e * conj (w d)).im * K e d := by
      apply Finset.sum_congr rfl
      intro e _
      exact (Finset.mul_sum Finset.univ _ _).symm
    _ = _ := (Finset.mul_sum Finset.univ _ _).symm

/-- A two-layer charged seed transported in the two reciprocal branches.  The
vectors may concatenate all transverse components and both interface layers. -/
def chargedTwoLayerMode {ι : Type*} [Fintype ι]
    (r : ℝ) (z w : ι → ℂ) (n : ℕ) : ι → ℂ :=
  (r^n) • z + ((r⁻¹)^n) • w

/-- Exact charged-area Laurent expansion.  Its three fixed coefficients are
respectively the decaying, mixed, and growing seed areas; no scalar decoupling
or sign assumption is made. -/
theorem chargedArea_twoLayerMode {ι : Type*} [Fintype ι]
    {r : ℝ} (hr : r ≠ 0) (K : ι → ι → ℝ) (z w : ι → ℂ) (n : ℕ) :
    chargedArea K (chargedTwoLayerMode r z w n) =
      laurent (r^2) (chargedArea K z) (chargedMixed K z w) (chargedArea K w) n := by
  rw [chargedArea_eq_chargedBilin]
  simp only [chargedTwoLayerMode, chargedBilin_add_left, chargedBilin_add_right,
    chargedBilin_real_smul_left, chargedBilin_real_smul_right]
  rw [← chargedArea_eq_chargedBilin, ← chargedArea_eq_chargedBilin]
  simp only [chargedMixed, laurent, pow_succ, inv_pow]
  apply (mul_left_inj' (pow_ne_zero (2*n) hr)).mp
  field_simp [pow_ne_zero n hr, pow_ne_zero (n+1) hr]
  ring

/-- The exact two-layer observable on the admissible even-radius progression. -/
def radiusChargedTwoLayerObservable {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (r : ℝ) (z w : ι → ℂ) : ℕ → ℕ → ℝ :=
  fun _ R => chargedArea K (chargedTwoLayerMode r z w (R/2 - 9))

/-- The fixed finite seed coefficients supply a compiled Laurent certificate. -/
theorem radiusLaurentData_of_chargedTwoLayer {q : ℕ} {ι : Type*} [Fintype ι]
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (K : ι → ι → ℝ) (z w : ι → ℂ)
    (hseed : chargedArea K z ≠ 0 ∨ chargedMixed K z w ≠ 0 ∨ chargedArea K w ≠ 0) :
    RadiusLaurentData (radiusChargedTwoLayerObservable K r z w) q := by
  refine ⟨r^2, chargedArea K z, chargedMixed K z w, chargedArea K w,
    sq_pos_of_pos hr0, by nlinarith, hseed, ?_⟩
  intro n
  have hidx : 2*(n+9)/2 - 9 = n := by omega
  simpa only [radiusChargedTwoLayerObservable, hidx] using
    chargedArea_twoLayerMode (ne_of_gt hr0) K z w n

/-- A vector-valued leading certificate permits an arbitrary remainder in both
the finite coordinate matrices and the generator coordinates.  The vector rate
is `s`; charged area, being quadratic, has rate `s^2`. -/
def ChargedVectorLeading {ι : Type*} [Fintype ι]
    (s : ℝ) (K : ℕ → ι → ι → ℝ) (K0 : ι → ι → ℝ)
    (z : ℕ → ι → ℂ) (z0 : ι → ℂ) : Prop :=
  0 < s ∧ z0 ≠ 0 ∧ chargedArea K0 z0 ≠ 0 ∧
    Tendsto (fun n => (s^n)⁻¹ • z n) atTop (𝓝 z0) ∧
    Tendsto K atTop (𝓝 K0)

/-- Joint matrix/vector convergence gives the normalized charged-area limit. -/
theorem tendsto_chargedArea_vector {ι : Type*} [Fintype ι]
    {s : ℝ} {K : ℕ → ι → ι → ℝ} {K0 : ι → ι → ℝ}
    {z : ℕ → ι → ℂ} {z0 : ι → ℂ} (hs : s ≠ 0)
    (hz : Tendsto (fun n => (s^n)⁻¹ • z n) atTop (𝓝 z0))
    (hK : Tendsto K atTop (𝓝 K0)) :
    Tendsto (fun n => chargedArea (K n) (z n) / (s^2)^n) atTop
      (𝓝 (chargedArea K0 z0)) := by
  have heq : (fun n => chargedArea (K n) (z n) / (s^2)^n) =
      (fun n => chargedArea (K n) ((s^n)⁻¹ • z n)) := by
    funext n
    rw [chargedArea_real_smul]
    field_simp [pow_ne_zero n hs]
    ring
  rw [heq]
  unfold chargedArea
  apply tendsto_finsetSum
  intro e _
  apply tendsto_finsetSum
  intro d _
  have he := tendsto_pi_nhds.mp hz e
  have hd := tendsto_pi_nhds.mp hz d
  have hc : Tendsto (fun n => conj (((s^n)⁻¹ • z n) d)) atTop
      (𝓝 (conj (z0 d))) :=
    (Complex.continuous_conj.tendsto _).comp hd
  have him : Tendsto
      (fun n => (((s^n)⁻¹ • z n) e * conj (((s^n)⁻¹ • z n) d)).im) atTop
      (𝓝 ((z0 e * conj (z0 d)).im)) :=
    (Complex.continuous_im.tendsto _).comp (he.mul hc)
  have hKed := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hK e) d
  exact him.mul hKed

/-- The vector observable on the exact even-radius progression. -/
def radiusChargedVectorObservable {ι : Type*} [Fintype ι]
    (K : ℕ → ι → ι → ℝ) (z : ℕ → ι → ℂ) : ℕ → ℕ → ℝ :=
  fun _ R => chargedArea (K (R/2 - 9)) (z (R/2 - 9))

/-- Convert a vector leading certificate to the already compiled dominant-data
interface.  Nonzero seed and nonzero charged area remain separate conjuncts. -/
theorem radiusDominantData_of_chargedVectorLeading {q : ℕ} {ι : Type*} [Fintype ι]
    {s : ℝ} {K : ℕ → ι → ι → ℝ} {K0 : ι → ι → ℝ}
    {z : ℕ → ι → ℂ} {z0 : ι → ℂ}
    (h : ChargedVectorLeading s K K0 z z0) :
    RadiusDominantData (radiusChargedVectorObservable K z) q := by
  obtain ⟨hs, _, harea, hz, hK⟩ := h
  refine ⟨s^2, chargedArea K0 z0, sq_pos_of_pos hs, harea, ?_⟩
  have ht := tendsto_chargedArea_vector (ne_of_gt hs) hz hK
  have hidx (n : ℕ) : 2*(n+9)/2 - 9 = n := by omega
  simpa only [radiusChargedVectorObservable, hidx] using ht

/-- A growing two-layer branch is a concrete vector leading certificate.  The
other branch and mixed term are precisely the exponentially smaller remainder. -/
theorem chargedVectorLeading_of_twoLayer {ι : Type*} [Fintype ι]
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (K : ι → ι → ℝ) (z w : ι → ℂ)
    (hw : w ≠ 0) (harea : chargedArea K w ≠ 0) :
    ChargedVectorLeading (r⁻¹) (fun _ => K) K (chargedTwoLayerMode r z w) w := by
  have hr : r ≠ 0 := ne_of_gt hr0
  have hr2 : |(r^2 : ℝ)| < 1 := by
    rw [abs_of_pos (sq_pos_of_pos hr0)]
    nlinarith
  have hp : Tendsto (fun n => (r^2)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr2
  have hpz : Tendsto (fun n => ((r^2)^n) • z) atTop (𝓝 0) := by
    simpa using hp.smul (tendsto_const_nhds : Tendsto (fun _ => z) atTop (𝓝 z))
  have heq : (fun n => ((r⁻¹)^n)⁻¹ • chargedTwoLayerMode r z w n) =
      (fun n => ((r^2)^n) • z + w) := by
    funext n
    simp only [chargedTwoLayerMode, inv_pow, inv_inv, smul_add, smul_smul]
    rw [mul_inv_cancel₀ (pow_ne_zero n hr), one_smul]
    congr 1
    rw [← mul_pow]
    congr 1
    ring
  refine ⟨inv_pos.mpr hr0, hw, harea, ?_, tendsto_const_nhds⟩
  rw [heq]
  simpa using hpz.add (tendsto_const_nhds : Tendsto (fun _ => w) atTop (𝓝 w))

/-- Exact physical input for the arbitrary-remainder vector interface.  All
indices, the same unit generator, and the genuine area are retained. -/
def ChargedVectorData (q : ℕ) (hq : 0 < q) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (s : ℝ) (K : ℕ → ι → ι → ℝ)
    (K0 : ι → ι → ℝ) (z : ℕ → ι → ℂ) (z0 : ι → ℂ),
    ChargedVectorLeading s K K0 z z0 ∧
    ∀ n : ℕ, ∃ u : TwistSpace q (2*(n+9)),
      KernelLine q (2*(n+9)) (rightStar hq (2*(n+9))) u ∧ ‖u‖ = 1 ∧
      ∃ k : ℕ, ∃ hk : k < blockCount q (2*(n+9)),
        areaSum hq hk u = chargedArea (K n) (z n)

/-- Only cofinally many dyadic scales are required; each selected scale still
has the full even-radius progression and a common finite coordinate system. -/
def CofinalChargedVectorCertificate : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ChargedVectorData (2^j) (by positivity)

/-- Main conditional reduction from the vector leading dictionary to the
preferred normalized cofinal area seed. -/
theorem cofinalUnitDominantAreaSeed_of_chargedVector
    (h : CofinalChargedVectorCertificate) :
    AdalyFormal.Round14.Transfer.Physical.CofinalUnitDominantAreaSeed := by
  intro j₀
  obtain ⟨j, hj, ι, hι, s, K, K0, z, z0, hlead, hident⟩ := h j₀
  letI := hι
  refine ⟨j, hj, radiusChargedVectorObservable K z,
    radiusDominantData_of_chargedVectorLeading hlead, ?_⟩
  intro n
  obtain ⟨u, hline, hnorm, k, hk, harea⟩ := hident n
  refine ⟨u, hline, hnorm, k, hk, ?_⟩
  rw [harea]
  have hidx : 2*(n+9)/2 - 9 = n := by omega
  simp only [radiusChargedVectorObservable, hidx]

/-- A fixed algebraic matrix on the actual eight-component sparse-mode index
space.  This is a model leading form, not an assertion about the frozen area. -/
def collarTestMatrix : Fin 8 → Fin 8 → ℝ := fun e d =>
  if e = 0 ∧ d = 1 then -1 else if e = 1 ∧ d = 0 then 1 else 0

set_option maxRecDepth 10000

/-- Exact algebraic leading constant on dictionary R1's sparse charged mode. -/
theorem collarTestLeadingConstant :
    chargedArea collarTestMatrix AdalyFormal.Round15.Dictionary.mode0 = Real.sqrt 2 := by
  have hs2 : 0 ≤ (2 : ℝ) := by norm_num
  have hsquare := Real.sq_sqrt hs2
  have hsne : Real.sqrt 2 ≠ 0 := by positivity
  norm_num +decide [chargedArea, collarTestMatrix, AdalyFormal.Round15.Dictionary.mode0,
    AdalyFormal.Round15.Dictionary.phase, Fin.sum_univ_eight,
    Complex.mul_re, Complex.mul_im]
  field_simp [hsne]
  ring_nf
  rw [hsquare]

theorem collarTestLeadingConstant_ne_zero :
    chargedArea collarTestMatrix AdalyFormal.Round15.Dictionary.mode0 ≠ 0 := by
  rw [collarTestLeadingConstant]
  positivity

theorem dictionary_mode0_ne_zero : AdalyFormal.Round15.Dictionary.mode0 ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [AdalyFormal.Round15.Dictionary.mode0] at h0

/-- The fixed model has a genuine normalized vector limit with the dictionary's
reciprocal dominant branch and an exact nonzero algebraic leading constant. -/
theorem collarModelLeading (z : Fin 8 → ℂ) :
    ChargedVectorLeading (dominantRho⁻¹) (fun _ => collarTestMatrix) collarTestMatrix
      (chargedTwoLayerMode dominantRho z AdalyFormal.Round15.Dictionary.mode0)
      AdalyFormal.Round15.Dictionary.mode0 :=
  chargedVectorLeading_of_twoLayer dominantRho_pos dominantRho_lt_one collarTestMatrix z
    AdalyFormal.Round15.Dictionary.mode0 dictionary_mode0_ne_zero
    collarTestLeadingConstant_ne_zero

#print axioms chargedArea_real_smul
#print axioms chargedBilin
#print axioms chargedMixed
#print axioms chargedBilin_add_left
#print axioms chargedBilin_add_right
#print axioms chargedBilin_real_smul_left
#print axioms chargedBilin_real_smul_right
#print axioms chargedTwoLayerMode
#print axioms chargedArea_twoLayerMode
#print axioms radiusChargedTwoLayerObservable
#print axioms radiusLaurentData_of_chargedTwoLayer
#print axioms ChargedVectorLeading
#print axioms tendsto_chargedArea_vector
#print axioms radiusChargedVectorObservable
#print axioms radiusDominantData_of_chargedVectorLeading
#print axioms chargedVectorLeading_of_twoLayer
#print axioms ChargedVectorData
#print axioms CofinalChargedVectorCertificate
#print axioms cofinalUnitDominantAreaSeed_of_chargedVector
#print axioms collarTestMatrix
#print axioms collarTestLeadingConstant
#print axioms collarTestLeadingConstant_ne_zero
#print axioms dictionary_mode0_ne_zero
#print axioms collarModelLeading

end AdalyFormal.Round15.Seed
