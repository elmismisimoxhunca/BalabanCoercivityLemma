/-! Compact concrete glue. No cofinal coupling is asserted without a premise. -/
namespace AdalyFormal.Round10.Assembly.R2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

/-- Symmetry of a derivative, including its totalized value at nonsmooth points.
This does not claim differentiability; round 9 proves that separately. -/
theorem deriv_symmetric {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : ℝ → E →L[ℝ] E) (hs : ∀ t x y, ⟪D t x, y⟫ = ⟪x, D t y⟫)
    (t : ℝ) (x y : E) : ⟪deriv D t x, y⟫ = ⟪x, deriv D t y⟫ := by
  by_cases hd : DifferentiableAt ℝ D t
  · have hd' : HasDerivAt D (deriv D t) t := hd.hasDerivAt
    let L := (innerSL ℝ y).comp (ContinuousLinearMap.apply ℝ E x)
    let M := (innerSL ℝ x).comp (ContinuousLinearMap.apply ℝ E y)
    have hl := L.hasFDerivAt.comp_hasDerivAt t hd'
    have hm := M.hasFDerivAt.comp_hasDerivAt t hd'
    have he : (fun s => L (D s)) = fun s => M (D s) := by
      funext s
      exact (real_inner_comm (D s x) y).trans (hs s x y)
    change HasDerivAt (fun s => L (D s)) (L (deriv D t)) t at hl
    rw [he] at hl
    exact (real_inner_comm y (deriv D t x)).trans (hl.unique hm)
  · rw [deriv_zero_of_not_differentiableAt hd]
    simp

/-- The actual round-9 coefficient is symmetric at every instance, with no
regularity premise added to the compact source-to-coupling bridge. -/
theorem corrDeriv_symmetric (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (x y : TwistSpace q R) :
    ⟪corrDeriv q R f x, y⟫ = ⟪x, corrDeriv q R f y⟫ :=
  deriv_symmetric (fun ε => bulkD q R f ε)
    (fun ε => ((dataS selIn selIn (bulkP q R f ε)).Delta2_spec
      (dataS_laws selIn selIn _)).1) 0 x y

/-- Full-kernel geometry for any exterior path. There is no assertion that a
selected character exhausts the kernel unless the last clause is proved. -/
def KernelLine (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (u₀ : TwistSpace q R) : Prop :=
  u₀ ≠ 0 ∧ vacA q R V 1 (vacEdge q R V) u₀ = 0 ∧
  adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
    (adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀) = -u₀ ∧
  (∀ u, vacA q R V 1 (vacEdge q R V) u = 0 →
    u ∈ Submodule.span ℝ {u₀,
      adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀})

/-- A concrete, compiled substitute for the uncompiled r1 glue. It works for
any exterior path, and consumes no unproved soft-regularity assumption. -/
theorem canonicalCoupling_of_line {q R : ℕ}
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (u₀ : TwistSpace q R)
    (hline : KernelLine q R V u₀) (hc : ⟪u₀, corrDeriv q R f u₀⟫ ≠ 0) :
    CanonicalCoupling q R V (corrDeriv q R f) := by
  obtain ⟨hu₀, -, hJJ, hK⟩ := hline
  let J := adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
  let Jop : TwistSpace q R →L[ℝ] TwistSpace q R :=
    J.toLinearIsometry.toContinuousLinearMap
  obtain ⟨l, hl⟩ := scalar_on_complex_line (corrDeriv q R f) Jop
    (corrDeriv_symmetric q R f) (fun x y => J.inner_map_map x y)
    (fun x => Dictionary.Actual.corrDeriv_U1 q R f (Real.pi / 4) x) u₀ hu₀ hJJ
  have hmem : u₀ ∈ Submodule.span ℝ {u₀, Jop u₀} := Submodule.subset_span (by simp)
  have hl0 : l ≠ 0 := by
    intro h0
    apply hc
    rw [hl u₀ hmem, h0, zero_mul]
  rcases lt_or_gt_of_ne hl0 with hneg | hpos
  · refine ⟨-l, by linarith, Or.inr (fun u hu => ?_)⟩
    have h1 := hl u (hK u hu)
    linarith
  · refine ⟨l, hpos, Or.inl (fun u hu => ?_)⟩
    exact le_of_eq (hl u (hK u hu)).symm

/-- Finite-source cancellation is discharged by the shared R1 estimate.
The source identification, jet hypotheses and full kernel still must be supplied. -/
theorem canonicalCoupling_of_dominatedSource {q R : ℕ}
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (u : TwistSpace q R)
    (hline : KernelLine q R V u)
    (hsource : Nonvanishing.BlockSourceData ⟪u, corrDeriv q R f u⟫) :
    CanonicalCoupling q R V (corrDeriv q R f) :=
  canonicalCoupling_of_line V f u hline
    (Nonvanishing.coupling_ne_zero_of_blockSourceData _ hsource)

/-- Missing cofinal hand-off. The body uses the actual carrier and derivative. -/
def CofinalDominatedSource : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ (f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ) (u : TwistSpace (2^j) R),
      KernelLine (2^j) R (uthPath (2^j) R) u ∧
      Nonvanishing.BlockSourceData ⟪u, corrDeriv (2^j) R f u⟫

theorem cofinalAnyProfileCoupling_of_dominatedSource (h : CofinalDominatedSource) :
    CofinalAnyProfileCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, f, u, hline, hsource⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, f,
    canonicalCoupling_of_dominatedSource (uthPath _ _) f u hline hsource⟩

/-- Source error implies a signed lower bound. Unlike the charged-line route,
this is applicable simultaneously to every vector of a higher-dimensional kernel. -/
theorem signed_source_lower (n : ℕ) (a v : ℕ → ℝ)
    (ha : a (n+1) = 0)
    (heq : ∀ j < n+1, 6*a j + Nonvanishing.left a j + a (j+1) =
      if j = 0 then (3/2 : ℝ) else 0)
    (hv : ∀ j < n+1, |v j| ≤ |v 0|) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hpos : 0 ≤ σ * v 0) :
    (4/19 : ℝ) * (σ * v 0) ≤ σ * Nonvanishing.sourcePairing n a v := by
  have he := Nonvanishing.sourcePairing_error n a v ha heq hv
  obtain ⟨hl, hu⟩ := abs_le.mp he
  rcases hσ with rfl | rfl
  · have hz : 0 ≤ v 0 := by simpa using hpos
    rw [abs_of_nonneg hz] at hl
    linarith
  · have hz : v 0 ≤ 0 := by linarith
    rw [abs_of_nonpos hz] at hu
    linarith

/-- Whole-kernel source criterion. No spectral simplicity or character exclusion
is required; instead the first jet must have one coercive sign on the whole kernel.
All operator/source and jet hypotheses are explicit, not established here. -/
theorem canonicalCoupling_of_kernelSource {q R : ℕ}
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (n : ℕ) (a : ℕ → ℝ) (v : TwistSpace q R → ℕ → ℝ)
    (factor δ σ : ℝ) (hf : 0 < factor) (hδ : 0 < δ) (hσ : σ = 1 ∨ σ = -1)
    (ha : a (n+1) = 0)
    (heq : ∀ j < n+1, 6*a j + Nonvanishing.left a j + a (j+1) =
      if j = 0 then (3/2 : ℝ) else 0)
    (hjet : ∀ u, vacA q R V 1 (vacEdge q R V) u = 0 →
      ∀ j < n+1, |v u j| ≤ |v u 0|)
    (hfirst : ∀ u, vacA q R V 1 (vacEdge q R V) u = 0 →
      δ * ‖u‖^2 ≤ σ * v u 0)
    (hform : ∀ u, vacA q R V 1 (vacEdge q R V) u = 0 →
      ⟪u, corrDeriv q R f u⟫ = factor * Nonvanishing.sourcePairing n a (v u)) :
    CanonicalCoupling q R V (corrDeriv q R f) := by
  have hbound (u : TwistSpace q R) (hu : vacA q R V 1 (vacEdge q R V) u = 0) :
      (factor * (4/19 : ℝ) * δ) * ‖u‖^2 ≤ σ * ⟪u, corrDeriv q R f u⟫ := by
    have hz : 0 ≤ σ * v u 0 :=
      (mul_nonneg hδ.le (sq_nonneg _)).trans (hfirst u hu)
    have hb := signed_source_lower n a (v u) ha heq (hjet u hu) σ hσ hz
    have h1 := mul_le_mul_of_nonneg_left (hfirst u hu) (by norm_num : (0 : ℝ) ≤ 4/19)
    have h2 := mul_le_mul_of_nonneg_left (h1.trans hb) hf.le
    rw [hform u hu]
    nlinarith only [h2]
  refine ⟨factor * (4/19 : ℝ) * δ, by positivity, ?_⟩
  rcases hσ with rfl | rfl
  · exact Or.inl (fun u hu => by simpa using hbound u hu)
  · exact Or.inr (fun u hu => by simpa using hbound u hu)

/-- The R2 source-family theorem removes every first-jet domination hypothesis.
It suffices to identify the actual coupling for a finite family of interior profiles
and prove that at least one component of the actual jet vector is nonzero. -/
theorem exists_profile_coupling_of_sourceFamily {q R : ℕ}
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (u : TwistSpace q R)
    (hline : KernelLine q R V u) (N : ℕ) (b : ℕ → ℝ)
    (profiles : ℕ → Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (factor : ℝ)
    (hb : b N = 0) (hne : ∃ j < N, b j ≠ 0) (hf : factor ≠ 0)
    (hdict : ∀ i < N, ⟪u, corrDeriv q R (profiles i) u⟫ =
      factor * Nonvanishing.FreeProfile.sourceResponse N i b) :
    ∃ i < N, CanonicalCoupling q R V (corrDeriv q R (profiles i)) := by
  obtain ⟨i, hi, hn⟩ := Nonvanishing.FreeProfile.exists_actual_coupling_of_source_dictionary
    N b (fun i => ⟪u, corrDeriv q R (profiles i) u⟫) factor hb hne hf hdict
  exact ⟨i, hi, canonicalCoupling_of_line V (profiles i) u hline hn⟩

/-- Choice-independent version for a dictionary that supplies source amplitudes
satisfying the finite equations, rather than the chosen sourceResponse operator. -/
theorem exists_profile_coupling_of_sourceColumns {q R : ℕ}
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (u : TwistSpace q R)
    (hline : KernelLine q R V u) (N : ℕ) (b : ℕ → ℝ) (c : ℕ → ℕ → ℝ)
    (profiles : ℕ → Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (factor : ℝ)
    (hb : b N = 0) (hne : ∃ j < N, b j ≠ 0) (hf : factor ≠ 0)
    (hc : ∀ i < N, c i N = 0)
    (heq : ∀ i < N, ∀ j < N, 6*c i j + Nonvanishing.FreeProfile.prev (c i) j +
      c i (j+1) = Nonvanishing.FreeProfile.sourceRhs i j)
    (hdict : ∀ i < N, ⟪u, corrDeriv q R (profiles i) u⟫ = factor *
      (∑ j ∈ Finset.range N, Nonvanishing.FreeProfile.columnWeight (c i) i j * b j)) :
    ∃ i < N, CanonicalCoupling q R V (corrDeriv q R (profiles i)) := by
  obtain ⟨i, hi, hn⟩ := Nonvanishing.FreeProfile.exists_coupling_of_source_columns
    N b (fun i => ⟪u, corrDeriv q R (profiles i) u⟫) c factor hb hne hf hc heq hdict
  exact ⟨i, hi, canonicalCoupling_of_line V (profiles i) u hline hn⟩

/-- Exact per-instance unproved hand-off, allowing the source site to vary. -/
def SourceFamilyData (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) : Prop :=
  ∃ (u : TwistSpace q R), KernelLine q R V u ∧
    ∃ (N : ℕ) (b : ℕ → ℝ)
      (profiles : ℕ → Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (factor : ℝ),
      b N = 0 ∧ (∃ j < N, b j ≠ 0) ∧ factor ≠ 0 ∧
      (∀ i < N, ⟪u, corrDeriv q R (profiles i) u⟫ =
        factor * Nonvanishing.FreeProfile.sourceResponse N i b)

def CofinalSourceFamily : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧ SourceFamilyData (2^j) R (uthPath (2^j) R)

theorem cofinalAnyProfileCoupling_of_sourceFamily (h : CofinalSourceFamily) :
    CofinalAnyProfileCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, u, hline, N, b, profiles, factor, hb, hne, hf, hd⟩ := hRs R₀
  obtain ⟨i, -, hi⟩ := exists_profile_coupling_of_sourceFamily (uthPath _ _)
    u hline N b profiles factor hb hne hf hd
  exact ⟨R, hRR, hR, hR18, profiles i, hi⟩

#print axioms exists_profile_coupling_of_sourceColumns
#print axioms exists_profile_coupling_of_sourceFamily
#print axioms SourceFamilyData
#print axioms CofinalSourceFamily
#print axioms cofinalAnyProfileCoupling_of_sourceFamily
#print axioms deriv_symmetric
#print axioms corrDeriv_symmetric
#print axioms KernelLine
#print axioms canonicalCoupling_of_line
#print axioms canonicalCoupling_of_dominatedSource
#print axioms CofinalDominatedSource
#print axioms cofinalAnyProfileCoupling_of_dominatedSource
#print axioms signed_source_lower
#print axioms canonicalCoupling_of_kernelSource
end AdalyFormal.Round10.Assembly.R2
