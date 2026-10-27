
/-! Round 10 assembly: interfaces to the actual round-9 coupling.
Every result below that concludes GoalNeg2 has an explicit missing premise. -/

namespace AdalyFormal.Round10.Assembly

open scoped RealInnerProductSpace
open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.GaugeCov (adEL)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-- The geometric part of the charged-line criterion, with the coupling removed.
This concerns the full carrier kernel. No sector simplicity is assumed implicitly. -/
def CanonicalKernelLine (q R : ℕ) (u₀ : AnalyticR1.TwistSpace q R) : Prop :=
  u₀ ≠ 0 ∧
  vacA q R (uthPath q R) 1 (QualitativeR2.vacEdge q R (uthPath q R)) u₀ = 0 ∧
  adEL (QualitativeR2.rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
    (adEL (QualitativeR2.rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀) = -u₀ ∧
  (∀ u, vacA q R (uthPath q R) 1 (QualitativeR2.vacEdge q R (uthPath q R)) u = 0 →
    u ∈ Submodule.span ℝ {u₀,
      adEL (QualitativeR2.rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀})

/-- The source-track sufficient conditions, tied by an explicit identity to the
actual derivative. No numerical formula is substituted for that identity. -/
def DominatedSource (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (u : AnalyticR1.TwistSpace q R) : Prop :=
  Nonvanishing.BlockSourceData ⟪u, corrDeriv q R f u⟫

/-- Combining the finite source estimate with the round-9 symmetry theorem.
The kernel identification and actual operator/source dictionary remain hypotheses. -/
theorem canonicalCoupling_of_dominatedSource {q R : ℕ}
    (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (u : AnalyticR1.TwistSpace q R)
    (hline : CanonicalKernelLine q R u) (hsource : DominatedSource q R f u) :
    QualitativeR2.CanonicalCoupling q R (uthPath q R) (corrDeriv q R f) := by
  obtain ⟨hu, hk, hJJ, hK⟩ := hline
  apply QualitativeR2.canonicalCoupling_of_U1 (hasDerivAt_corrDeriv hq hR hR16 f)
  exact ⟨u, hu, hk, hJJ, hK,
    Nonvanishing.coupling_ne_zero_of_blockSourceData _ hsource⟩

/-- A precise hand-off premise, not a proved fact. It permits arbitrary profiles. -/
def CofinalDominatedSource : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ (f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ) (u : AnalyticR1.TwistSpace (2^j) R),
      CanonicalKernelLine (2^j) R u ∧ DominatedSource (2^j) R f u

theorem cofinalAnyProfileCoupling_of_dominatedSource (h : CofinalDominatedSource) :
    CofinalAnyProfileCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, f, u, hline, hsource⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, f,
    canonicalCoupling_of_dominatedSource (by positivity) hR (by omega) f u hline hsource⟩

theorem goalNeg2_of_cofinalDominatedSource (h : CofinalDominatedSource) : GoalNeg2 :=
  goalNeg2_of_cofinalAnyProfileCoupling (cofinalAnyProfileCoupling_of_dominatedSource h)

/-- Normalized limits on an arbitrary exponent/radius subsequence suffice.
The limit and kernel-line hypotheses are pointwise in the exponent index; no
uniformity across scales, no sign choice and no lower bound on s are required. -/
theorem cofinalAnyProfileCoupling_of_normalized_limits
    (j : ℕ → ℕ) (r : ℕ → ℕ → ℕ)
    (f : ∀ n m, Bond (scaleUp 2 1 (dilLu (2^(j n)) (r n m))) → ℝ)
    (u : ∀ n m, AnalyticR1.TwistSpace (2^(j n)) (r n m))
    (s : ℕ → ℕ → ℝ) (K : ℕ → ℝ)
    (hj : ∀ n, n ≤ j n) (hr : ∀ n m, m ≤ r n m)
    (hR : ∀ n m, 2 ∣ r n m) (hR18 : ∀ n m, 18 ≤ r n m)
    (hline : ∀ n, ∀ᶠ m in atTop, CanonicalKernelLine (2^(j n)) (r n m) (u n m))
    (hK : ∀ n, K n ≠ 0)
    (hlim : ∀ n, Tendsto
      (fun m => ⟪u n m, corrDeriv (2^(j n)) (r n m) (f n m) (u n m)⟫ / s n m)
      atTop (𝓝 (K n))) : CofinalAnyProfileCoupling := by
  intro j₀
  refine ⟨j j₀, hj j₀, ?_⟩
  have hnz := eventually_ne_zero_of_normalized_limit (hK j₀) (hlim j₀)
  have hevent : ∀ᶠ m in atTop,
      2 ∣ r j₀ m ∧ 18 ≤ r j₀ m ∧
      ∃ f' : Bond (scaleUp 2 1 (dilLu (2^(j j₀)) (r j₀ m))) → ℝ,
        QualitativeR2.CanonicalCoupling (2^(j j₀)) (r j₀ m) (uthPath _ _)
          (corrDeriv _ _ f') := by
    filter_upwards [hline j₀, hnz] with m hl hn
    obtain ⟨hu, hk, hJJ, hker⟩ := hl
    exact ⟨hR j₀ m, hR18 j₀ m, f j₀ m,
      QualitativeR2.canonicalCoupling_of_U1
        (hasDerivAt_corrDeriv (by positivity) (hR j₀ m) (by have := hR18 j₀ m; omega) (f j₀ m))
        ⟨u j₀ m, hu, hk, hJJ, hker, hn⟩⟩
  exact cofinal_of_eventual_subsequence (hr j₀) hevent

#print axioms CanonicalKernelLine
#print axioms DominatedSource
#print axioms canonicalCoupling_of_dominatedSource
#print axioms CofinalDominatedSource
#print axioms cofinalAnyProfileCoupling_of_dominatedSource
#print axioms goalNeg2_of_cofinalDominatedSource
#print axioms cofinalAnyProfileCoupling_of_normalized_limits

end AdalyFormal.Round10.Assembly
