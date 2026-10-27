
/-! ## The weakest vacuum premise: first-order coupling on a vacuum crossing

At zero curvature the interior is flat whatever the profile is, so all path families
with the same exterior path share one vacuum carrier `vacA`.  Reflecting the profile
`f ↦ -f` reflects the curvature `ε ↦ -ε`, hence the sign of the first-order coupling;
so only the pre-crossing sign has to be treated (`first_order_separation`). -/
namespace AdalyFormal.Round9.Guarded.Qualitative

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round8.Guarded.SignFree
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.D1Literal (PSD)

/-- The vacuum carrier along an exterior path (flat interior, mass `a`). -/
noncomputable def vacA (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (a t : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  pathA q R V (fun _ => 0) 0 a t

theorem pathU_zero (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (t : ℝ) :
    pathU q R V f 0 t = pathU q R V (fun _ => 0) 0 t := by
  unfold pathU
  congr 1
  funext e
  simp

/-- At zero curvature every profile has the vacuum carrier. -/
theorem pathA_zero (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (a t : ℝ) :
    pathA q R V f 0 a t = vacA q R V a t := by
  unfold vacA pathA pathP
  rw [pathU_zero]

theorem pathU_neg (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε t : ℝ) :
    pathU q R V (fun e => -f e) ε t = pathU q R V f (-ε) t := by
  unfold pathU
  congr 1
  funext e
  simp

/-- Reflecting the profile reflects the curvature. -/
theorem pathA_neg (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    pathA q R V (fun e => -f e) ε a t = pathA q R V f (-ε) a t := by
  unfold pathA pathP
  rw [pathU_neg]

theorem pathD_neg (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    pathD q R V (fun e => -f e) ε a t = pathD q R V f (-ε) a t := by
  have hd : dataS selIn selIn (pathP q R V (fun e => -f e) ε a t) =
      dataS selIn selIn (pathP q R V f (-ε) a t) := by
    unfold pathP
    rw [pathU_neg]
  have heq : ∀ (d d' : BaseDataS
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  exact heq _ _ hd _ _

/-- **Vacuum coupling at `(q,R)`** for an exterior path `V` and an interior profile `f`
(mass `1`).  NOT proved here.
* Vacuum crossing (zero curvature, the same for every profile): the vacuum carrier is
  positive definite at angles arbitrarily close before `ts` and has a negative direction
  at angles arbitrarily close after `ts`.
* Regularity: the carrier is jointly continuous in curvature and angle at zero curvature,
  for angles near `ts`, and the correction is differentiable in the curvature at zero, with
  derivative `De`.
* Nondegeneracy: `De` is definite, of EITHER sign, on the kernel of the vacuum carrier at
  `ts`, with constant `c > 0`.
No derivative in the angle, no spectral gap and no scalar action on the kernel are
required. -/
def VacuumCoupling (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) : Prop :=
  ∃ (ts c : ℝ) (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))),
    (∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x, x ≠ 0 → 0 < ⟪x, vacA q R V 1 t₀ x⟫) ∧
    (∀ η : ℝ, 0 < η → ∃ t₁ : ℝ, ts < t₁ ∧ t₁ < ts + η ∧ ∃ w, ⟪w, vacA q R V 1 t₁ w⟫ < 0) ∧
    (∃ η₀ : ℝ, 0 < η₀ ∧ ∀ t : ℝ, |t - ts| < η₀ →
      ContinuousAt (fun p : ℝ × ℝ => pathA q R V f p.1 1 p.2) (0, t)) ∧
    HasDerivAt (fun ε : ℝ => pathD q R V f ε 1 0) De 0 ∧
    0 < c ∧ ((∀ u, vacA q R V 1 ts u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫) ∨
      (∀ u, vacA q R V 1 ts u = 0 → c * ‖u‖ ^ 2 ≤ -⟪u, De u⟫))

/-- The pre-crossing step on the actual operators, for any profile with the given data. -/
theorem eventually_pathSeparation_pos {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (ts c : ℝ) (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R))))
    (hbef : ∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x, x ≠ 0 → 0 < ⟪x, vacA q R V 1 t₀ x⟫)
    (haft : ∀ η : ℝ, 0 < η → ∃ t₁ : ℝ, ts < t₁ ∧ t₁ < ts + η ∧ ∃ w, ⟪w, vacA q R V 1 t₁ w⟫ < 0)
    (hj : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ t : ℝ, |t - ts| < η₀ → ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧
      ∀ ε s : ℝ, |ε| < r → |s - t| < r → ‖pathA q R V f ε 1 s - pathA q R V f 0 1 t‖ < δ)
    (hDx : ∀ μ : ℝ, 0 < μ → ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε < r →
      ‖pathD q R V f ε 1 0 - ε • De‖ ≤ μ * ε)
    (hc : 0 < c) (hpos : ∀ u, vacA q R V 1 ts u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → PathSeparation q R V f ε := by
  have hsA : ∀ ε t x y, ⟪pathA q R V f ε 1 t x, y⟫ = ⟪x, pathA q R V f ε 1 t y⟫ := by
    intro ε t x y
    exact (dataS selAll selAll (pathP q R V f ε 1 t)).Ginv_symm (dataS_laws selAll selAll _) x y
  have hsD : ∀ ε x y, ⟪pathD q R V f ε 1 0 x, y⟫ = ⟪x, pathD q R V f ε 1 0 y⟫ := by
    intro ε x y
    exact ((dataS selIn selIn (pathP q R V f ε 1 0)).Delta2_spec (dataS_laws selIn selIn _)).1 x y
  have hbef' : ∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x, x ≠ 0 → 0 < ⟪x, pathA q R V f 0 1 t₀ x⟫ := by
    intro η hη
    obtain ⟨t₀, h1, h2, h3⟩ := hbef η hη
    exact ⟨t₀, h1, h2, fun x hx => by rw [pathA_zero]; exact h3 x hx⟩
  have haft' : ∀ η : ℝ, 0 < η → ∃ t₁ : ℝ, ts < t₁ ∧ t₁ < ts + η ∧
      ∃ w, ⟪w, pathA q R V f 0 1 t₁ w⟫ < 0 := by
    intro η hη
    obtain ⟨t₁, h1, h2, w, hw⟩ := haft η hη
    exact ⟨t₁, h1, h2, w, by rw [pathA_zero]; exact hw⟩
  have hpos' : ∀ u, pathA q R V f 0 1 ts u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫ := by
    intro u hu
    rw [pathA_zero] at hu
    exact hpos u hu
  obtain ⟨ε₀, hε₀, hall⟩ := first_order_separation (fun ε t => pathA q R V f ε 1 t)
    (fun ε => pathD q R V f ε 1 0) hsA hsD (fun ε => pathA_continuous hq hR hroom hV f ε 1)
    ts hj hbef' haft' c De hc hpos' hDx
  refine ⟨ε₀, hε₀, fun ε hε hεε => ?_⟩
  obtain ⟨t, hu, hnu⟩ := hall ε hε hεε
  exact ⟨t, hu, by rwa [pathD_constant hq hR hroom V f ε 1 t]⟩

/-- Vacuum coupling gives a guarded separation at EVERY small curvature, for the profile
`f` itself or for its reflection `-f` (according to the sign of the coupling). -/
theorem eventually_pathSeparation_of_coupling {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V) {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    (h : VacuumCoupling q R V f) :
    ∃ f' : Bond (scaleUp 2 1 (dilLu q R)) → ℝ, (∀ e, |f' e| = |f e|) ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → PathSeparation q R V f' ε := by
  obtain ⟨ts, c, De, hbef, haft, ⟨η₀, hη₀, hjoint⟩, hD, hc, hsign⟩ := h
  have h3 : 3 ≤ R * (2*q) := by omega
  have hj : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ t : ℝ, |t - ts| < η₀ → ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧
      ∀ ε s : ℝ, |ε| < r → |s - t| < r → ‖pathA q R V f ε 1 s - pathA q R V f 0 1 t‖ < δ :=
    ⟨η₀, hη₀, fun t ht => metric_of_continuousAt (fun ε t => pathA q R V f ε 1 t) t (hjoint t ht)⟩
  have hDx := expansion_of_hasDerivAt (fun ε => pathD q R V f ε 1 0) De
    (pathD_zero hq hR h3 V f 1 0) hD
  rcases hsign with hpos | hneg
  · refine ⟨f, fun e => rfl, ?_⟩
    refine eventually_pathSeparation_pos hq hR hroom hV f ts c De hbef haft hj ?_ hc hpos
    intro μ hμ
    obtain ⟨r, hr, hb⟩ := hDx μ hμ
    refine ⟨r, hr, fun ε hε hεr => ?_⟩
    have h1 := hb ε (by rw [abs_of_pos hε]; exact hεr)
    rw [abs_of_pos hε] at h1
    exact h1
  · refine ⟨fun e => -f e, fun e => abs_neg (f e), ?_⟩
    have hj' : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ t : ℝ, |t - ts| < η₀ → ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧
        ∀ ε s : ℝ, |ε| < r → |s - t| < r →
        ‖pathA q R V (fun e => -f e) ε 1 s - pathA q R V (fun e => -f e) 0 1 t‖ < δ := by
      obtain ⟨η₁, hη₁, hj1⟩ := hj
      refine ⟨η₁, hη₁, fun t ht δ hδ => ?_⟩
      obtain ⟨r, hr, hb⟩ := hj1 t ht δ hδ
      refine ⟨r, hr, fun ε s hε hs => ?_⟩
      rw [pathA_neg, pathA_neg, neg_zero]
      exact hb (-ε) s (by rwa [abs_neg]) hs
    have hDx' : ∀ μ : ℝ, 0 < μ → ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε < r →
        ‖pathD q R V (fun e => -f e) ε 1 0 - ε • (-De)‖ ≤ μ * ε := by
      intro μ hμ
      obtain ⟨r, hr, hb⟩ := hDx μ hμ
      refine ⟨r, hr, fun ε hε hεr => ?_⟩
      have h1 := hb (-ε) (by rw [abs_neg, abs_of_pos hε]; exact hεr)
      rw [abs_neg, abs_of_pos hε] at h1
      have e2 : ε • (-De) = (-ε) • De := by
        rw [smul_neg]
        exact (neg_smul ε De).symm
      rw [pathD_neg, e2]
      exact h1
    refine eventually_pathSeparation_pos hq hR hroom hV (fun e => -f e) ts c (-De) hbef haft
      hj' hDx' hc ?_
    intro u hu
    have h1 := hneg u hu
    have e : ⟪u, (-De) u⟫ = -⟪u, De u⟫ := by
      show ⟪u, -(De u)⟫ = -⟪u, De u⟫
      exact inner_neg_right u (De u)
    rw [e]
    exact h1

/-- **The weakest cofinal premise of this route.**  Infinitely many dyadic scales, for
each infinitely many even radii `R ≥ 18`, each with SOME continuous exterior path and SOME
bounded interior profile having vacuum coupling.  NOT proved here. -/
def CofinalVacuumCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V ∧
    ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ, (∀ e, |f e| ≤ 1) ∧
      VacuumCoupling (2^j) R V f

theorem cofinalPathSeparation_of_cofinalVacuumCoupling (h : CofinalVacuumCoupling) :
    CofinalPathSeparation := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, V, hV, f, hf, hv⟩ := hRs R₀
  have hq : 0 < 2^j := by positivity
  have h1 : 1 ≤ 2^j := Nat.one_le_two_pow
  have hroom : 17*2 ≤ R*(2*2^j) := by nlinarith
  obtain ⟨f', hf', ε₀, hε₀, hall⟩ := eventually_pathSeparation_of_coupling hq hR hroom hV hv
  refine ⟨R, hRR, hR, hR18, V, hV, f', fun e => by rw [hf']; exact hf e, fun δ hδ => ?_⟩
  have hm : 0 < min δ ε₀ := lt_min hδ hε₀
  exact ⟨min δ ε₀ / 2, by positivity, by linarith [min_le_left δ ε₀],
    hall (min δ ε₀ / 2) (by positivity) (by linarith [min_le_right δ ε₀])⟩

/-- **Main reduction of this round.**  Cofinal vacuum coupling refutes the guarded
all-plaquette reading. -/
theorem goalNeg2_of_cofinalVacuumCoupling (h : CofinalVacuumCoupling) : GoalNeg2 :=
  goalNeg2_of_cofinalPathSeparation (cofinalPathSeparation_of_cofinalVacuumCoupling h)

/-- The positive reading forbids it. -/
theorem not_cofinalVacuumCoupling_of_goalPos1 (h : GoalPos1) : ¬ CofinalVacuumCoupling :=
  fun h' => goalNeg2_of_cofinalVacuumCoupling h' (goalPos2_iff_goalPos1.mpr h)

/-- What the positive reading demands, stated directly: from some scale on, for all large
even radii, NO continuous exterior path and NO bounded interior profile has vacuum
coupling. -/
theorem goalPos1_forces_no_vacuum_coupling (h : GoalPos1) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 2 ∣ R → 18 ≤ R →
      ∀ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V →
      ∀ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ, (∀ e, |f e| ≤ 1) →
        ¬ VacuumCoupling (2^j) R V f := by
  have h' := not_cofinalVacuumCoupling_of_goalPos1 h
  by_contra hcon
  apply h'
  intro j₀
  obtain ⟨j, hj⟩ := not_forall.mp (not_exists.mp hcon j₀)
  obtain ⟨hjj, hj2⟩ := Classical.not_imp.mp hj
  refine ⟨j, hjj, fun R₀ => ?_⟩
  obtain ⟨R, hR⟩ := not_forall.mp (not_exists.mp hj2 R₀)
  obtain ⟨hRR, hR1⟩ := Classical.not_imp.mp hR
  obtain ⟨hR2, hR3⟩ := Classical.not_imp.mp hR1
  obtain ⟨hR18, hR4⟩ := Classical.not_imp.mp hR3
  obtain ⟨V, hV⟩ := not_forall.mp hR4
  obtain ⟨hVc, hV1⟩ := Classical.not_imp.mp hV
  obtain ⟨f, hf⟩ := not_forall.mp hV1
  obtain ⟨hfb, hf1⟩ := Classical.not_imp.mp hf
  exact ⟨R, hRR, hR2, hR18, V, hVc, f, hfb, not_not.mp hf1⟩

/-- The same premise for the round-4/5 family itself: the frozen exterior twist and the single
defect line.  Its coupling is the round-8 vacuum coefficient `c1(q,R)` (numerically negative
at `q = 2, 4`); the reflection then separates with the reversed defect.  NOT proved here. -/
def CofinalDefectLineCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    VacuumCoupling (2^j) R (uthPath (2^j) R) (dilMask (2^j) R)

theorem cofinalVacuumCoupling_of_defectLine (h : CofinalDefectLineCoupling) :
    CofinalVacuumCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hv⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, uthPath (2^j) R, uthPath_cont (2^j) R, dilMask (2^j) R,
    dilMask_bound (2^j) R, hv⟩

theorem goalNeg2_of_cofinalDefectLineCoupling (h : CofinalDefectLineCoupling) : GoalNeg2 :=
  goalNeg2_of_cofinalVacuumCoupling (cofinalVacuumCoupling_of_defectLine h)

#print axioms vacA
#print axioms pathU_zero
#print axioms pathA_zero
#print axioms pathU_neg
#print axioms pathA_neg
#print axioms pathD_neg
#print axioms VacuumCoupling
#print axioms eventually_pathSeparation_pos
#print axioms eventually_pathSeparation_of_coupling
#print axioms CofinalVacuumCoupling
#print axioms cofinalPathSeparation_of_cofinalVacuumCoupling
#print axioms goalNeg2_of_cofinalVacuumCoupling
#print axioms not_cofinalVacuumCoupling_of_goalPos1
#print axioms goalPos1_forces_no_vacuum_coupling
#print axioms CofinalDefectLineCoupling
#print axioms cofinalVacuumCoupling_of_defectLine
#print axioms goalNeg2_of_cofinalDefectLineCoupling

end AdalyFormal.Round9.Guarded.Qualitative
