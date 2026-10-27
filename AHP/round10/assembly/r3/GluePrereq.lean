
namespace AdalyFormal.Round9.Guarded.Qualitative
open scoped RealInnerProductSpace Topology
open Filter Set
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
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)

noncomputable def pathU (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε t : ℝ) : LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  maskedU q R (fun e => ε * f e) (V t)

#print axioms pathU
noncomputable def pathP (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) : IngrBParams :=
  gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (pathU q R V f ε t) a (dilLam q R)

#print axioms pathP
noncomputable def pathA (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selAll selAll (pathP q R V f ε a t)).Ginv

#print axioms pathA
noncomputable def uthPath (q R : ℕ) : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun t => AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0) t

#print axioms uthPath
noncomputable def vacA (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (a t : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  pathA q R V (fun _ => 0) 0 a t

#print axioms vacA

end AdalyFormal.Round9.Guarded.Qualitative


namespace AdalyFormal.Round9.Guarded.QualitativeR2
open scoped RealInnerProductSpace Topology
open Filter Set
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
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)

noncomputable def bulkD (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selIn selIn (bulkP q R f ε)).Delta2 (dataS_laws selIn selIn _)

#print axioms bulkD
theorem bulkD_rot (q R : ℕ) (α : ℝ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ)
    (u : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    ⟪adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u,
      bulkD q R f ε (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u)⟫ = ⟪u, bulkD q R f ε u⟫ := by
  have h2 : (0 : ℕ) < 2 := by norm_num
  have h := AdalyFormal.M1GaugeW4.delta2_gauge (ell := 2) (k := 1) (Lu := dilLu q R) h2
    (dilTower q R) 1 (dilLam q R) (bulkU q R f ε) (rotGauge α) u
  have heq : ∀ (d d' : BaseDataS ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  have hd1 : (gparams 2 1 (dilLu q R) h2 (dilTower q R)
      (periodicGaugeTransform (rotGauge α) (bulkU q R f ε)) 1 (dilLam q R)).data =
      dataS selIn selIn (bulkP q R f ε) := by
    show dataS selIn selIn (gparams 2 1 (dilLu q R) h2 (dilTower q R)
      (periodicGaugeTransform (rotGauge α) (bulkU q R f ε)) 1 (dilLam q R)) = _
    unfold bulkP
    rw [rot_bulkU]
  have hd2 : (gparams 2 1 (dilLu q R) h2 (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)).data =
      dataS selIn selIn (bulkP q R f ε) := rfl
  have e1 : (gparams 2 1 (dilLu q R) h2 (dilTower q R)
      (periodicGaugeTransform (rotGauge α) (bulkU q R f ε)) 1 (dilLam q R)).data.Delta2
      (gparams 2 1 (dilLu q R) h2 (dilTower q R)
        (periodicGaugeTransform (rotGauge α) (bulkU q R f ε)) 1 (dilLam q R)).data_laws =
      bulkD q R f ε := heq _ _ hd1 _ _
  have e2 : (gparams 2 1 (dilLu q R) h2 (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)).data.Delta2
      (gparams 2 1 (dilLu q R) h2 (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)).data_laws =
      bulkD q R f ε := heq _ _ hd2 _ _
  rw [e1, e2] at h
  exact h

#print axioms bulkD_rot

end AdalyFormal.Round9.Guarded.QualitativeR2


namespace AdalyFormal.Round9.Guarded.QualitativeR2Joint
open scoped RealInnerProductSpace Topology
open Filter Set
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
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)

noncomputable def corrDeriv (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  deriv (fun ε : ℝ => QualitativeR2.bulkD q R f ε) 0

#print axioms corrDeriv

end AdalyFormal.Round9.Guarded.QualitativeR2Joint


namespace AdalyFormal.Round9.Guarded.Qualitative
open scoped RealInnerProductSpace Topology
open Filter Set
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
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem scalar_on_complex_line (M J : E →L[ℝ] E) (hM : ∀ x y, ⟪M x, y⟫ = ⟪x, M y⟫)
    (hJ : ∀ x y, ⟪J x, J y⟫ = ⟪x, y⟫) (hMJ : ∀ x, M (J x) = J (M x))
    (u₀ : E) (hu₀ : u₀ ≠ 0) (hJJ : J (J u₀) = -u₀) :
    ∃ l : ℝ, ∀ u ∈ Submodule.span ℝ {u₀, J u₀}, ⟪u, M u⟫ = l * ‖u‖ ^ 2 := by
  have h01' : ⟪u₀, J u₀⟫ = -⟪u₀, J u₀⟫ := by
    calc ⟪u₀, J u₀⟫ = ⟪J u₀, J (J u₀)⟫ := (hJ _ _).symm
      _ = ⟪J u₀, -u₀⟫ := by rw [hJJ]
      _ = -⟪J u₀, u₀⟫ := inner_neg_right _ _
      _ = -⟪u₀, J u₀⟫ := by rw [real_inner_comm u₀ (J u₀)]
  have h01 : ⟪u₀, J u₀⟫ = 0 := by linarith
  have h10 : ⟪J u₀, u₀⟫ = 0 := by rw [real_inner_comm]; exact h01
  have hJn : ⟪J u₀, J u₀⟫ = ⟪u₀, u₀⟫ := hJ u₀ u₀
  have e1 : ⟪J u₀, M u₀⟫ = ⟪u₀, M (J u₀)⟫ :=
    (hM (J u₀) u₀).symm.trans (real_inner_comm u₀ (M (J u₀)))
  have h1 : ⟪u₀, M (J u₀)⟫ = -⟪u₀, M (J u₀)⟫ := by
    calc ⟪u₀, M (J u₀)⟫ = ⟪J u₀, J (M (J u₀))⟫ := (hJ _ _).symm
      _ = ⟪J u₀, M (J (J u₀))⟫ := by rw [hMJ (J u₀)]
      _ = ⟪J u₀, M (-u₀)⟫ := by rw [hJJ]
      _ = -⟪J u₀, M u₀⟫ := by rw [map_neg, inner_neg_right]
      _ = -⟪u₀, M (J u₀)⟫ := by rw [e1]
  have hc1 : ⟪u₀, M (J u₀)⟫ = 0 := by linarith
  have hc2 : ⟪J u₀, M u₀⟫ = 0 := by rw [e1]; exact hc1
  have hd : ⟪J u₀, M (J u₀)⟫ = ⟪u₀, M u₀⟫ := by rw [hMJ u₀]; exact hJ _ _
  have hn : 0 < ‖u₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu₀) 2
  refine ⟨⟪u₀, M u₀⟫ / ‖u₀‖ ^ 2, fun u hu => ?_⟩
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hu
  have hform : ⟪a • u₀ + b • J u₀, M (a • u₀ + b • J u₀)⟫ =
      (a ^ 2 + b ^ 2) * ⟪u₀, M u₀⟫ := by
    simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hc1, hc2, hd]
    ring
  have hnorm : ‖a • u₀ + b • J u₀‖ ^ 2 = (a ^ 2 + b ^ 2) * ‖u₀‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hJn, h01, h10]
    ring
  rw [hform, hnorm, div_mul_eq_mul_div, eq_div_iff hn.ne']
  ring

#print axioms scalar_on_complex_line

end AdalyFormal.Round9.Guarded.Qualitative


namespace AdalyFormal.Round9.Guarded.QualitativeR2
open scoped RealInnerProductSpace Topology
open Filter Set
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
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)
open AdalyFormal.D1Literal (PSD)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def psdEdge (A : ℝ → E →L[ℝ] E) (t₀ t₁ : ℝ) : ℝ :=
  sSup {t | t ∈ Icc t₀ t₁ ∧ ∀ s ∈ Icc t₀ t, PSD (A s)}

#print axioms psdEdge

end AdalyFormal.Round9.Guarded.QualitativeR2


namespace AdalyFormal.Round9.Guarded.QualitativeR2
open scoped RealInnerProductSpace Topology
open Filter Set
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
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)

noncomputable def vacEdge (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) : ℝ :=
  psdEdge (vacA q R V 1) 0 Real.pi

#print axioms vacEdge
def CanonicalCoupling (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ((∀ u, vacA q R V 1 (vacEdge q R V) u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫) ∨
      (∀ u, vacA q R V 1 (vacEdge q R V) u = 0 → c * ‖u‖ ^ 2 ≤ -⟪u, De u⟫))

#print axioms CanonicalCoupling

end AdalyFormal.Round9.Guarded.QualitativeR2


namespace AdalyFormal.Round9.Guarded.QualitativeR2
open scoped RealInnerProductSpace Topology
open Filter Set
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
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)
variable {L : PeriodicLatticeExtent}
open AdalyFormal.D1Literal (SU2m)

def AnM (f : ℝ → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ (θ₀ : ℝ) (i j : Fin 2), AnalyticAt ℝ (fun θ => f θ i j) θ₀

#print axioms AnM
def AnFam (U : ℝ → PeriodicLinkConfiguration SU2m L) : Prop :=
  ∀ e : PeriodicLatticeEdge L, AnM fun θ => ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)

#print axioms AnFam

end AdalyFormal.Round9.Guarded.QualitativeR2


namespace AdalyFormal.Round9.Guarded.QualitativeR2Joint
open scoped RealInnerProductSpace Topology
open Filter Set
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
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)

def CofinalAnyProfileCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ,
      QualitativeR2.CanonicalCoupling (2^j) R (uthPath (2^j) R) (corrDeriv (2^j) R f)

#print axioms CofinalAnyProfileCoupling
def CofinalAnyPathCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V ∧
      QualitativeR2.AnFam V ∧ V 0 = (fun _ => 1) ∧
      (∃ w, ⟪w, vacA (2^j) R V 1 Real.pi w⟫ < 0) ∧
      ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ,
        QualitativeR2.CanonicalCoupling (2^j) R V (corrDeriv (2^j) R f)

#print axioms CofinalAnyPathCoupling

end AdalyFormal.Round9.Guarded.QualitativeR2Joint


namespace AdalyFormal.Round10.Dictionary
open scoped RealInnerProductSpace Topology
open Filter Set
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
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem comm_of_quad (T : E →L[ℝ] E) (J : E ≃ₗᵢ[ℝ] E)
    (hs : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫)
    (hq : ∀ x, ⟪J x, T (J x)⟫ = ⟪x, T x⟫) (y : E) :
    T (J y) = J (T y) := by
  have hb (x : E) : ⟪J x, T (J y)⟫ = ⟪x, T y⟫ := by
    have h := hq (x + y)
    have hx := hq x
    have hy := hq y
    have hs1 : ⟪J y, T (J x)⟫ = ⟪J x, T (J y)⟫ := by
      rw [← hs, real_inner_comm]
    have hs2 : ⟪y, T x⟫ = ⟪x, T y⟫ := by rw [← hs, real_inner_comm]
    simp only [map_add, inner_add_left, inner_add_right] at h
    linarith
  apply ext_inner_left ℝ
  intro v
  obtain ⟨x, rfl⟩ := J.surjective v
  rw [hb, J.inner_map_map]

#print axioms comm_of_quad
theorem deriv_comm (D : ℝ → E →L[ℝ] E) (J : E ≃ₗᵢ[ℝ] E)
    (h : ∀ t x, D t (J x) = J (D t x)) (t : ℝ) (x : E) :
    deriv D t (J x) = J (deriv D t x) := by
  by_cases hd : DifferentiableAt ℝ D t
  · have hd' : HasDerivAt D (deriv D t) t := hd.hasDerivAt
    let L : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E (J x)
    let M : (E →L[ℝ] E) →L[ℝ] E :=
      J.toLinearIsometry.toContinuousLinearMap.comp (ContinuousLinearMap.apply ℝ E x)
    have hl := L.hasFDerivAt.comp_hasDerivAt t hd'
    have hm := M.hasFDerivAt.comp_hasDerivAt t hd'
    have he : (fun s => L (D s)) = fun s => M (D s) := funext (fun s => h s x)
    change HasDerivAt (fun s => L (D s)) (L (deriv D t)) t at hl
    rw [he] at hl
    exact hl.unique hm
  · rw [deriv_zero_of_not_differentiableAt hd]
    simp

#print axioms deriv_comm

end AdalyFormal.Round10.Dictionary


namespace AdalyFormal.Round10.Dictionary.Actual
open scoped RealInnerProductSpace Topology
open Filter Set
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
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)

theorem bulkD_U1 (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (ε α : ℝ) (u : TwistSpace q R) :
    bulkD q R f ε (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u) =
    adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) (bulkD q R f ε u) :=
  comm_of_quad _ _ ((dataS selIn selIn (bulkP q R f ε)).Delta2_spec
    (dataS_laws selIn selIn _)).1 (bulkD_rot q R α f ε) u

#print axioms bulkD_U1
theorem corrDeriv_U1 (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (α : ℝ) (u : TwistSpace q R) :
    corrDeriv q R f (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u) =
    adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) (corrDeriv q R f u) :=
  deriv_comm (fun ε : ℝ => bulkD q R f ε) _ (fun ε => bulkD_U1 q R f ε α) 0 u

#print axioms corrDeriv_U1

end AdalyFormal.Round10.Dictionary.Actual


namespace AdalyFormal.Round10.Assembly.R2
open scoped RealInnerProductSpace Topology
open Filter Set
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
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)

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

#print axioms deriv_symmetric
theorem corrDeriv_symmetric (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (x y : TwistSpace q R) :
    ⟪corrDeriv q R f x, y⟫ = ⟪x, corrDeriv q R f y⟫ :=
  deriv_symmetric (fun ε => bulkD q R f ε)
    (fun ε => ((dataS selIn selIn (bulkP q R f ε)).Delta2_spec
      (dataS_laws selIn selIn _)).1) 0 x y

#print axioms corrDeriv_symmetric
def KernelLine (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (u₀ : TwistSpace q R) : Prop :=
  u₀ ≠ 0 ∧ vacA q R V 1 (vacEdge q R V) u₀ = 0 ∧
  adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
    (adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀) = -u₀ ∧
  (∀ u, vacA q R V 1 (vacEdge q R V) u = 0 →
    u ∈ Submodule.span ℝ {u₀,
      adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀})

#print axioms KernelLine
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

#print axioms canonicalCoupling_of_line

end AdalyFormal.Round10.Assembly.R2


namespace AdalyFormal.Round9.Guarded.AnalyticR2
open scoped RealInnerProductSpace Topology
open Filter Set
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
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)
open ContinuousLinearMap

theorem tendsto_clm_apply₂ {α : Type*} {l : Filter α} {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : α → E →L[ℝ] F} {x : α → E}
    {f₀ : E →L[ℝ] F} {x₀ : E} (hf : Tendsto f l (𝓝 f₀)) (hx : Tendsto x l (𝓝 x₀)) :
    Tendsto (fun a => f a (x a)) l (𝓝 (f₀ x₀)) :=
  ((continuous_fst.clm_apply continuous_snd).tendsto (f₀, x₀)).comp (hf.prodMk_nhds hx)

#print axioms tendsto_clm_apply₂
theorem tendsto_Delta2_div_form {E S F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (D : ℝ → BaseDataS E S F) (hL : ∀ ε, (D ε).Laws)
    (hH : ContinuousAt (fun ε => (D ε).H) 0)
    (hC2 : ∀ A, Tendsto (fun ε => (D ε).C2 A) (𝓝 0) (𝓝 ((D 0).C2 A)))
    (J' : E) (hJ : Tendsto (fun ε => ε⁻¹ • (D ε).J) (𝓝[≠] 0) (𝓝 J')) (A : E) :
    Tendsto (fun ε => ⟪A, (ε⁻¹ • (D ε).Delta2 (hL ε)) A⟫) (𝓝[≠] 0)
      (𝓝 (2 * ⟪(D 0).H ((D 0).C2 A), J'⟫)) := by
  have e : ∀ ε : ℝ, ⟪A, (ε⁻¹ • (D ε).Delta2 (hL ε)) A⟫
      = 2 * ⟪(D ε).H ((D ε).C2 A), ε⁻¹ • (D ε).J⟫ := by
    intro ε
    rw [smul_apply, real_inner_smul_right, ((D ε).Delta2_spec (hL ε)).2 A,
      real_inner_smul_right]
    ring
  simp only [e]
  have hHC : Tendsto (fun ε => (D ε).H ((D ε).C2 A)) (𝓝[≠] 0) (𝓝 ((D 0).H ((D 0).C2 A))) :=
    tendsto_clm_apply₂ (hH.tendsto.mono_left nhdsWithin_le_nhds)
      ((hC2 A).mono_left nhdsWithin_le_nhds)
  exact (Filter.Tendsto.inner (𝕜 := ℝ) hHC hJ).const_mul (2 : ℝ)

#print axioms tendsto_Delta2_div_form
theorem limit_Delta2_div_form {E S F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (D : ℝ → BaseDataS E S F) (hL : ∀ ε, (D ε).Laws)
    (hH : ContinuousAt (fun ε => (D ε).H) 0)
    (hC2 : ∀ A, Tendsto (fun ε => (D ε).C2 A) (𝓝 0) (𝓝 ((D 0).C2 A)))
    (J' : E) (hJ : Tendsto (fun ε => ε⁻¹ • (D ε).J) (𝓝[≠] 0) (𝓝 J'))
    (D₁ : E →L[ℝ] E) (hD₁ : Tendsto (fun ε => ε⁻¹ • (D ε).Delta2 (hL ε)) (𝓝[>] 0) (𝓝 D₁)) (A : E) :
    ⟪A, D₁ A⟫ = 2 * ⟪(D 0).H ((D 0).C2 A), J'⟫ := by
  have h1 : Tendsto (fun ε => ⟪A, (ε⁻¹ • (D ε).Delta2 (hL ε)) A⟫) (𝓝[>] 0) (𝓝 ⟪A, D₁ A⟫) :=
    (Filter.Tendsto.inner (𝕜 := ℝ) tendsto_const_nhds (tendsto_clm_apply₂ hD₁ tendsto_const_nhds))
  have h2 := (tendsto_Delta2_div_form D hL hH hC2 J' hJ A).mono_left
    (nhdsWithin_mono _ (fun x (hx : (0 : ℝ) < x) => ne_of_gt hx))
  exact tendsto_nhds_unique h1 h2

#print axioms limit_Delta2_div_form

end AdalyFormal.Round9.Guarded.AnalyticR2
