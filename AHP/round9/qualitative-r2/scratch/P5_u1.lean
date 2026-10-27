
/-! ## The diagonal `U(1)`: the coupling is a single number on a charged complex line

Every link of the curved twist family is diagonal, so the constant gauge rotations
`diag(e^{iα}, e^{-iα})` leave the configuration unchanged.  By the frozen covariance lane the
vacuum carrier and the correction commute with the induced orthogonal maps `J_α`.  Hence, if the
canonical vacuum kernel is the complex line spanned by a charged vector `u₀` and `J u₀`
(`J = J_{π/4}`, `J (J u₀) = -u₀`), the first-order coefficient acts on it as the scalar
`⟪u₀, De u₀⟫ / ‖u₀‖²`, and the coupling premise is exactly `⟪u₀, De u₀⟫ ≠ 0`: round 8's
`c₁(q,R) ≠ 0`.  Round 9.1 assumed the commutation; here it is proved. -/
namespace AdalyFormal.Round9.Guarded.QualitativeR2

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
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.GaugeCov (adEL)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.D1Literal (PSD)

/-- The constant diagonal gauge rotation by `diag(e^{iα}, e^{-iα})`. -/
noncomputable def rotGauge {L : PeriodicLatticeExtent} (α : ℝ) : GaugeFn L :=
  fun _ => AdalyFormal.D1Literal.uθ α

theorem uθ_comm (α s : ℝ) :
    AdalyFormal.D1Literal.uθ α * AdalyFormal.D1Literal.uθ s =
      AdalyFormal.D1Literal.uθ s * AdalyFormal.D1Literal.uθ α := by
  apply Subtype.ext
  show AdalyFormal.D1Literal.uMat α * AdalyFormal.D1Literal.uMat s =
    AdalyFormal.D1Literal.uMat s * AdalyFormal.D1Literal.uMat α
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.D1Literal.uMat, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem uθ_conj (α s : ℝ) :
    AdalyFormal.D1Literal.uθ α * AdalyFormal.D1Literal.uθ s * (AdalyFormal.D1Literal.uθ α)⁻¹ =
      AdalyFormal.D1Literal.uθ s := by
  rw [uθ_comm, mul_assoc, mul_inv_cancel, mul_one]

theorem Ug_eq_uθ (s : ℝ) : Ug s = AdalyFormal.D1Literal.uθ s :=
  Subtype.ext (Ug_coe_uMat s)

theorem rot_maskedU (q R : ℕ) (α : ℝ) (g : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    periodicGaugeTransform (rotGauge α) (maskedU q R g V) =
      maskedU q R g (periodicGaugeTransform (rotGauge α) V) := by
  classical
  funext e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [periodicGaugeTransform, maskedU, if_pos he, rotGauge]
  · simp only [periodicGaugeTransform, maskedU, if_neg he, rotGauge, Ug_eq_uθ]
    exact uθ_conj α (g e)

theorem rot_uthPath (q R : ℕ) (α t : ℝ) :
    periodicGaugeTransform (rotGauge α) (uthPath q R t) = uthPath q R t := by
  classical
  funext e
  simp only [periodicGaugeTransform, uthPath, AdalyFormal.D1Literal.Uth, rotGauge]
  split_ifs
  · exact uθ_conj α t
  · rw [mul_one, mul_inv_cancel]

theorem rot_trivial (L : PeriodicLatticeExtent) (α : ℝ) :
    periodicGaugeTransform (rotGauge (L := L) α)
      (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) = fun _ => 1 := by
  funext e
  show AdalyFormal.D1Literal.uθ α * 1 * (AdalyFormal.D1Literal.uθ α)⁻¹ = 1
  rw [mul_one, mul_inv_cancel]

theorem rot_pathU (q R : ℕ) (α : ℝ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε t : ℝ) :
    periodicGaugeTransform (rotGauge α) (pathU q R (uthPath q R) f ε t) =
      pathU q R (uthPath q R) f ε t := by
  unfold pathU
  rw [rot_maskedU, rot_uthPath]

theorem rot_bulkU (q R : ℕ) (α : ℝ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    periodicGaugeTransform (rotGauge α) (bulkU q R f ε) = bulkU q R f ε := by
  unfold bulkU
  rw [rot_maskedU, rot_trivial]

/-- The vacuum carrier of the twist commutes with every diagonal rotation. -/
theorem vacA_rot (q R : ℕ) (α t : ℝ) (x : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    vacA q R (uthPath q R) 1 t (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) x) =
      adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) (vacA q R (uthPath q R) 1 t x) := by
  have h := Ginv_all_gauge (ell := 2) (k := 1) (Lu := dilLu q R) (by norm_num) (dilTower q R)
    (pathU q R (uthPath q R) (fun _ => 0) 0 t) 1 (dilLam q R) (rotGauge α) x
  rw [rot_pathU] at h
  exact h

/-- The correction has rotation-invariant quadratic form. -/
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

/-- The derivative of a matrix coefficient of a differentiable operator family. -/
theorem hasDerivAt_bilin {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {D : ℝ → E →L[ℝ] E} {De : E →L[ℝ] E} {x₀ : ℝ} (hD : HasDerivAt D De x₀) (v w : E) :
    HasDerivAt (fun ε => ⟪v, D ε w⟫) ⟪v, De w⟫ x₀ := by
  have hL : HasFDerivAt ((innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ E w))
      ((innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ E w)) (D x₀) :=
    ((innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ E w)).hasFDerivAt
  exact hL.comp_hasDerivAt x₀ hD

/-- The first-order coefficient of the correction is symmetric. -/
theorem De_symm {q R : ℕ} {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hD : HasDerivAt (fun ε : ℝ => bulkD q R f ε) De 0)
    (x y : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) : ⟪De x, y⟫ = ⟪x, De y⟫ := by
  have h1 := hasDerivAt_bilin hD y x
  have h2 := hasDerivAt_bilin hD x y
  have e : (fun ε : ℝ => ⟪y, bulkD q R f ε x⟫) = fun ε => ⟪x, bulkD q R f ε y⟫ := by
    funext ε
    exact (real_inner_comm (bulkD q R f ε x) y).trans
      (((dataS selIn selIn (bulkP q R f ε)).Delta2_spec (dataS_laws selIn selIn _)).1 x y)
  rw [e] at h1
  rw [real_inner_comm]
  exact h1.unique h2

/-- The first-order coefficient commutes with every diagonal rotation. -/
theorem De_rot_comm {q R : ℕ} {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hD : HasDerivAt (fun ε : ℝ => bulkD q R f ε) De 0) (α : ℝ)
    (y : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    De (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) y) =
      adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) (De y) := by
  set J := adEL (rotGauge α) (geomOf 2 1 (dilTower q R))
  have hq : ∀ u, ⟪J u, De (J u)⟫ = ⟪u, De u⟫ := by
    intro u
    have h1 := hasDerivAt_quadForm hD (J u)
    have h2 := hasDerivAt_quadForm hD u
    have e : (fun ε : ℝ => ⟪J u, bulkD q R f ε (J u)⟫) = fun ε => ⟪u, bulkD q R f ε u⟫ :=
      funext (fun ε => bulkD_rot q R α f ε u)
    rw [e] at h1
    exact h1.unique h2
  have hb : ∀ x, ⟪J x, De (J y)⟫ = ⟪x, De y⟫ := by
    intro x
    have h := hq (x + y)
    have hx := hq x
    have hy := hq y
    have hs1 : ⟪J y, De (J x)⟫ = ⟪J x, De (J y)⟫ := by
      rw [← De_symm hD, real_inner_comm]
    have hs2 : ⟪y, De x⟫ = ⟪x, De y⟫ := by
      rw [← De_symm hD, real_inner_comm]
    simp only [map_add, inner_add_left, inner_add_right] at h
    linarith
  refine ext_inner_left ℝ (fun v => ?_)
  obtain ⟨x, rfl⟩ := J.surjective v
  rw [hb x, LinearIsometryEquiv.inner_map_map]

/-- **Complex-line form of the coupling premise.**  The canonical forward vacuum kernel lies in
the plane spanned by a nonzero vector `u₀` and `J u₀`, where `J` is the quarter rotation and
`J (J u₀) = -u₀` (`u₀` is charged), and `⟪u₀, De u₀⟫ ≠ 0`.  NOT proved here. -/
def CanonicalU1Line (q R : ℕ)
    (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))) : Prop :=
  ∃ u₀ : ↥(bondSupp (geomOf 2 1 (dilTower q R))), u₀ ≠ 0 ∧
    vacA q R (uthPath q R) 1 (vacEdge q R (uthPath q R)) u₀ = 0 ∧
    adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
      (adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀) = -u₀ ∧
    (∀ u, vacA q R (uthPath q R) 1 (vacEdge q R (uthPath q R)) u = 0 →
      u ∈ Submodule.span ℝ {u₀, adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀}) ∧
    ⟪u₀, De u₀⟫ ≠ 0

/-- On a charged complex line the coupling is the single number `⟪u₀, De u₀⟫`; its
nonvanishing is the definite coupling of the reduced premise. -/
theorem canonicalCoupling_of_U1 {q R : ℕ} {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hD : HasDerivAt (fun ε : ℝ => bulkD q R f ε) De 0) (h : CanonicalU1Line q R De) :
    CanonicalCoupling q R (uthPath q R) De := by
  obtain ⟨u₀, hu₀, -, hJJ, hK, hc⟩ := h
  let J := adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
  let Jop : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
    J.toLinearIsometry.toContinuousLinearMap
  obtain ⟨l, hl⟩ := scalar_on_complex_line De Jop (De_symm hD)
    (fun x y => LinearIsometryEquiv.inner_map_map J x y)
    (fun x => De_rot_comm hD (Real.pi / 4) x) u₀ hu₀ hJJ
  have hmem : u₀ ∈ Submodule.span ℝ {u₀, Jop u₀} := Submodule.subset_span (by simp)
  have hn : 0 < ‖u₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu₀) 2
  have hl0 : l ≠ 0 := by
    intro h0
    apply hc
    rw [hl u₀ hmem, h0, zero_mul]
  rcases lt_or_gt_of_ne hl0 with hneg | hpos
  · refine ⟨-l, by linarith, Or.inr (fun u hu => ?_)⟩
    have h1 := hl u (hK u hu)
    linarith
  · refine ⟨l, hpos, Or.inl (fun u hu => ?_)⟩
    have h1 := hl u (hK u hu)
    linarith

/-- The literal reduced premise in complex-line form. -/
def TwistSoftU1 (q R : ℕ) : Prop :=
  ∃ De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))),
    InteriorSoft q R (dilMask q R) De ∧ CanonicalU1Line q R De

theorem twistSoftCouplingFwd_of_U1 {q R : ℕ} (h : TwistSoftU1 q R) : TwistSoftCouplingFwd q R := by
  obtain ⟨De, hs, hc⟩ := h
  exact ⟨De, hs, canonicalCoupling_of_U1 hs.2.2 hc⟩

def CofinalTwistSoftU1 : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧ TwistSoftU1 (2^j) R

theorem cofinalTwistSeparation_of_cofinalTwistSoftU1 (h : CofinalTwistSoftU1) :
    CofinalTwistSeparation := by
  refine cofinalTwistSeparation_of_cofinalTwistSoftCouplingFwd (fun j₀ => ?_)
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hv⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, twistSoftCouplingFwd_of_U1 hv⟩

theorem goalNeg2_of_cofinalTwistSoftU1 (h : CofinalTwistSoftU1) : GoalNeg2 :=
  goalNeg2_of_cofinalTwistSeparation (cofinalTwistSeparation_of_cofinalTwistSoftU1 h)

#print axioms rotGauge
#print axioms uθ_comm
#print axioms uθ_conj
#print axioms Ug_eq_uθ
#print axioms rot_maskedU
#print axioms rot_uthPath
#print axioms rot_trivial
#print axioms rot_pathU
#print axioms rot_bulkU
#print axioms vacA_rot
#print axioms bulkD_rot
#print axioms hasDerivAt_bilin
#print axioms De_symm
#print axioms De_rot_comm
#print axioms CanonicalU1Line
#print axioms canonicalCoupling_of_U1
#print axioms TwistSoftU1
#print axioms twistSoftCouplingFwd_of_U1
#print axioms CofinalTwistSoftU1
#print axioms cofinalTwistSeparation_of_cofinalTwistSoftU1
#print axioms goalNeg2_of_cofinalTwistSoftU1

end AdalyFormal.Round9.Guarded.QualitativeR2
