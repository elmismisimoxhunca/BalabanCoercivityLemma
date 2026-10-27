import DrEquiv
/-! A concrete cofinal family of valid right-exterior-star paths.
No kernel-line or response-detection conclusion is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
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

/-! Actual boundary dressing and gauge-fixing identities, for all carrier fields.
The results do not assert a crossing or response noncancellation. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
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

/-! The frozen mass contains each distinct level-zero leaf mass with its exact weight.
These are actual carrier estimates, not entries of a numerical Schur matrix. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
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
namespace AdalyFormal.Round13.Trial
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round12.Noncancel.Boundary
open AdalyFormal.Round12.Noncancel.Mass
open Classical

abbrev Fine (q R : ℕ) := scaleUp 2 1 (dilLu q R)

theorem seven_le_side {q : ℕ} (hq : 0 < q) (R : ℕ) (μ : Fin 3) :
    7 ≤ Fine q R μ + 1 := by
  rw [dil_fine_size hq]
  split_ifs <;> omega

/-- A seven-site coordinate box centered at the actual right boundary point. -/
def patchSite {q : ℕ} (hq : 0 < q) (R : ℕ) (v : Fin 3 → Fin 7) :
    PeriodicLatticeSite (Fine q R) :=
  fun μ => rightSite hq R μ + (Fin.castLE (seven_le_side hq R μ) (v μ) - 3)

theorem patchSite_injective {q : ℕ} (hq : 0 < q) (R : ℕ) :
    Function.Injective (patchSite hq R) := by
  intro v w h
  funext μ
  have he := congrFun h μ
  dsimp [patchSite] at he
  have he' := add_left_cancel he
  have he'' := sub_left_inj.mp he'
  exact Fin.ext (congrArg (fun a : Fin (Fine q R μ+1) => a.val) he'')

theorem castLE_add_one {n : ℕ} (hn : 7 ≤ n+1) (v : Fin 7) (hv : v.val < 6) :
    Fin.castLE hn (v + 1) = Fin.castLE hn v + (1 : Fin (n+1)) := by
  apply Fin.ext
  simp only [Fin.val_castLE, Fin.val_add, Fin.val_one']
  rw [Nat.mod_eq_of_lt (by omega : 1 < 7), Nat.mod_eq_of_lt (by omega : 1 < n+1),
    Nat.mod_eq_of_lt (by omega : v.val + 1 < 7),
    Nat.mod_eq_of_lt (by omega : v.val + 1 < n+1)]

theorem patchSite_shift {q : ℕ} (hq : 0 < q) (R : ℕ)
    (v : Fin 3 → Fin 7) (μ : Fin 3) (hv : (v μ).val < 6) :
    periodicLatticeShift (patchSite hq R v) μ =
      patchSite hq R (Function.update v μ (v μ + 1)) := by
  funext ν
  by_cases h : ν = μ
  · subst ν
    simp only [periodicLatticeShift, Function.update_self, patchSite]
    rw [castLE_add_one _ _ hv]
    abel
  · simp [periodicLatticeShift, patchSite, Function.update_of_ne h]

def centerCoord : Fin 3 → Fin 7 := ![3,3,3]

theorem patchSite_center {q : ℕ} (hq : 0 < q) (R : ℕ) :
    patchSite hq R centerCoord = rightSite hq R := by
  funext μ
  have hc : Fin.castLE (seven_le_side hq R μ) (centerCoord μ) = (3 : Fin (Fine q R μ+1)) := by
    apply Fin.ext
    have hμ : 3 < Fine q R μ+1 := lt_of_lt_of_le (by decide) (seven_le_side hq R μ)
    have hv : (centerCoord μ).val = 3 := by fin_cases μ <;> rfl
    change (centerCoord μ).val = 3 % (Fine q R μ+1)
    rw [hv, Nat.mod_eq_of_lt hμ]
  simp [patchSite, hc]

/-- Six distinct physical bonds; index 5 is the essential tangent correction. -/
def trialCoord : Fin 6 → (Fin 3 → Fin 7) :=
  ![![3,3,3], ![3,4,3], ![3,2,3], ![3,3,4], ![3,3,2], ![3,3,3]]
def trialDir : Fin 6 → Fin 3 := ![0,0,0,0,0,1]
def trialBond {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 6) : Bond (Fine q R) :=
  (patchSite hq R (trialCoord i), trialDir i)

theorem trialBond_injective {q : ℕ} (hq : 0 < q) (R : ℕ) :
    Function.Injective (trialBond hq R) := by
  intro i j h
  have hc := patchSite_injective hq R (congrArg Prod.fst h)
  have hd := congrArg Prod.snd h
  change trialDir i = trialDir j at hd
  fin_cases i <;> fin_cases j <;> simp_all [trialCoord, trialDir, funext_iff, Fin.forall_fin_succ]

/-- Charged Lie-algebra vector with its actual upper-right matrix entry z. -/
def charged (z : ℂ) : SuTwo :=
  ⟨!![0,z;-star z,0], by
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
    · simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]⟩

theorem charged_norm (z : ℂ) : ‖charged z‖^2 = Complex.normSq z := by
  rw [← real_inner_self_eq_norm_sq]
  change hsInner (charged z) (charged z) = _
  rw [hsInner_self_entries]
  simp [charged]

def trialAmplitude : Fin 6 → ℂ :=
  ![1, -Complex.I/4, Complex.I/4, -Complex.I/4, Complex.I/4, -Complex.I/4]

def trialField {q : ℕ} (hq : 0 < q) (R : ℕ) : BondFnL2 (Fine q R) :=
  ∑ i : Fin 6, sing (trialBond hq R i) (charged (trialAmplitude i))

theorem trialField_apply {q : ℕ} (hq : 0 < q) (R : ℕ) (e : Bond (Fine q R)) :
    trialField hq R e = ∑ i : Fin 6,
      if e = trialBond hq R i then charged (trialAmplitude i) else 0 := by
  simp [trialField, sing_apply]

theorem trialField_at {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 6) :
    trialField hq R (trialBond hq R i) = charged (trialAmplitude i) := by
  rw [trialField_apply]
  simp only [(trialBond_injective hq R).eq_iff]
  simp

theorem trialField_support {q : ℕ} (hq : 0 < q) (R : ℕ) (e : Bond (Fine q R))
    (he : trialField hq R e ≠ 0) : ∃ i : Fin 6, e = trialBond hq R i := by
  by_contra h
  push Not at h
  apply he
  rw [trialField_apply]
  simp [h]

theorem trialField_norm {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ‖trialField hq R‖^2 = (21/16 : ℝ) := by
  rw [PiLp.norm_sq_eq_of_L2]
  have hs : (∑ e : Bond (Fine q R), ‖trialField hq R e‖^2) =
      ∑ i : Fin 6, ‖trialField hq R (trialBond hq R i)‖^2 := by
    rw [← Finset.sum_image (f := fun e : Bond (Fine q R) => ‖trialField hq R e‖^2)
      (s := Finset.univ) (g := trialBond hq R)
      (fun i _ j _ h => trialBond_injective hq R h)]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    have hz : trialField hq R e = 0 := by
      by_contra hn
      obtain ⟨i,rfl⟩ := trialField_support hq R e hn
      exact he (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    simp [hz]
  rw [hs]
  simp only [trialField_at, charged_norm]
  norm_num [Fin.sum_univ_succ, trialAmplitude, Complex.normSq_apply]

end AdalyFormal.Round13.Trial
#print axioms AdalyFormal.Round13.Trial.patchSite_injective
#print axioms AdalyFormal.Round13.Trial.patchSite_shift
#print axioms AdalyFormal.Round13.Trial.patchSite_center
#print axioms AdalyFormal.Round13.Trial.trialBond_injective
#print axioms AdalyFormal.Round13.Trial.charged_norm
#print axioms AdalyFormal.Round13.Trial.trialField_at
#print axioms AdalyFormal.Round13.Trial.trialField_support
#print axioms AdalyFormal.Round13.Trial.trialField_norm

namespace AdalyFormal.Round13.Trial
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round12.Noncancel.Boundary
open AdalyFormal.Round12.Noncancel.Mass
open Classical

theorem trial_sites {q : ℕ} (hq : 0 < q) (R : ℕ) :
    (fun i : Fin 6 => (trialBond hq R i).1) =
      ![rightSite hq R, periodicLatticeShift (rightSite hq R) 1,
        periodicLatticeShiftBack (rightSite hq R) 1,
        periodicLatticeShift (rightSite hq R) 2,
        periodicLatticeShiftBack (rightSite hq R) 2, rightSite hq R] := by
  have hp1 := patchSite_shift hq R centerCoord 1 (by decide)
  have hp2 := patchSite_shift hq R centerCoord 2 (by decide)
  have hm1 := patchSite_shift hq R (trialCoord 2) 1 (by decide)
  have hm2 := patchSite_shift hq R (trialCoord 4) 2 (by decide)
  rw [patchSite_center] at hp1 hp2
  have hu1 : Function.update centerCoord 1 (centerCoord 1+1) = trialCoord 1 := by decide
  have hu2 : Function.update centerCoord 2 (centerCoord 2+1) = trialCoord 3 := by decide
  have hd1 : Function.update (trialCoord 2) 1 (trialCoord 2 1+1) = centerCoord := by decide
  have hd2 : Function.update (trialCoord 4) 2 (trialCoord 4 2+1) = centerCoord := by decide
  rw [hu1] at hp1
  rw [hu2] at hp2
  rw [hd1, patchSite_center] at hm1
  rw [hd2, patchSite_center] at hm2
  have hm1' := congrArg (fun z => periodicLatticeShiftBack z 1) hm1
  have hm2' := congrArg (fun z => periodicLatticeShiftBack z 2) hm2
  rw [periodicLatticeShiftBack_shift] at hm1' hm2'
  funext i
  fin_cases i
  · exact patchSite_center hq R
  · exact hp1.symm
  · exact hm1'
  · exact hp2.symm
  · exact hm2'
  · exact patchSite_center hq R

theorem trial_start_near {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 6) :
    pdist (rightSite hq R) (trialBond hq R i).1 ≤ 1 := by
  have h := congrFun (trial_sites hq R) i
  rw [h]
  fin_cases i
  · change pdist (rightSite hq R) (rightSite hq R) ≤ 1
    rw [AdalyFormal.StatementLaneR8.pdist_self]
    omega
  · exact pdist_shift_le _ _
  · exact pdist_shiftBack_le _ _
  · exact pdist_shift_le _ _
  · exact pdist_shiftBack_le _ _
  · change pdist (rightSite hq R) (rightSite hq R) ≤ 1
    rw [AdalyFormal.StatementLaneR8.pdist_self]
    omega

theorem trial_start_zero {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 6) :
    ((trialBond hq R i).1 0).val = 12*(R*q)+12*q-1 := by
  have hv : trialCoord i 0 = (3 : Fin 7) := by fin_cases i <;> rfl
  have hc : Fin.castLE (seven_le_side hq R 0) (3 : Fin 7) = (3 : Fin (Fine q R 0+1)) := by
    apply Fin.ext
    change 3 = 3 % (Fine q R 0+1)
    rw [Nat.mod_eq_of_lt (by have := seven_le_side hq R 0; omega)]
  simp [trialBond, patchSite, hv, hc, rightSite]

theorem trial_touch {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 6) :
    trialBond hq R i ∈ bondsOm0 (geomOf 2 1 (dilTower q R)) := by
  apply Or.inl
  change 4*q ≤ _ ∧ _ < 12*(R*q)+12*q
  rw [trial_start_zero]
  omega

theorem trial_collar {q R : ℕ} (hq : 0 < q) (hR18 : 18 ≤ R) (i : Fin 6) :
    (trialBond hq R i).1 ∉ (dilTower q R).Om 1 ∧
      periodicLatticeShift (trialBond hq R i).1 (trialBond hq R i).2 ∉
        (dilTower q R).Om 1 := by
  have hr : 18*q ≤ R*q := Nat.mul_le_mul_right q hR18
  constructor
  · change ¬ (2*(R*q)+4*q ≤ _ ∧ _ < 10*(R*q)+12*q)
    rw [trial_start_zero]
    omega
  · change ¬ (2*(R*q)+4*q ≤ _ ∧ _ < 10*(R*q)+12*q)
    rw [dil_shift_zero hq, trial_start_zero]
    split_ifs
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · omega

theorem trial_levelZero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) (i : Fin 6) :
    trialBond hq R i ∈ bondsLam (geomOf 2 1 (dilTower q R)) 0 :=
  collar_levelZero (dil_admissible hq hR) (by norm_num) _ (trial_touch hq R i)
    (trial_collar hq hR18 i).1 (trial_collar hq hR18 i).2

theorem trialField_mem {q : ℕ} (hq : 0 < q) (R : ℕ) :
    trialField hq R ∈ bondSupp (geomOf 2 1 (dilTower q R)) := by
  intro e he
  by_contra hn
  obtain ⟨i,rfl⟩ := trialField_support hq R e hn
  exact he (trial_touch hq R i)

def trialVector {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) := ⟨trialField hq R,trialField_mem hq R⟩

theorem trial_near_exterior {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 6) :
    pdist (periodicLatticeShift (rightSite hq R) 0) (trialBond hq R i).1 ≤ 2 ∧
    pdist (periodicLatticeShift (rightSite hq R) 0)
      (periodicLatticeShift (trialBond hq R i).1 (trialBond hq R i).2) ≤ 3 := by
  have h1 : pdist (periodicLatticeShift (rightSite hq R) 0) (rightSite hq R) ≤ 1 := by
    rw [AdalyFormal.StatementLaneR8.pdist_comm]
    exact pdist_shift_le _ _
  have h2 := trial_start_near hq R i
  have ht := pdist_triangle (periodicLatticeShift (rightSite hq R) 0)
    (rightSite hq R) (trialBond hq R i).1
  have h3 := pdist_shift_le (trialBond hq R i).1 (trialBond hq R i).2
  have ht' := pdist_triangle (periodicLatticeShift (rightSite hq R) 0)
    (trialBond hq R i).1 (periodicLatticeShift (trialBond hq R i).1 (trialBond hq R i).2)
  omega

theorem trialField_hsupp {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ∀ e : Bond (Fine q R), trialField hq R e ≠ 0 →
      ∃ w : PeriodicLatticeSite (Fine q R), w ∉ (dilTower q R).Om 0 ∧ pdist e.1 w ≤ 2 := by
  intro e he
  obtain ⟨i,rfl⟩ := trialField_support hq R e he
  exact ⟨periodicLatticeShift (rightSite hq R) 0, (rightSite_bd hq R).hx', by
    rw [AdalyFormal.StatementLaneR8.pdist_comm]; exact (trial_near_exterior hq R i).1⟩

/-- All positive-level physical blocking rows vanish, for arbitrary background U. -/
theorem trial_higher_rows_zero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (U : Cfg (Fine q R)) {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ 1)
    {b : Bond (Fine q R)} (hb : b ∈ bondsLam (geomOf 2 1 (dilTower q R)) j) :
    QlinB (geomOf 2 1 (dilTower q R)) U j (trialField hq R) b = 0 := by
  exact QlinB_supp_zero (dil_admissible hq hR) (by norm_num) (by nlinarith)
    U (trialField hq R) (trialField_hsupp hq R) hj hjk hb

theorem trial_mass_upper {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (U : Cfg (Fine q R)) :
    ⟪trialField hq R, MassFull (geomOf 2 1 (dilTower q R)) 1
      (bondSectorOf (geomOf 2 1 (dilTower q R)) U) (trialField hq R)⟫ ≤ (21/16 : ℝ) := by
  have h := Mass_supp_le (dil_admissible hq hR) (by norm_num) (by nlinarith)
    U 1 (by norm_num) (trialField hq R) (trialField_hsupp hq R)
  simpa only [trialField_norm, one_mul] using h

/-- Exact physical mass, not a lower estimate: the frozen higher rows contribute zero. -/
theorem trial_mass_eq {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (U : Cfg (Fine q R)) :
    ⟪trialField hq R, MassFull (geomOf 2 1 (dilTower q R)) 1
      (bondSectorOf (geomOf 2 1 (dilTower q R)) U) (trialField hq R)⟫ = (21/16 : ℝ) := by
  apply le_antisymm (trial_mass_upper hq hR hR18 U)
  have h := leaf_mass_le (geomOf 2 1 (dilTower q R)) U 1 (by norm_num)
    (Finset.univ.image (trialBond hq R)) (by
      intro e he
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      exact trial_levelZero hq hR hR18 i) (trialField hq R)
  rw [Finset.sum_image (fun i _ j _ h => trialBond_injective hq R h)] at h
  simp only [one_mul, trialField_at, charged_norm] at h
  norm_num [Fin.sum_univ_succ, trialAmplitude, Complex.normSq_apply] at h ⊢
  exact h

theorem trial_T_zero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (U : Cfg (Fine q R)) : Tfull (geomOf 2 1 (dilTower q R)) U (trialField hq R) = 0 := by
  unfold trialField
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact Tfull_sing_zero_near (dil_admissible hq hR) (d := 3) (by nlinarith)
    U _ _ _ (rightSite_bd hq R).hx'
    (by have := (trial_near_exterior hq R i).1; omega) (trial_near_exterior hq R i).2

theorem trial_W_eq {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (U : Cfg (Fine q R)) (a : ℝ) :
    Wop (geomOf 2 1 (dilTower q R)) U a (trialField hq R) = trialField hq R := by
  unfold trialField
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact Wop_sing_near (dil_admissible hq hR) (d := 3) (by nlinarith)
    U a _ _ _ (rightSite_bd hq R).hx'
    (by have := (trial_near_exterior hq R i).1; omega) (trial_near_exterior hq R i).2

end AdalyFormal.Round13.Trial
#print axioms AdalyFormal.Round13.Trial.trial_sites
#print axioms AdalyFormal.Round13.Trial.trialBond_injective
#print axioms AdalyFormal.Round13.Trial.trialField_norm
#print axioms AdalyFormal.Round13.Trial.trialField_mem
#print axioms AdalyFormal.Round13.Trial.trial_higher_rows_zero
#print axioms AdalyFormal.Round13.Trial.trial_mass_upper
#print axioms AdalyFormal.Round13.Trial.trial_mass_eq
#print axioms AdalyFormal.Round13.Trial.trial_T_zero
#print axioms AdalyFormal.Round13.Trial.trial_W_eq

namespace AdalyFormal.Round13.Trial
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round12.Noncancel.Path
open Classical

def stepCoord (v : Fin 3 → Fin 7) (μ : Fin 3) := Function.update v μ (v μ+1)
def backCoord (v : Fin 3 → Fin 7) (μ : Fin 3) := Function.update v μ (v μ-1)

theorem patchSite_back {q : ℕ} (hq : 0 < q) (R : ℕ)
    (v : Fin 3 → Fin 7) (μ : Fin 3) (hv : 0 < (v μ).val) :
    periodicLatticeShiftBack (patchSite hq R v) μ = patchSite hq R (backCoord v μ) := by
  have hb : ((backCoord v μ) μ).val < 6 := by
    simp only [backCoord, Function.update_self]
    have hvlt := (v μ).isLt
    rw [Fin.val_sub]
    norm_num
    omega
  have h := patchSite_shift hq R (backCoord v μ) μ hb
  have hu : Function.update (backCoord v μ) μ ((backCoord v μ) μ+1) = v := by
    simp [backCoord]
  rw [hu] at h
  have hh := congrArg (fun z => periodicLatticeShiftBack z μ) h
  rw [periodicLatticeShiftBack_shift] at hh
  exact hh.symm

def d02 : PeriodicPlaquetteDirections := ⟨(0,2),by decide⟩
def d12 : PeriodicPlaquetteDirections := ⟨(1,2),by decide⟩

def trialPlaqPattern : Fin 19 → ((Fin 3 → Fin 7) × PeriodicPlaquetteDirections) :=
  ![(![2,3,3],d01), (![3,1,3],d01), (![3,2,2],d01), (![3,2,2],d02),
    (![3,2,3],d01), (![3,2,3],d02), (![3,2,4],d01), (![3,3,1],d02),
    (![3,3,2],d01), (![3,3,2],d02), (![3,3,2],d12), (![3,3,3],d01),
    (![3,3,3],d02), (![3,3,3],d12), (![3,3,4],d01), (![3,3,4],d02),
    (![3,4,2],d02), (![3,4,3],d01), (![3,4,3],d02)]

def trialPlaq {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 19) : PeriodicLatticePlaquette (Fine q R) :=
  (patchSite hq R (trialPlaqPattern i).1, (trialPlaqPattern i).2)

theorem trialPlaqPattern_injective : Function.Injective trialPlaqPattern := by decide

theorem trialPlaq_injective {q : ℕ} (hq : 0 < q) (R : ℕ) : Function.Injective (trialPlaq hq R) := by
  intro i j h
  apply trialPlaqPattern_injective
  exact Prod.ext (patchSite_injective hq R (congrArg Prod.fst h))
    (congrArg (fun p : PeriodicLatticePlaquette (Fine q R) => p.2) h)

theorem pattern_front : ∀ (i : Fin 6) (d : PeriodicPlaquetteDirections),
    (d.1.1 = trialDir i ∨ d.1.2 = trialDir i) →
      ∃ k : Fin 19, trialPlaqPattern k = (trialCoord i,d) := by decide

theorem pattern_back1 : ∀ (i : Fin 6) (d : PeriodicPlaquetteDirections),
    d.1.1 = trialDir i →
      ∃ k : Fin 19, trialPlaqPattern k = (backCoord (trialCoord i) d.1.2,d) := by decide

theorem pattern_back2 : ∀ (i : Fin 6) (d : PeriodicPlaquetteDirections),
    d.1.2 = trialDir i →
      ∃ k : Fin 19, trialPlaqPattern k = (backCoord (trialCoord i) d.1.1,d) := by decide

theorem trialCoord_positive (i : Fin 6) (μ : Fin 3) : 0 < (trialCoord i μ).val := by
  fin_cases i <;> fin_cases μ <;> decide

theorem front_mem {q : ℕ} (hq : 0 < q) (R : ℕ)
    (i : Fin 6) (d : PeriodicPlaquetteDirections) (hd : d.1.1 = trialDir i ∨ d.1.2 = trialDir i) :
    (patchSite hq R (trialCoord i),d) ∈ Finset.univ.image (trialPlaq hq R) := by
  obtain ⟨k,hk⟩ := pattern_front i d hd
  exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _, by simp [trialPlaq, hk]⟩

theorem back_mem1 {q : ℕ} (hq : 0 < q) (R : ℕ)
    (i : Fin 6) (d : PeriodicPlaquetteDirections) (hd : d.1.1 = trialDir i) :
    (periodicLatticeShiftBack (patchSite hq R (trialCoord i)) d.1.2,d) ∈
      Finset.univ.image (trialPlaq hq R) := by
  obtain ⟨k,hk⟩ := pattern_back1 i d hd
  rw [patchSite_back hq R _ _ (trialCoord_positive i _)]
  exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _, by simp [trialPlaq, hk]⟩

theorem back_mem2 {q : ℕ} (hq : 0 < q) (R : ℕ)
    (i : Fin 6) (d : PeriodicPlaquetteDirections) (hd : d.1.2 = trialDir i) :
    (periodicLatticeShiftBack (patchSite hq R (trialCoord i)) d.1.1,d) ∈
      Finset.univ.image (trialPlaq hq R) := by
  obtain ⟨k,hk⟩ := pattern_back2 i d hd
  rw [patchSite_back hq R _ _ (trialCoord_positive i _)]
  exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _, by simp [trialPlaq, hk]⟩

/-- All plaquettes outside the explicit nineteen have exactly zero frozen contribution,
for every background, not only for the right star. -/
theorem trial_plaq_zero_off {q : ℕ} (hq : 0 < q) (R : ℕ) (U : Cfg (Fine q R))
    (p : PeriodicLatticePlaquette (Fine q R)) (hp : p ∉ Finset.univ.image (trialPlaq hq R)) :
    contrib U (WithLp.ofLp (trialField hq R)) p = 0 := by
  have hc : curlValueCovariant U (WithLp.ofLp (trialField hq R)) p = 0 ∧
      bilPlaq U p (WithLp.ofLp (trialField hq R)) (WithLp.ofLp (trialField hq R)) = 0 := by
    apply curl_bil_zero
    · by_contra hn
      obtain ⟨i,hi⟩ := trialField_support hq R _ hn
      have hx := congrArg Prod.fst hi
      have hd := congrArg Prod.snd hi
      dsimp only [trialBond] at hx hd
      have hx' : p.1 = periodicLatticeShiftBack (patchSite hq R (trialCoord i)) p.2.1.2 := by
        rw [← hx, periodicLatticeShiftBack_shift]
      exact hp (by simpa only [← hx', Prod.mk.eta] using back_mem1 hq R i p.2 hd)
    · by_contra hn
      obtain ⟨i,hi⟩ := trialField_support hq R _ hn
      have hx := congrArg Prod.fst hi
      have hd := congrArg Prod.snd hi
      dsimp only [trialBond] at hx hd
      exact hp (by simpa only [← hx, Prod.mk.eta] using front_mem hq R i p.2 (Or.inr hd))
    · by_contra hn
      obtain ⟨i,hi⟩ := trialField_support hq R _ hn
      have hx := congrArg Prod.fst hi
      have hd := congrArg Prod.snd hi
      dsimp only [trialBond] at hx hd
      exact hp (by simpa only [← hx, Prod.mk.eta] using front_mem hq R i p.2 (Or.inl hd))
    · by_contra hn
      obtain ⟨i,hi⟩ := trialField_support hq R _ hn
      have hx := congrArg Prod.fst hi
      have hd := congrArg Prod.snd hi
      dsimp only [trialBond] at hx hd
      have hx' : p.1 = periodicLatticeShiftBack (patchSite hq R (trialCoord i)) p.2.1.1 := by
        rw [← hx, periodicLatticeShiftBack_shift]
      exact hp (by simpa only [← hx', Prod.mk.eta] using back_mem2 hq R i p.2 hd)
  unfold contrib
  rw [hc.1, hc.2]
  change ⟪(0 : SuTwo), 0⟫ + (1/2 : ℝ)*0 = 0
  simp

/-- Exact enumeration of the FROZEN all-plaquette form. No integer-lattice surrogate. -/
theorem trial_delta_sum {q : ℕ} (hq : 0 < q) (R : ℕ) (U : Cfg (Fine q R)) :
    ⟪trialField hq R, AdalyFormal.StatementLaneR6.deltaKLocCLM U Set.univ (trialField hq R)⟫ =
      ∑ i : Fin 19, contrib U (WithLp.ofLp (trialField hq R)) (trialPlaq hq R i) := by
  rw [delta_form_sum]
  change (∑ p, contrib U (WithLp.ofLp (trialField hq R)) p) = _
  rw [← Finset.sum_image (f := contrib U (WithLp.ofLp (trialField hq R)))
    (s := Finset.univ) (g := trialPlaq hq R)
    (fun i _ j _ h => trialPlaq_injective hq R h)]
  symm
  exact Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => trial_plaq_zero_off hq R U p hp)

end AdalyFormal.Round13.Trial
#print axioms AdalyFormal.Round13.Trial.patchSite_back
#print axioms AdalyFormal.Round13.Trial.trialPlaq_injective
#print axioms AdalyFormal.Round13.Trial.pattern_front
#print axioms AdalyFormal.Round13.Trial.pattern_back1
#print axioms AdalyFormal.Round13.Trial.pattern_back2
#print axioms AdalyFormal.Round13.Trial.trial_plaq_zero_off
#print axioms AdalyFormal.Round13.Trial.trial_delta_sum

namespace AdalyFormal.Round13.Trial
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round12.Noncancel.Path
open AdalyFormal.Round12.Noncancel.Plaquette
open Classical

def quadForm (c s : ℝ) (x y z w : ℂ) : ℝ :=
  c * Complex.normSq (x+y+z+w) + 2*s*((star x*y).im+(star x*z).im+
    (star x*w).im+(star y*z).im+(star y*w).im+(star z*w).im)

/-- Four-atom extension of the copied frozen three-atom identity. -/
theorem frozen_four_form {L : PeriodicLatticeExtent} (U : Cfg L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (c s : ℝ) (x y z w : ℂ)
    (hr : reHolonomy U p = realHol c) (hi : imHolonomy U p = imagHol s)
    (h1 : a1LM U p A = chargedMat x) (h2 : a2LM p A = chargedMat y)
    (h3 : a3LM p A = chargedMat z) (h4 : a4LM U p A = chargedMat w) :
    contrib U A p = quadForm c s x y z w := by
  have hc : curlMatLM U p A = chargedMat (x+y+z+w) := by
    rw [curl_atoms, h1, h2, h3, h4, chargedMat_add, chargedMat_add, chargedMat_add]
  have hn : ⟪curlValueCovariant U A p, curlValueCovariant U A p⟫ =
      Complex.normSq (x+y+z+w) := charged_inner _ _ hc
  unfold contrib
  change ⟪curlValueCovariant U A p, curlValueCovariant U A p⟫ + _ = _
  rw [hn, bilPlaq_atoms]
  simp only [b1LM,b2LM,b3LM,b4LM,LinearMap.comp_apply,hr,hi,hc,h1,h2,h3,h4]
  rw [first_atom, comm_atom, comm_atom, comm_atom, comm_atom, comm_atom, comm_atom]
  unfold quadForm
  ring

def anchorCoord : Fin 3 → Fin 7 := ![4,3,3]

theorem star_anchor {q : ℕ} (hq : 0 < q) (R : ℕ) :
    periodicLatticeShift (rightSite hq R) 0 = patchSite hq R anchorCoord := by
  have h := patchSite_shift hq R centerCoord 0 (by decide)
  rw [patchSite_center] at h
  have he : Function.update centerCoord 0 (centerCoord 0+1) = anchorCoord := by decide
  simpa only [he] using h

def localStar (v : Fin 3 → Fin 7) (μ : Fin 3) : Prop :=
  μ ≠ 0 ∧ (v = anchorCoord ∨ stepCoord v μ = anchorCoord)

theorem rightStar_patch {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ)
    (v : Fin 3 → Fin 7) (μ : Fin 3) (hv : (v μ).val < 6) :
    rightStar hq R t (patchSite hq R v,μ) =
      if localStar v μ then uθ t else 1 := by
  unfold rightStar starPath starLinks
  simp only [Set.mem_setOf_eq, star_anchor, patchSite_shift hq R v μ hv,
    (patchSite_injective hq R).eq_iff, localStar, stepCoord]
  split_ifs <;> rfl

def localField (v : Fin 3 → Fin 7) (μ : Fin 3) : SuTwo :=
  ∑ i : Fin 6, if v = trialCoord i ∧ μ = trialDir i then charged (trialAmplitude i) else 0

theorem trialField_patch {q : ℕ} (hq : 0 < q) (R : ℕ)
    (v : Fin 3 → Fin 7) (μ : Fin 3) :
    trialField hq R (patchSite hq R v,μ) = localField v μ := by
  rw [trialField_apply]
  simp only [trialBond, Prod.mk.injEq, (patchSite_injective hq R).eq_iff, localField]

theorem charged_zero : charged 0 = 0 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [charged]

theorem charged_neg (z : ℂ) : -charged z = charged (-z) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [charged]

def isCurved (i : Fin 19) : Bool := decide (i = 4 ∨ i = 9 ∨ i = 11 ∨ i = 12)

theorem pattern_room (i : Fin 19) (μ : Fin 3) : ((trialPlaqPattern i).1 μ).val < 5 := by
  fin_cases i <;> fin_cases μ <;> decide

theorem pattern_base_flat (i : Fin 19) :
    ¬ localStar (trialPlaqPattern i).1 (trialPlaqPattern i).2.1.1 ∧
    ¬ localStar (trialPlaqPattern i).1 (trialPlaqPattern i).2.1.2 := by
  revert i
  unfold localStar
  decide

theorem pattern_shift_links (i : Fin 19) :
    (localStar (stepCoord (trialPlaqPattern i).1 (trialPlaqPattern i).2.1.1)
      (trialPlaqPattern i).2.1.2 ↔ isCurved i = true) ∧
    ¬ localStar (stepCoord (trialPlaqPattern i).1 (trialPlaqPattern i).2.1.2)
      (trialPlaqPattern i).2.1.1 := by
  revert i
  unfold localStar
  decide

theorem trial_base_links {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ) (i : Fin 19) :
    rightStar hq R t ((trialPlaq hq R i).1,(trialPlaq hq R i).2.1.1) = 1 ∧
    rightStar hq R t ((trialPlaq hq R i).1,(trialPlaq hq R i).2.1.2) = 1 := by
  have hm := pattern_room i (trialPlaqPattern i).2.1.1
  have hn := pattern_room i (trialPlaqPattern i).2.1.2
  change rightStar hq R t (patchSite hq R (trialPlaqPattern i).1, (trialPlaqPattern i).2.1.1) = 1 ∧
    rightStar hq R t (patchSite hq R (trialPlaqPattern i).1, (trialPlaqPattern i).2.1.2) = 1
  rw [rightStar_patch hq R t _ _ (by omega), rightStar_patch hq R t _ _ (by omega)]
  simp only [(pattern_base_flat i).1,(pattern_base_flat i).2,↓reduceIte,and_self]

theorem trial_holonomy {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ) (i : Fin 19) :
    holonomyElem (rightStar hq R t) (trialPlaq hq R i) =
      if isCurved i then uθ t else 1 := by
  have hb := trial_base_links hq R t i
  unfold holonomyElem periodicPlaquetteHolonomy
  dsimp only
  rw [hb.1,hb.2]
  change 1 * rightStar hq R t
      (periodicLatticeShift (patchSite hq R (trialPlaqPattern i).1) (trialPlaqPattern i).2.1.1,
        (trialPlaqPattern i).2.1.2) *
      (rightStar hq R t
      (periodicLatticeShift (patchSite hq R (trialPlaqPattern i).1) (trialPlaqPattern i).2.1.2,
        (trialPlaqPattern i).2.1.1))⁻¹ * 1⁻¹ = _
  rw [patchSite_shift hq R _ _ (by have := pattern_room i (trialPlaqPattern i).2.1.1; omega),
    patchSite_shift hq R _ _ (by have := pattern_room i (trialPlaqPattern i).2.1.2; omega)]
  have h1 : ((stepCoord (trialPlaqPattern i).1 (trialPlaqPattern i).2.1.1)
      (trialPlaqPattern i).2.1.2).val < 6 := by
    fin_cases i <;> decide
  have h2 : ((stepCoord (trialPlaqPattern i).1 (trialPlaqPattern i).2.1.2)
      (trialPlaqPattern i).2.1.1).val < 6 := by
    fin_cases i <;> decide
  have he1 := rightStar_patch hq R t _ _ h1
  have he2 := rightStar_patch hq R t _ _ h2
  have hp := pattern_shift_links i
  dsimp only [stepCoord] at he1 he2 hp
  rw [he1,he2]
  simp only [hp.1, hp.2, ↓reduceIte, inv_one, mul_one, one_mul]

theorem uhalf_coe : ((uθ (Real.pi/2) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) =
    !![Complex.I,0;0,-Complex.I] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uθ,uMat,Complex.ofReal_div,Complex.exp_pi_div_two_mul_I,Complex.exp_neg]

theorem trial_hol_parts {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 19) :
    reHolonomy (rightStar hq R (Real.pi/2)) (trialPlaq hq R i) = realHol (if isCurved i then 0 else 1) ∧
    imHolonomy (rightStar hq R (Real.pi/2)) (trialPlaq hq R i) = imagHol (if isCurved i then 1 else 0) := by
  have he := trial_holonomy hq R (Real.pi/2) i
  have hinv : ((holonomyElemInv (rightStar hq R (Real.pi/2)) (trialPlaq hq R i) : SU2m) :
      Matrix (Fin 2) (Fin 2) ℂ) = star ((holonomyElem (rightStar hq R (Real.pi/2))
        (trialPlaq hq R i) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := rfl
  unfold reHolonomy imHolonomy
  rw [hinv,he]
  cases hc : isCurved i <;> simp only [hc, Bool.false_eq_true, ↓reduceIte, uhalf_coe]
  all_goals constructor <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [realHol,imagHol,Matrix.star_apply,Matrix.ofNat_apply,Complex.ext_iff,Complex.div_re,Complex.div_im]

end AdalyFormal.Round13.Trial
#print axioms AdalyFormal.Round13.Trial.frozen_four_form
#print axioms AdalyFormal.Round13.Trial.rightStar_patch
#print axioms AdalyFormal.Round13.Trial.trial_base_links
#print axioms AdalyFormal.Round13.Trial.trial_holonomy
#print axioms AdalyFormal.Round13.Trial.trial_hol_parts

namespace AdalyFormal.Round13.Trial
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round12.Noncancel.Plaquette
open Classical

theorem charged_add (z w : ℂ) : charged (z+w) = charged z + charged w := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [charged,add_comm]

def chargedHom : ℂ →+ SuTwo where
  toFun := charged
  map_zero' := charged_zero
  map_add' := charged_add

def localAmplitude (v : Fin 3 → Fin 7) (μ : Fin 3) : ℂ :=
  ∑ i : Fin 6, if v = trialCoord i ∧ μ = trialDir i then trialAmplitude i else 0

theorem localField_amplitude (v : Fin 3 → Fin 7) (μ : Fin 3) :
    localField v μ = charged (localAmplitude v μ) := by
  unfold localField localAmplitude
  change _ = chargedHom _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [chargedHom,charged_zero]

theorem trial_edge_values {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 19) :
    let v := (trialPlaqPattern i).1
    let μ := (trialPlaqPattern i).2.1.1
    let ν := (trialPlaqPattern i).2.1.2
    trialField hq R ((trialPlaq hq R i).1, μ) = charged (localAmplitude v μ) ∧
    trialField hq R ((trialPlaq hq R i).1, ν) = charged (localAmplitude v ν) ∧
    trialField hq R (periodicLatticeShift (trialPlaq hq R i).1 ν,μ) =
      charged (localAmplitude (stepCoord v ν) μ) ∧
    trialField hq R (periodicLatticeShift (trialPlaq hq R i).1 μ,ν) =
      charged (localAmplitude (stepCoord v μ) ν) := by
  dsimp only [trialPlaq]
  rw [patchSite_shift hq R _ _ (by have := pattern_room i (trialPlaqPattern i).2.1.2; omega),
    patchSite_shift hq R _ _ (by have := pattern_room i (trialPlaqPattern i).2.1.1; omega)]
  simp only [trialField_patch,localField_amplitude,stepCoord,and_self]

theorem trial_atom_values {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ) (i : Fin 19) :
    let v := (trialPlaqPattern i).1
    let μ := (trialPlaqPattern i).2.1.1
    let ν := (trialPlaqPattern i).2.1.2
    a1LM (rightStar hq R t) (trialPlaq hq R i) (WithLp.ofLp (trialField hq R)) =
      chargedMat (-localAmplitude (stepCoord v ν) μ) ∧
    a2LM (trialPlaq hq R i) (WithLp.ofLp (trialField hq R)) = chargedMat (-localAmplitude v ν) ∧
    a3LM (trialPlaq hq R i) (WithLp.ofLp (trialField hq R)) = chargedMat (localAmplitude v μ) ∧
    a4LM (rightStar hq R t) (trialPlaq hq R i) (WithLp.ofLp (trialField hq R)) =
      chargedMat (localAmplitude (stepCoord v μ) ν) := by
  have hb := trial_base_links hq R t i
  have he := trial_edge_values hq R i
  dsimp only [trialPlaq] at hb he
  dsimp only at ⊢
  constructor
  · rw [a1LM_apply]
    unfold AprimeZW
    dsimp only [trialPlaq]
    rw [hb.2, he.2.2.1, AdalyFormal.Balaban.CovariantOperators.RMap_one, LinearMap.id_apply, charged_neg]
    rfl
  constructor
  · rw [a2LM_apply]
    unfold AprimeWX
    dsimp only [trialPlaq]
    rw [he.2.1,charged_neg]
    rfl
  constructor
  · rw [a3LM_apply]
    unfold AprimeXY
    dsimp only [trialPlaq]
    rw [he.1]
    rfl
  · rw [a4LM_apply]
    unfold AprimeYZ
    dsimp only [trialPlaq]
    rw [hb.1,he.2.2.2,AdalyFormal.Balaban.CovariantOperators.RMap_one]
    rfl

def localQuad (i : Fin 19) : ℝ :=
  let v := (trialPlaqPattern i).1
  let μ := (trialPlaqPattern i).2.1.1
  let ν := (trialPlaqPattern i).2.1.2
  quadForm (if isCurved i then 0 else 1) (if isCurved i then 1 else 0)
    (-localAmplitude (stepCoord v ν) μ) (-localAmplitude v ν)
    (localAmplitude v μ) (localAmplitude (stepCoord v μ) ν)

theorem trial_contrib_quad {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 19) :
    contrib (rightStar hq R (Real.pi/2)) (WithLp.ofLp (trialField hq R)) (trialPlaq hq R i) =
      localQuad i := by
  have h := trial_atom_values hq R (Real.pi/2) i
  have hh := trial_hol_parts hq R i
  exact frozen_four_form _ _ _ _ _ _ _ _ _ hh.1 hh.2 h.1 h.2.1 h.2.2.1 h.2.2.2

def plaqNumerator : Fin 19 → ℝ := ![1,1,1,1,-8,1,1,1,1,-8,1,-16,-8,1,1,1,1,1,1]

def edgePattern (i : Fin 19) : Fin 4 → ((Fin 3 → Fin 7) × Fin 3) :=
  let v := (trialPlaqPattern i).1
  let μ := (trialPlaqPattern i).2.1.1
  let ν := (trialPlaqPattern i).2.1.2
  ![(v,μ),(stepCoord v μ,ν),(stepCoord v ν,μ),(v,ν)]

/-- Exact incidence table, checked by kernel reduction over finite index types. -/
def edgeIndex : Fin 19 → Fin 4 → Option (Fin 6) :=
  ![![none,some 5,none,none], ![none,none,some 2,none],
    ![none,none,some 4,none], ![none,none,some 2,none],
    ![some 2,none,some 0,none], ![some 2,none,none,none],
    ![none,none,some 3,none], ![none,none,some 4,none],
    ![some 4,none,none,none], ![some 4,none,some 0,none],
    ![none,none,some 5,none], ![some 0,none,some 1,some 5],
    ![some 0,none,some 3,none], ![some 5,none,none,none],
    ![some 3,none,none,none], ![some 3,none,none,none],
    ![none,none,some 1,none], ![some 1,none,none,none], ![some 1,none,none,none]]

theorem edgeIndex_spec : ∀ (i : Fin 19) (k : Fin 4) (j : Fin 6),
    ((edgePattern i k).1 = trialCoord j ∧ (edgePattern i k).2 = trialDir j) ↔
      edgeIndex i k = some j := by decide

theorem localAmplitude_edge (i : Fin 19) (k : Fin 4) :
    localAmplitude (edgePattern i k).1 (edgePattern i k).2 =
      (edgeIndex i k).elim 0 trialAmplitude := by
  unfold localAmplitude
  simp only [edgeIndex_spec]
  cases h : edgeIndex i k <;> simp [h]

theorem localQuad_value (i : Fin 19) : localQuad i = plaqNumerator i / 16 := by
  change quadForm (if isCurved i then 0 else 1) (if isCurved i then 1 else 0)
    (-localAmplitude (edgePattern i 2).1 (edgePattern i 2).2)
    (-localAmplitude (edgePattern i 3).1 (edgePattern i 3).2)
    (localAmplitude (edgePattern i 0).1 (edgePattern i 0).2)
    (localAmplitude (edgePattern i 1).1 (edgePattern i 1).2) = _
  rw [localAmplitude_edge,localAmplitude_edge,localAmplitude_edge,localAmplitude_edge]
  fin_cases i
  · change quadForm 1 0 (-(0)) (-(0)) (0) (-Complex.I/4) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(Complex.I/4)) (-(0)) (0) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(Complex.I/4)) (-(0)) (0) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(Complex.I/4)) (-(0)) (0) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 0 1 (-(1)) (-(0)) (Complex.I/4) (0) = (-8 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(0)) (-(0)) (Complex.I/4) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(-Complex.I/4)) (-(0)) (0) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(Complex.I/4)) (-(0)) (0) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(0)) (-(0)) (Complex.I/4) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 0 1 (-(1)) (-(0)) (Complex.I/4) (0) = (-8 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(-Complex.I/4)) (-(0)) (0) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 0 1 (-(-Complex.I/4)) (-(-Complex.I/4)) (1) (0) = (-16 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 0 1 (-(-Complex.I/4)) (-(0)) (1) (0) = (-8 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(0)) (-(0)) (-Complex.I/4) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(0)) (-(0)) (-Complex.I/4) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(0)) (-(0)) (-Complex.I/4) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(-Complex.I/4)) (-(0)) (0) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(0)) (-(0)) (-Complex.I/4) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(0)) (-(0)) (-Complex.I/4) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]

/-- Exact actual frozen all-plaquette value for the periodic six-bond trial. -/
theorem trial_delta_value {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ⟪trialField hq R, AdalyFormal.StatementLaneR6.deltaKLocCLM
      (rightStar hq R (Real.pi/2)) Set.univ (trialField hq R)⟫ = (-25/16 : ℝ) := by
  rw [trial_delta_sum]
  simp only [trial_contrib_quad,localQuad_value]
  norm_num [plaqNumerator,Fin.sum_univ_succ]

/-- The four curved plaquettes have exact total -5/2. -/
theorem trial_curved_energy {q : ℕ} (hq : 0 < q) (R : ℕ) :
    (∑ i : Fin 19, if isCurved i then
      contrib (rightStar hq R (Real.pi/2)) (WithLp.ofLp (trialField hq R)) (trialPlaq hq R i)
      else 0) = (-5/2 : ℝ) := by
  simp only [trial_contrib_quad,localQuad_value]
  norm_num [Fin.sum_univ_succ,isCurved,plaqNumerator,Fin.ext_iff]

/-- The remaining fifteen plaquettes have exact total 15/16. -/
theorem trial_flat_energy {q : ℕ} (hq : 0 < q) (R : ℕ) :
    (∑ i : Fin 19, if isCurved i then 0 else
      contrib (rightStar hq R (Real.pi/2)) (WithLp.ofLp (trialField hq R)) (trialPlaq hq R i)) =
        (15/16 : ℝ) := by
  simp only [trial_contrib_quad,localQuad_value]
  norm_num [Fin.sum_univ_succ,isCurved,plaqNumerator,Fin.ext_iff]

/-- The exact energy is -1/4 on the ORIGINAL vacuum carrier, at every admissible q,R. -/
theorem trial_carrier_energy {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    ⟪trialVector hq R, vacA q R (rightStar hq R) 1 (Real.pi/2) (trialVector hq R)⟫ = (-1/4 : ℝ) := by
  rw [vacA_rightStar, BaseDataS.inner_Ginv]
  have hd : ⟪trialVector hq R,
      (dataS selAll selAll (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
        (rightStar hq R (Real.pi/2)) 1 (dilLam q R))).Dpi (trialVector hq R)⟫ = (-25/16 : ℝ) := by
    have e := E0_Dpi_inner selAll (geomOf 2 1 (dilTower q R))
      (rightStar hq R (Real.pi/2)) 1 (trialVector hq R)
    refine e.trans ?_
    change ⟪Wop (geomOf 2 1 (dilTower q R)) (rightStar hq R (Real.pi/2)) 1 (trialField hq R),
      DeltaS selAll (geomOf 2 1 (dilTower q R)) (rightStar hq R (Real.pi/2))
        (Wop (geomOf 2 1 (dilTower q R)) (rightStar hq R (Real.pi/2)) 1 (trialField hq R))⟫ = _
    rw [trial_W_eq hq hR hR18]
    exact trial_delta_value hq R
  have ht : (dataS selAll selAll (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (rightStar hq R (Real.pi/2)) 1 (dilLam q R))).T (trialVector hq R) = 0 :=
    trial_T_zero hq hR hR18 _
  have hm : ⟪trialVector hq R,
      (dataS selAll selAll (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
        (rightStar hq R (Real.pi/2)) 1 (dilLam q R))).Mass (trialVector hq R)⟫ = (21/16 : ℝ) := by
    change ⟪trialVector hq R, pE (geomOf 2 1 (dilTower q R))
      (MassFull (geomOf 2 1 (dilTower q R)) 1 (bondSectorOf (geomOf 2 1 (dilTower q R))
        (rightStar hq R (Real.pi/2))) (iE (geomOf 2 1 (dilTower q R)) (trialVector hq R)))⟫ = _
    rw [pE_inner_right]
    exact trial_mass_eq hq hR hR18 _
  rw [hd,ht,hm]
  norm_num

/-- P1, with its exact all-instance quantifiers; no physical estimate is a premise. -/
theorem rightStar_negative_halfpi :
    ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
      ∃ w : TwistSpace q R,
        ⟪w, vacA q R (rightStar hq R) 1 (Real.pi/2) w⟫ < 0 := by
  intro q R hq hR hR18
  exact ⟨trialVector hq R, by rw [trial_carrier_energy hq hR hR18]; norm_num⟩

theorem cofinal_rightStar_negative_halfpi :
    ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
      ∃ w : TwistSpace (2^j) R,
        ⟪w, vacA (2^j) R (rightStar (by positivity) R) 1 (Real.pi/2) w⟫ < 0 := by
  intro j₀
  refine ⟨j₀,le_rfl,?_⟩
  intro R₀
  refine ⟨2*(R₀+18),by omega,dvd_mul_right _ _,by omega,?_⟩
  exact rightStar_negative_halfpi (by positivity) (dvd_mul_right _ _) (by omega)

end AdalyFormal.Round13.Trial
#print axioms AdalyFormal.Round13.Trial.trial_edge_values
#print axioms AdalyFormal.Round13.Trial.trial_atom_values
#print axioms AdalyFormal.Round13.Trial.localQuad_value
#print axioms AdalyFormal.Round13.Trial.trial_contrib_quad
#print axioms AdalyFormal.Round13.Trial.trial_delta_value
#print axioms AdalyFormal.Round13.Trial.trial_carrier_energy
#print axioms AdalyFormal.Round13.Trial.rightStar_negative_halfpi
#print axioms AdalyFormal.Round13.Trial.cofinal_rightStar_negative_halfpi

#print axioms AdalyFormal.Round13.Trial.Fine
#print axioms AdalyFormal.Round13.Trial.seven_le_side
#print axioms AdalyFormal.Round13.Trial.patchSite
#print axioms AdalyFormal.Round13.Trial.patchSite_injective
#print axioms AdalyFormal.Round13.Trial.castLE_add_one
#print axioms AdalyFormal.Round13.Trial.patchSite_shift
#print axioms AdalyFormal.Round13.Trial.centerCoord
#print axioms AdalyFormal.Round13.Trial.patchSite_center
#print axioms AdalyFormal.Round13.Trial.trialCoord
#print axioms AdalyFormal.Round13.Trial.trialDir
#print axioms AdalyFormal.Round13.Trial.trialBond
#print axioms AdalyFormal.Round13.Trial.trialBond_injective
#print axioms AdalyFormal.Round13.Trial.charged
#print axioms AdalyFormal.Round13.Trial.charged_norm
#print axioms AdalyFormal.Round13.Trial.trialAmplitude
#print axioms AdalyFormal.Round13.Trial.trialField
#print axioms AdalyFormal.Round13.Trial.trialField_apply
#print axioms AdalyFormal.Round13.Trial.trialField_at
#print axioms AdalyFormal.Round13.Trial.trialField_support
#print axioms AdalyFormal.Round13.Trial.trialField_norm
#print axioms AdalyFormal.Round13.Trial.trial_sites
#print axioms AdalyFormal.Round13.Trial.trial_start_near
#print axioms AdalyFormal.Round13.Trial.trial_start_zero
#print axioms AdalyFormal.Round13.Trial.trial_touch
#print axioms AdalyFormal.Round13.Trial.trial_collar
#print axioms AdalyFormal.Round13.Trial.trial_levelZero
#print axioms AdalyFormal.Round13.Trial.trialField_mem
#print axioms AdalyFormal.Round13.Trial.trialVector
#print axioms AdalyFormal.Round13.Trial.trial_near_exterior
#print axioms AdalyFormal.Round13.Trial.trialField_hsupp
#print axioms AdalyFormal.Round13.Trial.trial_higher_rows_zero
#print axioms AdalyFormal.Round13.Trial.trial_mass_upper
#print axioms AdalyFormal.Round13.Trial.trial_mass_eq
#print axioms AdalyFormal.Round13.Trial.trial_T_zero
#print axioms AdalyFormal.Round13.Trial.trial_W_eq
#print axioms AdalyFormal.Round13.Trial.stepCoord
#print axioms AdalyFormal.Round13.Trial.backCoord
#print axioms AdalyFormal.Round13.Trial.patchSite_back
#print axioms AdalyFormal.Round13.Trial.d02
#print axioms AdalyFormal.Round13.Trial.d12
#print axioms AdalyFormal.Round13.Trial.trialPlaqPattern
#print axioms AdalyFormal.Round13.Trial.trialPlaq
#print axioms AdalyFormal.Round13.Trial.trialPlaqPattern_injective
#print axioms AdalyFormal.Round13.Trial.trialPlaq_injective
#print axioms AdalyFormal.Round13.Trial.pattern_front
#print axioms AdalyFormal.Round13.Trial.pattern_back1
#print axioms AdalyFormal.Round13.Trial.pattern_back2
#print axioms AdalyFormal.Round13.Trial.trialCoord_positive
#print axioms AdalyFormal.Round13.Trial.front_mem
#print axioms AdalyFormal.Round13.Trial.back_mem1
#print axioms AdalyFormal.Round13.Trial.back_mem2
#print axioms AdalyFormal.Round13.Trial.trial_plaq_zero_off
#print axioms AdalyFormal.Round13.Trial.trial_delta_sum
#print axioms AdalyFormal.Round13.Trial.quadForm
#print axioms AdalyFormal.Round13.Trial.frozen_four_form
#print axioms AdalyFormal.Round13.Trial.anchorCoord
#print axioms AdalyFormal.Round13.Trial.star_anchor
#print axioms AdalyFormal.Round13.Trial.localStar
#print axioms AdalyFormal.Round13.Trial.rightStar_patch
#print axioms AdalyFormal.Round13.Trial.localField
#print axioms AdalyFormal.Round13.Trial.trialField_patch
#print axioms AdalyFormal.Round13.Trial.charged_zero
#print axioms AdalyFormal.Round13.Trial.charged_neg
#print axioms AdalyFormal.Round13.Trial.isCurved
#print axioms AdalyFormal.Round13.Trial.pattern_room
#print axioms AdalyFormal.Round13.Trial.pattern_base_flat
#print axioms AdalyFormal.Round13.Trial.pattern_shift_links
#print axioms AdalyFormal.Round13.Trial.trial_base_links
#print axioms AdalyFormal.Round13.Trial.trial_holonomy
#print axioms AdalyFormal.Round13.Trial.uhalf_coe
#print axioms AdalyFormal.Round13.Trial.trial_hol_parts
#print axioms AdalyFormal.Round13.Trial.charged_add
#print axioms AdalyFormal.Round13.Trial.chargedHom
#print axioms AdalyFormal.Round13.Trial.localAmplitude
#print axioms AdalyFormal.Round13.Trial.localField_amplitude
#print axioms AdalyFormal.Round13.Trial.trial_edge_values
#print axioms AdalyFormal.Round13.Trial.trial_atom_values
#print axioms AdalyFormal.Round13.Trial.localQuad
#print axioms AdalyFormal.Round13.Trial.trial_contrib_quad
#print axioms AdalyFormal.Round13.Trial.plaqNumerator
#print axioms AdalyFormal.Round13.Trial.edgePattern
#print axioms AdalyFormal.Round13.Trial.edgeIndex
#print axioms AdalyFormal.Round13.Trial.edgeIndex_spec
#print axioms AdalyFormal.Round13.Trial.localAmplitude_edge
#print axioms AdalyFormal.Round13.Trial.localQuad_value
#print axioms AdalyFormal.Round13.Trial.trial_delta_value
#print axioms AdalyFormal.Round13.Trial.trial_curved_energy
#print axioms AdalyFormal.Round13.Trial.trial_flat_energy
#print axioms AdalyFormal.Round13.Trial.trial_carrier_energy
#print axioms AdalyFormal.Round13.Trial.rightStar_negative_halfpi
#print axioms AdalyFormal.Round13.Trial.cofinal_rightStar_negative_halfpi

/-! Round 13 trial R2. The R1 physical certificate above is retained verbatim.
This appendix exposes its nonzero witness, exact Rayleigh quotient and complete
nested cofinal path handoff. It makes no crossing or detection assertion. -/
namespace AdalyFormal.Round13.Trial.R2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu)
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round9.Guarded.Qualitative (vacA)
open AdalyFormal.Round9.Guarded.QualitativeR2 (AnFam)
open AdalyFormal.Round12.Noncancel.RightFamily

/-- The carrier subspace uses the actual ambient physical norm. -/
theorem trialVector_norm_sq {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ‖trialVector hq R‖^2 = (21/16 : ℝ) := by
  exact trialField_norm hq R

theorem trialVector_ne_zero {q : ℕ} (hq : 0 < q) (R : ℕ) :
    trialVector hq R ≠ 0 := by
  intro h
  have hn := trialVector_norm_sq hq R
  rw [h] at hn
  norm_num at hn

/-- A quantitative negative Rayleigh value, not a statement about the crossing vector. -/
theorem trial_rayleigh {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    ⟪trialVector hq R,
      vacA q R (rightStar hq R) 1 (Real.pi/2) (trialVector hq R)⟫ /
        ‖trialVector hq R‖^2 = (-4/21 : ℝ) := by
  rw [trial_carrier_energy hq hR hR18, trialVector_norm_sq hq R]
  norm_num

/-- P1 exactly as requested, obtained from the already verified R1 theorem. -/
theorem rightStar_negative_halfpi :
    ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
      ∃ w : TwistSpace q R,
        ⟪w, vacA q R (rightStar hq R) 1 (Real.pi/2) w⟫ < 0 :=
  AdalyFormal.Round13.Trial.rightStar_negative_halfpi

/-- All path clauses and the exact physical trial hold at ANY selected admissible
scale and radius; no intersection of unrelated cofinal subsequences is used. -/
theorem rightStar_physical_halfpi {q R : ℕ}
    (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    AdalyFormal.D1Literal.ContFam (rightStar hq R) ∧
    AnFam (rightStar hq R) ∧ rightStar hq R 0 = (fun _ => 1) ∧
    (∃ w : TwistSpace q R, ⟪w, vacA q R (rightStar hq R) 1 Real.pi w⟫ < 0) ∧
    trialVector hq R ≠ 0 ∧ ‖trialVector hq R‖^2 = (21/16 : ℝ) ∧
    ⟪trialVector hq R,
      vacA q R (rightStar hq R) 1 (Real.pi/2) (trialVector hq R)⟫ = (-1/4 : ℝ) :=
  ⟨rightStar_cont hq R, rightStar_an hq R, rightStar_zero hq R,
    rightStar_negative hq hR hR18, trialVector_ne_zero hq R,
    trialVector_norm_sq hq R, trial_carrier_energy hq hR hR18⟩

/-- Original nested scale/radius order, now with path validity and an explicit
half-pi witness at the SAME indices. No KernelLine or CurlDetected is asserted. -/
theorem cofinal_rightStar_paths_halfpi :
    ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
      ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)),
        V = rightStar (by positivity) R ∧
        AdalyFormal.D1Literal.ContFam V ∧ AnFam V ∧ V 0 = (fun _ => 1) ∧
        (∃ z : TwistSpace (2^j) R, ⟪z, vacA (2^j) R V 1 Real.pi z⟫ < 0) ∧
        ∃ w : TwistSpace (2^j) R,
          w = trialVector (by positivity) R ∧ w ≠ 0 ∧ ‖w‖^2 = (21/16 : ℝ) ∧
          ⟪w, vacA (2^j) R V 1 (Real.pi/2) w⟫ = (-1/4 : ℝ) ∧
          ⟪w, vacA (2^j) R V 1 (Real.pi/2) w⟫ < 0 := by
  intro j₀
  refine ⟨j₀, le_rfl, ?_⟩
  intro R₀
  let R := 2*(R₀+18)
  have hR : 2 ∣ R := dvd_mul_right _ _
  have hR18 : 18 ≤ R := by dsimp [R]; omega
  have hq : 0 < 2^j₀ := by positivity
  obtain ⟨hc, ha, hz, hp, hn, hnorm, he⟩ := rightStar_physical_halfpi hq hR hR18
  refine ⟨R, by dsimp [R]; omega, hR, hR18, rightStar hq R, rfl,
    hc, ha, hz, hp, trialVector hq R, rfl, hn, hnorm, he, ?_⟩
  rw [he]
  norm_num

#print axioms trialVector_norm_sq
#print axioms trialVector_ne_zero
#print axioms trial_rayleigh
#print axioms rightStar_negative_halfpi
#print axioms rightStar_physical_halfpi
#print axioms cofinal_rightStar_paths_halfpi
end AdalyFormal.Round13.Trial.R2
