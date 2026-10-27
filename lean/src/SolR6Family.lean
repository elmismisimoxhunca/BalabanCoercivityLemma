import GdR6b
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
namespace SolR6Family
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2 AdalyFormal.D1Literal AdalyFormal.D1Guarded
open AdalyFormal.StatementLaneR8 AdalyFormal.StatementLaneR6
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
variable {L : PeriodicLatticeExtent}
open Classical in
noncomputable def sparse (e0 : Bond L) (θ : ℝ) : Cfg L := fun e => if e = e0 then uθ θ else 1

theorem sparse_zero (e0 : Bond L) : sparse e0 0 = fun _ => 1 := by
  funext e; simp [sparse, uθ_zero]

theorem sparse_cont (e0 : Bond L) : ContFam (sparse e0) := by
  intro e
  by_cases he : e = e0
  · simp only [sparse, he, if_true]
    show Continuous fun θ => uMat θ
    unfold uMat
    refine continuous_matrix (fun i j => ?_)
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · simp only [sparse, he, if_false]
    exact continuous_const

theorem sparse_base {Om : Set (PeriodicLatticeSite L)} (e0 : Bond L) (hz : e0 ∈ Zb Om) (θ : ℝ) :
    ∀ e : Bond L, e.1 ∈ Om → sparse e0 θ e = 1 := by
  intro e he
  have hn : e ≠ e0 := by rintro rfl; exact hz.1 he
  simp [sparse, hn]

theorem sparse_not_twist {Om : Set (PeriodicLatticeSite L)} (e0 e1 : Bond L)
    (hz0 : e0 ∈ Zb Om) (hz1 : e1 ∈ Zb Om) (hne : e1 ≠ e0) (θ : ℝ) (hu : uθ θ ≠ 1) :
    ∀ φ : ℝ, sparse e0 θ ≠ Uth Om φ := by
  intro φ heq
  have h1 := congrFun heq e1
  have h0 := congrFun heq e0
  simp only [sparse, if_neg hne, Uth, if_pos hz1] at h1
  simp only [sparse, if_pos rfl, Uth, if_pos hz0] at h0
  exact hu (h0.trans h1.symm)

section geometry
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
    (hroom : 17 * ell ≤ R * M) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (e0 : Bond (scaleUp ell k Lu)) (hz : e0 ∈ Zb (S.Om 0)) (sJ : PlaqSel)

noncomputable def sparseP (θ : ℝ) : IngrBParams := gparams ell k Lu hell0 S (sparse e0 θ) a Lam
noncomputable def sparseF (θ : ℝ) : ↥(bondSupp (geomOf ell k S)) →L[ℝ] ↥(bondSupp (geomOf ell k S)) :=
  (dataS selAll sJ (sparseP hell0 a Lam e0 θ)).Ginv

include hS hell hroom hz in
theorem sparseF_diff (θ : ℝ) :
    sparseF (S := S) hell0 a Lam e0 sJ θ = sparseF (S := S) hell0 a Lam e0 sJ 0 +
      (pE (geomOf ell k S)).comp (((ContinuousLinearMap.adjoint (Wop (geomOf ell k S) (sparse e0 0) a)).comp
        (((deltaKLocCLM (sparse e0 θ) Set.univ) - (deltaKLocCLM (sparse e0 0) Set.univ)).comp
          (Wop (geomOf ell k S) (sparse e0 0) a))).comp (iE (geomOf ell k S))) := by
  have hUU : ∀ e : Bond (scaleUp ell k Lu), e ∉ Zb (S.Om 0) → sparse e0 θ e = sparse e0 0 e := by
    intro e he
    have hn : e ≠ e0 := by rintro rfl; exact he hz
    simp [sparse, hn]
  have hBoth : ∀ e : Bond (scaleUp ell k Lu), BothIn (S.Om 0) e → sparse e0 θ e = sparse e0 0 e :=
    fun e he => hUU e (fun hz => Zb_not_bothIn _ hz he)
  have hW := Wop_congr_Z hS hell hroom hUU a
  have hT := Tfull_congr hS hell hroom hBoth
  have hsec := sector_congr hS hell hroom hBoth
  unfold sparseF sparseP BaseDataS.Ginv dataS
  simp only [gparams, IngrBParams.G, IngrBParams.sector, baseData, DpiFullS, DeltaS, selAll, hW, hT, hsec]
  ext1 y
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]
  abel

include hS hell hroom hz in
theorem sparseF_cont : Continuous fun θ => sparseF (S := S) hell0 a Lam e0 sJ θ := by
  have h : (fun θ => sparseF (S := S) hell0 a Lam e0 sJ θ) = fun θ => sparseF (S := S) hell0 a Lam e0 sJ 0 +
      (pE (geomOf ell k S)).comp (((ContinuousLinearMap.adjoint (Wop (geomOf ell k S) (sparse e0 0) a)).comp
        (((deltaKLocCLM (sparse e0 θ) Set.univ) - (deltaKLocCLM (sparse e0 0) Set.univ)).comp
          (Wop (geomOf ell k S) (sparse e0 0) a))).comp (iE (geomOf ell k S))) := by
    funext θ; exact sparseF_diff hell0 hS hell hroom a Lam e0 hz sJ θ
  rw [h]
  have hd := cont_deltaKLocCLM (sparse_cont e0) (Set.univ : Set (PeriodicLatticePlaquette (scaleUp ell k Lu)))
  refine continuous_const.add (Continuous.clm_comp continuous_const (Continuous.clm_comp ?_ continuous_const))
  exact Continuous.clm_comp continuous_const (Continuous.clm_comp (hd.sub continuous_const) continuous_const)

include hS hell hroom hz in
theorem sparse_guard_near_zero (hunit : IsUnit (sparseF (S := S) hell0 a Lam e0 sJ 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ θ : ℝ, |θ| < δ → IsUnit (sparseF (S := S) hell0 a Lam e0 sJ θ) := by
  have hopen : IsOpen {F : ↥(bondSupp (geomOf ell k S)) →L[ℝ] ↥(bondSupp (geomOf ell k S)) | IsUnit F} := isOpen_isUnit_clm
  have ho := hopen.preimage (sparseF_cont hell0 hS hell hroom a Lam e0 hz sJ)
  obtain ⟨δ, hδ, hd⟩ := Metric.isOpen_iff.mp ho 0 hunit
  refine ⟨δ, hδ, fun θ hθ => hd ?_⟩
  simpa [Metric.mem_ball, Real.dist_eq] using hθ

end geometry

theorem sparse_class {ell M c k : ℕ} {S : Tower L} (hnest : ∀ j, S.Om (j+1) ⊆ S.Om j)
    (hcov : CoversOm0p ell M c k S) {α η : ℝ} (hα : 0 < α) (hM : 0 < M) (hc : 0 < c)
    (hell : 0 < ell) (hη : 0 < η) (e0 : Bond L) (hz : e0 ∈ Zb (S.Om 0)) (θ : ℝ) :
    ClassCoupled ell M c k S α η (sparse e0 θ) := by
  exact ⟨hcov, perCubeRegular2_of_one_on_om0 S hnest hα hM hc hell hη _
    (fun e he _ => sparse_base e0 hz θ e he)⟩
#print axioms sparseF_cont
#print axioms sparse_guard_near_zero
#print axioms sparse_class
#print axioms sparse_not_twist
end SolR6Family
