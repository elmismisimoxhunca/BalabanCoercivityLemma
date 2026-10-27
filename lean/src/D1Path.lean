import D1Cont
import ZR8Data
import ZR8Class

/-!
# D1Path -- the in-class path `U_θ` (SU(2) element `diag(e^{iθ}, e^{-iθ})` on every bond with NO endpoint in `Ω₀`, identity elsewhere) and the locality of `W`, `Rproj`, `Tfull`, `Mass` along it.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.D1Literal

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneR8
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap gradValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

variable {L : PeriodicLatticeExtent}

/-- bonds with NO endpoint in `Om`. -/
def Zb (Om : Set (PeriodicLatticeSite L)) : Set (Bond L) :=
  {e | e.1 ∉ Om ∧ periodicLatticeShift e.1 e.2 ∉ Om}

/-- the matrix `diag(e^{iθ}, e^{-iθ})` -/
noncomputable def uMat (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (θ * Complex.I), 0; 0, Complex.exp (-(θ * Complex.I))]

theorem uMat_mem (θ : ℝ) : uMat θ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [uMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.one_apply,
        ← Complex.exp_conj, ← Complex.exp_add]
  · simp [uMat, Matrix.det_fin_two, ← Complex.exp_add]

noncomputable def uθ (θ : ℝ) : Matrix.specialUnitaryGroup (Fin 2) ℂ := ⟨uMat θ, uMat_mem θ⟩

open Classical in
/-- the path of link configurations. -/
noncomputable def Uth (Om : Set (PeriodicLatticeSite L)) (θ : ℝ) : Cfg L :=
  fun e => if e ∈ Zb Om then uθ θ else 1

theorem uθ_zero : uθ 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uθ, uMat]

theorem Uth_zero (Om : Set (PeriodicLatticeSite L)) : Uth Om 0 = fun _ => 1 := by
  funext e; unfold Uth; split_ifs <;> simp [uθ_zero]

theorem uθ_pi_coe : ((uθ Real.pi : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uθ, uMat, Complex.exp_pi_mul_I, Complex.exp_neg]

theorem contFam_Uth (Om : Set (PeriodicLatticeSite L)) : ContFam (Uth Om) := by
  intro e
  unfold Uth
  by_cases he : e ∈ Zb Om
  · simp only [he, if_true]
    show Continuous fun θ => uMat θ
    unfold uMat
    refine continuous_matrix (fun i j => ?_)
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · simp only [he, if_false]
    exact continuous_const

theorem Uth_eq_off_Z (Om : Set (PeriodicLatticeSite L)) (θ θ' : ℝ) (e : Bond L) (he : e ∉ Zb Om) :
    Uth Om θ e = Uth Om θ' e := by
  unfold Uth; simp [he]

theorem Zb_not_bothIn (Om : Set (PeriodicLatticeSite L)) {e : Bond L} (he : e ∈ Zb Om) : ¬ BothIn Om e :=
  fun h => he.1 h.1

theorem Gp_supp (G : TowerGeom L) (U : Cfg L) (a : ℝ) (f : SiteL2 L) (x : PeriodicLatticeSite L)
    (hx : x ∉ G.Om0) : (Gp G U a f) x = 0 := by
  by_cases hu : IsUnit (DelpA G U a + (1 - siteMask G.Om0))
  · have := (Gp_spec G U a hu f).1
    have h2 := congrArg (fun g : SiteL2 L => g x) this
    simp only [siteMask_apply, if_neg hx] at h2
    exact h2.symm
  · have : Gp G U a f = 0 := by
      unfold Gp
      simp only [ContinuousLinearMap.comp_apply]
      rw [Ring.inverse_non_unit _ hu]
      simp
    rw [this]; rfl

/-- `W` is the same operator along any two configurations that agree off `Zb Ω₀` (bonds with no endpoint in `Ω₀`). -/
theorem Wop_congr_Z {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
    (hroom : 17 * ell ≤ R * M) {U U' : Cfg L} (hUU : ∀ e : Bond L, e ∉ Zb (S.Om 0) → U e = U' e) (a : ℝ) :
    Wop (geomOf ell k S) U a = Wop (geomOf ell k S) U' a := by
  have hBoth : ∀ e : Bond L, BothIn (S.Om 0) e → U e = U' e :=
    fun e he => hUU e (fun hz => Zb_not_bothIn _ hz he)
  have hT := Tfull_congr hS hell hroom hBoth
  ext1 A
  refine PiLp.ext (fun b => ?_)
  have hh : Gp (geomOf ell k S) U a (Rproj (geomOf ell k S) U (gradAdj U A))
      = Gp (geomOf ell k S) U' a (Rproj (geomOf ell k S) U' (gradAdj U' A)) := by
    rw [Gp_congr hS hell hroom hBoth a]
    have := congrArg (fun T => T A) hT
    simp only [Tfull, ContinuousLinearMap.comp_apply] at this
    rw [this]
  unfold Wop
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply]
  rw [hh]
  show (WithLp.ofLp A) b - (WithLp.ofLp (gradL2 U _)) b = (WithLp.ofLp A) b - (WithLp.ofLp (gradL2 U' _)) b
  rw [gradL2_apply, gradL2_apply]
  unfold gradValueCovariant
  by_cases hb : b ∈ Zb (S.Om 0)
  · have h1 := Gp_supp (geomOf ell k S) U' a (Rproj (geomOf ell k S) U' (gradAdj U' A)) b.1 hb.1
    have h2 := Gp_supp (geomOf ell k S) U' a (Rproj (geomOf ell k S) U' (gradAdj U' A)) _ hb.2
    simp only [h1, h2, map_zero, sub_zero]
  · rw [hUU b hb]

#print axioms Wop_congr_Z
#print axioms Gp_supp
#print axioms uθ_zero
#print axioms contFam_Uth

end AdalyFormal.D1Literal
