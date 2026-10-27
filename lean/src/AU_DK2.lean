import AU_CUT
import DK2

open AdalyFormal.AllU (M1BoundsU M1RegularU)

/-! AU copy of DK2: M1Regular -> M1RegularU, affected declarations only (lane allc_20261016, uniform-in-c route). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DK

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible bigSide pdist pcd scaleUp)
open AdalyFormal.StatementLaneG (LambdaOK2)
open AdalyFormal.StatementLaneR8 (pdist_triangle pdist_comm pdist_self pdist_coarseShift_le)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.CurvBlock (dv pw PlaqT plaqIn CubeChart cube_link cube_plaq link_tower_na_loc)
open AdalyFormal.IngredientFamilyR2 (embY embY_val)

variable {L : PeriodicLatticeExtent}

/-- **the M1 chart on `Ω_k`**: links and plaquettes. -/
theorem chart_boundsU (ell M k : ℕ) (hell : 0 < ell) (S : Tower L) (α₀ : ℝ) (U : LinkCfg L)
    (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (η : ℝ) (hη : η = ((ell : ℝ) ^ k)⁻¹)
    (hg : ∀ e : Bond L, ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
        = NormedSpace.exp (((η : ℂ) * Complex.I) • A e))
    (hb : AdalyFormal.AllU.M1BoundsU S ell M 12 k α₀ η A)
    (hα : 0 ≤ α₀) (hβ1 : (12 : ℝ) * M * α₀ ≤ 1) :
    (∀ e : PeriodicLatticeEdge L, BK S k e → dv (periodicGaugeTransform g U e) ≤ (12 * M * α₀) / (ell : ℝ) ^ k) ∧
    (∀ t : PlaqT L, plaqIn (BK S k) t →
      dv (pw 1 (periodicGaugeTransform g U) t.1 t.2.1 t.2.2)
        ≤ (2 * (12 * M * α₀) + (4 * Real.pi + 2) * (12 * M * α₀) ^ 2) / ((ell : ℝ) ^ k) ^ 2) := by
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := pow_pos (by exact_mod_cast hell) k
  have hn1 : (1 : ℝ) ≤ (ell : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hell)
  have hη0 : 0 < η := by rw [hη]; positivity
  have hnη : (ell : ℝ) ^ k * η = 1 := by rw [hη]; exact mul_inv_cancel₀ hn.ne'
  set β : ℝ := 12 * M * α₀ with hβ
  have hc1 : ((12 : ℕ) : ℝ) * M * α₀ * (((ell : ℝ) ^ k * η)⁻¹ ^ 1) = β := by rw [hnη]; push_cast; ring
  have hc2 : ((12 : ℕ) : ℝ) * M * α₀ * (((ell : ℝ) ^ k * η)⁻¹ ^ 2) = β := by rw [hnη]; push_cast; ring
  have hbs : ∀ e : Bond L, BK S k e → k ≤ AdalyFormal.M1.bstrat S k e :=
    fun e he => AdalyFormal.M1.le_bstrat_of_mem le_rfl e he.1 he.2
  let K : CubeChart U (BK S k) η β β :=
    ⟨g, A, fun e he => ⟨hb.1 e, hg e, by rw [← hc1]; exact hb.2.1 e k (hbs e he)⟩,
      fun μ ν x h1 h2 => by rw [← hc2]; exact hb.2.2.1 μ ν x k (hbs _ h1) (hbs _ h2)⟩
  have hsmall : η * β ≤ 1 := by
    have : η ≤ 1 := by rw [hη]; exact inv_le_one_of_one_le₀ hn1
    have hβ0 : 0 ≤ β := by positivity
    nlinarith
  refine ⟨fun e he => ?_, fun t ht => ?_⟩
  · have := cube_link hη0 K e he
    refine this.trans (le_of_eq ?_)
    rw [hη, div_eq_inv_mul]
  · have := cube_plaq hη0 K hsmall t ht
    refine this.trans (le_of_eq ?_)
    rw [hη]; field_simp

end AdalyFormal.M1DK

