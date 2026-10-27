import NB25
import CB9
/-!
# NB26 -- PER-CUBE TOWER CLASS for every `ell ≥ 2` (dyadic included), from the (3.35) chart of one cube

`cube_tower_class_na`: `K : CubeChart U B η c1 c2` at the printed scales `c1 = a (ell^j η)⁻¹`,
`c2 = a (ell^j η)⁻²` (`a = f M α₀`), `a ≤ 1`, `4·10⁶ ell² (4π+4) a ≤ 1`, `ell^j ∣ N_ρ`, `2 ell^j < N_ρ`.
Then for every `l ≤ j` and every `ell^l`-aligned bond `c` whose cones stay in the cube
(`GoodBd` w.r.t. sites all of whose plaquettes are in the cube, `goodL` w.r.t. the cube's bonds):

  `dv (ubarTowerSU2 ell (U^g) l c) ≤ a (1 + 3π(4π+4)) · ell^l / ell^j`      (cube gauge `g = K.g`).

The constant is independent of `ell`, `l`, `j`, `k` and the volume.

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.Balaban.BlockedBackground (ubarTowerSU2)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)

variable {L : PeriodicLatticeExtent}

theorem cube_tower_class_na (ell : ℕ) (hell : 2 ≤ ell)
    {U : PeriodicLinkConfiguration SU2 L} {B : PeriodicLatticeEdge L → Prop} {η a : ℝ} (j : ℕ)
    (hη : 0 < η) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (K : CubeChart U B η (a * (((ell : ℝ) ^ j * η)⁻¹ ^ 1)) (a * (((ell : ℝ) ^ j * η)⁻¹ ^ 2)))
    (hdvd : ∀ ρ, ell ^ j ∣ L ρ + 1) (hN : ∀ ρ, 2 * ell ^ j < L ρ + 1)
    (hsm : 4000000 * (ell : ℝ) ^ 2 * ((4 * Real.pi + 4) * a) ≤ 1)
    (l : ℕ) (hlj : l ≤ j) (c : PeriodicLatticeEdge L) (hc : c.1 ∈ CoarseLattice L (ell ^ l))
    (hgB : GoodBd ell (fun y => ∀ ν μ : Fin 3, plaqIn B (y, ν, μ)) l c) (hgL : goodL ell B l c) :
    dv (ubarTowerSU2 ell (periodicGaugeTransform K.g U) l c)
      ≤ a * (1 + 3 * Real.pi * (4 * Real.pi + 4)) * ((ell : ℝ) ^ l / (ell : ℝ) ^ j) := by
  have hpi := Real.pi_pos
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  have hPj : 0 < (ell : ℝ) ^ j := by positivity
  have e1 : η * (a * (((ell : ℝ) ^ j * η)⁻¹ ^ 1)) = a / (ell : ℝ) ^ j := by field_simp
  have e2 : η ^ 2 * (a * (((ell : ℝ) ^ j * η)⁻¹ ^ 2)) = a / ((ell : ℝ) ^ j) ^ 2 := by field_simp
  have hsmall1 : η * (a * (((ell : ℝ) ^ j * η)⁻¹ ^ 1)) ≤ 1 := by
    rw [e1, div_le_one hPj]; exact le_trans ha1 (one_le_pow₀ hellR)
  set q0 : ℝ := (4 * Real.pi + 4) * a / ((ell : ℝ) ^ j) ^ 2
  have hq0 : 0 ≤ q0 := by positivity
  have h0 : ∀ y, (∀ ν μ : Fin 3, plaqIn B (y, ν, μ)) → ∀ ν μ,
      dv (pw 1 (periodicGaugeTransform K.g U) y ν μ) ≤ q0 := by
    intro y hy ν μ
    have := cube_plaq hη K hsmall1 (y, ν, μ) (hy ν μ)
    rw [e1, e2] at this
    refine le_trans this ?_
    have hsq : (a / (ell : ℝ) ^ j) ^ 2 ≤ a / ((ell : ℝ) ^ j) ^ 2 := by
      rw [div_pow]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    simp only [q0]
    have : 2 * (a / ((ell : ℝ) ^ j) ^ 2) + (4 * Real.pi + 2) * (a / ((ell : ℝ) ^ j) ^ 2)
        = (4 * Real.pi + 4) * a / ((ell : ℝ) ^ j) ^ 2 := by ring
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0:ℝ) ≤ 4 * Real.pi + 2)]
  have he : ∀ b, B b → dv (periodicGaugeTransform K.g U b) ≤ a / (ell : ℝ) ^ j := by
    intro b hb; rw [← e1]; exact cube_link hη K b hb
  have hsmall : 4000000 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ j * q0) ≤ 1 := by
    have : ((ell : ℝ) ^ 2) ^ j * q0 = (4 * Real.pi + 4) * a := by
      simp only [q0]; rw [← pow_mul, mul_comm 2 j, pow_mul]; field_simp
    rw [this]; exact hsm
  have h := link_tower_na_loc ell hell (periodicGaugeTransform K.g U)
    (fun y => ∀ ν μ : Fin 3, plaqIn B (y, ν, μ)) B q0 (a / (ell : ℝ) ^ j) hq0 h0 he j hdvd hN hsmall
    l hlj c hc hgB hgL
  refine le_trans h ?_
  set t : ℝ := (ell : ℝ) ^ l / (ell : ℝ) ^ j
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by rw [div_le_one hPj]; exact pow_le_pow_right₀ hellR hlj
  have hA : (ell : ℝ) ^ l * (a / (ell : ℝ) ^ j) = a * t := by simp only [t]; ring
  have hB2 : ((ell : ℝ) ^ 2) ^ l * q0 = (4 * Real.pi + 4) * a * t ^ 2 := by
    simp only [q0, t]; rw [← pow_mul, mul_comm 2 l, pow_mul]; field_simp
  rw [hA, hB2]
  have h2 : t ^ 2 ≤ t := by nlinarith
  have hc0 : 0 ≤ 3 * Real.pi * ((4 * Real.pi + 4) * a) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 hc0]

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.cube_tower_class_na
