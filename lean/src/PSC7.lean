import SC6
import PGFC22

/-!
# SC7 -- EXPLICIT, `k`-uniform-in-the-SCALED-norm coercivity of the genuine flat `G₁⁻¹ = Δ_a(1)`.

`G1inv_coercive_explicit`:  for every `ell k a>0`, every unit torus `Lu` and every `Λ`,
    `cellC (ell^k) (a n/n^8) · ‖x‖² ≤ ⟨x, G₁⁻¹ x⟩`   (`n = ell^k`),
and `scaled_G1inv`:  `ell^{2k} ⟨x, G₁⁻¹ x⟩ ≥ hfun(a) ‖x‖²` with `hfun` independent of `k` and of the volume.
Standard axioms only.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
open scoped ComplexInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GenuineU1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.FlatCoercivity

namespace AdalyFormal.ScaledCoercivity

/-- **EXPLICIT volume-independent coercivity of the genuine flat `G₁⁻¹`**. -/
theorem G1inv_coercive_explicit (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (ha : 0 < a)
    (Lu : PeriodicLatticeExtent) (Lam : Set (PeriodicLatticeSite Lu))
    (x : ↥(bondSupp (PK ell k Lu hell a Lam).G)) :
    cellC (ell ^ k) (a * ((ell ^ k : ℕ) : ℝ) / ((ell ^ k : ℕ) : ℝ) ^ 8) * ‖x‖ ^ 2
      ≤ inner ℝ x ((PK ell k Lu hell a Lam).G1inv x) := by
  have hn : 0 < ell ^ k := pow_pos hell k
  have hnR : (0 : ℝ) < ((ell ^ k : ℕ) : ℝ) := by exact_mod_cast hn
  set κ : ℝ := a * ((ell ^ k : ℕ) : ℝ) / ((ell ^ k : ℕ) : ℝ) ^ 8 with hκ
  have hκpos : 0 < κ := by positivity
  have hFS : (PK ell k Lu hell a Lam).FullSupp := PK_fullSupp ell k Lu hell a Lam
  have hform := Gen.G1inv_form (PK ell k Lu hell a Lam) hFS (PK_Om0_univ ell k Lu hell a Lam) rfl x
  rw [hform]
  set A : BondFnL2 (scaleUp ell k Lu) := iE (PK ell k Lu hell a Lam).G x with hA
  have hdvd : ∀ μ, ell ^ k ∣ scaleUp ell k Lu μ + 1 := scaleUp_tiling ell k Lu hell
  have hx : ‖x‖ = ‖A‖ := rfl
  have h1 := curl_energy A
  have h2 := R_lower ell k Lu hell A
  have h3 := Qnorm_eq ell k Lu hell a Lam x
  rw [← hA] at h3
  have h4 := Qsum hn hdvd (WithLp.ofLp A)
  have h5 := norm_bond A
  have hT : ‖Tfull (PK ell k Lu hell a Lam).G (PK ell k Lu hell a Lam).U A‖
      = ‖Rproj (geomOf ell k (fullTower ell k Lu)) (flatCfg : PeriodicLinkConfiguration
          (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) (gradAdj flatCfg A)‖ := rfl
  show cellC (ell ^ k) κ * ‖x‖ ^ 2 ≤ ‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) A‖ ^ 2 +
      ‖Tfull (PK ell k Lu hell a Lam).G (PK ell k Lu hell a Lam).U A‖ ^ 2 +
      (PK ell k Lu hell a Lam).a * ((PK ell k Lu hell a Lam).ell : ℝ) ^ (PK ell k Lu hell a Lam).k * ‖(PK ell k Lu hell a Lam).data.Q x‖ ^ 2
  have e : (PK ell k Lu hell a Lam).a * ((PK ell k Lu hell a Lam).ell : ℝ) ^ (PK ell k Lu hell a Lam).k
      = a * (ell : ℝ) ^ k := rfl
  have hT2 : ‖Tfull (PK ell k Lu hell a Lam).G (PK ell k Lu hell a Lam).U A‖ ^ 2
      = ‖Rproj (geomOf ell k (fullTower ell k Lu)) (flatCfg : PeriodicLinkConfiguration
          (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) (gradAdj flatCfg A)‖ ^ 2 := by
    have := congrArg (fun t => t ^ 2) hT
    exact this
  have hQ2 : a * (ell : ℝ) ^ k * ‖(PK ell k Lu hell a Lam).data.Q x‖ ^ 2
      = κ * ∑ j, ‖L2 hdvd (coordB (WithLp.ofLp A) j)‖ ^ 2 := by
    refine (congrArg (fun t => a * (ell : ℝ) ^ k * t) (h3.trans h4)).trans ?_
    rw [hκ]; push_cast; field_simp
  rw [e, hQ2]
  have hper : ∀ j, cellC (ell ^ k) κ * ‖coordB (WithLp.ofLp A) j‖ ^ 2 ≤
      ‖L1 (scaleUp ell k Lu) (coordB (WithLp.ofLp A) j)‖ ^ 2 + κ * ‖L2 hdvd (coordB (WithLp.ofLp A) j)‖ ^ 2
        + ‖L3 hdvd (coordB (WithLp.ofLp A) j)‖ ^ 2 := by
    intro j
    exact torus_coercive_kappa hn hκpos.le
      (fun z w S hS0 hS => cell_coercive_explicit hn κ hκpos z w S hS0 hS)
      (scaleUp ell k Lu) hdvd (coordB (WithLp.ofLp A) j)
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hper j)
  rw [← Finset.mul_sum] at hsum
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hxx : cellC (ell ^ k) κ * ‖x‖ ^ 2 = cellC (ell ^ k) κ * ∑ j, ‖coordB (WithLp.ofLp A) j‖ ^ 2 := by
    rw [hx, h5]
  rw [hxx, h1, hT2]
  exact hsum.trans (by
    have := add_le_add_left h2 (∑ j, ‖L1 (scaleUp ell k Lu) (coordB (WithLp.ofLp A) j)‖ ^ 2
      + κ * ∑ j, ‖L2 hdvd (coordB (WithLp.ofLp A) j)‖ ^ 2)
    linarith)

#print axioms G1inv_coercive_explicit

end AdalyFormal.ScaledCoercivity
