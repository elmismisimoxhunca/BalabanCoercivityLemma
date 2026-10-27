import D1Final
import RI6

/-!
# D1Cons -- the two readings DIFFER in truth value: the localised headline (`P428Target8`, proved in `compute/m2_rightinv_20261015`) holds, the literal one is refuted.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Literal

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.NonVac
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-- `P428Target8S selIn selIn` IS the frozen `P428Target8` (definitional, `pin_target8`), which is a theorem (`AdalyFormal.M2RightInv.p428Target8`); the literal reading is refuted (`not_P428Target8Literal`). -/
theorem localised_holds_literal_fails :
    P428Target8S selIn selIn ∧ ¬ P428Target8S selAll selAll :=
  ⟨AdalyFormal.M2RightInv.p428Target8, not_P428Target8Literal⟩

/-- **junk-free form of the defect.**  At the in-class configuration `U_π` (`-1` on the bonds with no endpoint in `Ω₀`, identity elsewhere), on the slab tower with
`M = 2^m`, `R ≥ 18`, `a = 1`, the literal quadratic form `G⁻¹ = Δ_π + D R D* + Q* a Q` (3.122) on `E₀` takes a negative value: no inverse is involved. -/
theorem literal_Ginv_indefinite (sJ : PlaqSel) {m R : ℕ} (hm : 1 ≤ m) (hR : 18 ≤ R) {α₀ : ℝ} (hα : 0 < α₀) :
    ClassCoupled 2 (2 ^ m) 12 2 (SlabNv 2 (2 ^ m) R) α₀ ((((2 : ℕ) : ℝ)) ^ 2)⁻¹
        (Uth ((SlabNv 2 (2 ^ m) R).Om 0) Real.pi) ∧
      ∃ v : ↥(bondSupp (geomOf 2 2 (SlabNv 2 (2 ^ m) R))),
        ⟪v, (dataS selAll sJ (gparams 2 2 (nvLu (2 ^ m) R) (by norm_num) (SlabNv 2 (2 ^ m) R)
            (Uth ((SlabNv 2 (2 ^ m) R).Om 0) Real.pi) 1 (LamN (2 ^ m) R))).Ginv v⟫ < 0 := by
  have hM : 0 < 2 ^ m := pow_pos (by norm_num) m
  have hM2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hdvd : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have hell : 2 ≤ 2 := le_rfl
  have hell0 : 0 < 2 := by norm_num
  have G := slabGeo_inst (ell := 2) hell hM hdvd (show 1 ≤ R by omega)
  obtain ⟨w0L, w0R, w1, w2, hQN, hP12, hQ21, hQ10⟩ := nv_widths (ell := 2) hell hM hR
  have hN : ∀ μ, scaleUp 2 2 (nvLu (2 ^ m) R) μ + 1 = nvN 2 (2 ^ m) R := fun μ => scaleUp_nv hell0 hM μ
  have hAdm : Admissible 2 (2 ^ m) R 2 (SlabNv 2 (2 ^ m) R) := slab3_admissible G hN
  have hcov : CoversOm0p 2 (2 ^ m) 12 2 (SlabNv 2 (2 ^ m) R) := slab3_coversp G w0L w0R w1 w2 hQN hP12 hQ21 hQ10 hN
  obtain ⟨x, hbd⟩ := SlabNv_bdpt hell hdvd hM hR
  have hroom : 17 * 2 ≤ R * 2 ^ m := by nlinarith
  refine ⟨⟨hcov, perCubeRegular2_of_one_on_om0 _ hAdm.1 hα hM (by norm_num) hell0 (by positivity) _
    (fun e he _ => Uth_in _ _ e he)⟩, ?_⟩
  exact Fth_pi_neg sJ hell0 1 (LamN (2 ^ m) R) hAdm hell hroom hbd (by norm_num) (by norm_num)
    AdalyFormal.Balaban.CovariantOperators.suTwoWitness AdalyFormal.Balaban.CovariantOperators.suTwoWitness_ne_zero

/-- **the literal operator does not depend on `U|Ω₀`** (p.394: "They depend on the configuration U restricted to Ω₀"): two configurations equal on every bond with both endpoints in `Ω₀`
(both are the identity there; one is `U_π`, the other the flat `U_0`) with different literal `Ginv`.  (For the localised data, `AdalyFormal.StatementLaneR8.data_congr` says the opposite.) -/
theorem literal_Ginv_depends_outside (sJ : PlaqSel) {m R : ℕ} (hm : 1 ≤ m) (hR : 18 ≤ R) :
    (∀ e : Bond (scaleUp 2 2 (nvLu (2 ^ m) R)), BothIn ((SlabNv 2 (2 ^ m) R).Om 0) e →
        Uth ((SlabNv 2 (2 ^ m) R).Om 0) Real.pi e = Uth ((SlabNv 2 (2 ^ m) R).Om 0) 0 e) ∧
      Fth sJ 2 2 (nvLu (2 ^ m) R) (by norm_num) (SlabNv 2 (2 ^ m) R) 1 (LamN (2 ^ m) R) Real.pi ≠
        Fth sJ 2 2 (nvLu (2 ^ m) R) (by norm_num) (SlabNv 2 (2 ^ m) R) 1 (LamN (2 ^ m) R) 0 := by
  have hM : 0 < 2 ^ m := pow_pos (by norm_num) m
  have hM2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hdvd : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have hell : 2 ≤ 2 := le_rfl
  have hell0 : 0 < 2 := by norm_num
  have G := slabGeo_inst (ell := 2) hell hM hdvd (show 1 ≤ R by omega)
  have hN : ∀ μ, scaleUp 2 2 (nvLu (2 ^ m) R) μ + 1 = nvN 2 (2 ^ m) R := fun μ => scaleUp_nv hell0 hM μ
  have hAdm : Admissible 2 (2 ^ m) R 2 (SlabNv 2 (2 ^ m) R) := slab3_admissible G hN
  obtain ⟨x, hbd⟩ := SlabNv_bdpt hell hdvd hM hR
  have hroom : 17 * 2 ≤ R * 2 ^ m := by nlinarith
  refine ⟨fun e he => ?_, fun heq => ?_⟩
  · rw [Uth_in _ _ e he.1, Uth_in _ _ e he.1]
  · obtain ⟨v, hv⟩ := Fth_pi_neg sJ hell0 1 (LamN (2 ^ m) R) hAdm hell hroom hbd (by norm_num) (by norm_num)
      AdalyFormal.Balaban.CovariantOperators.suTwoWitness AdalyFormal.Balaban.CovariantOperators.suTwoWitness_ne_zero
    have h0 := Fth_zero_psd sJ hell0 1 (LamN (2 ^ m) R) (S := SlabNv 2 (2 ^ m) R) (by norm_num) v
    rw [heq] at hv
    linarith

#print axioms literal_Ginv_depends_outside
#print axioms literal_Ginv_indefinite
#print axioms localised_holds_literal_fails
#print axioms AdalyFormal.M2RightInv.p428Target8

end AdalyFormal.D1Literal
