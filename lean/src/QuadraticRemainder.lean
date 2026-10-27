import FittedGeometry

set_option autoImplicit false
noncomputable section
namespace Prop1.ScaleFittedProof

open AdalyFormal.Balaban.SuTwoLogExp
  (SU2 M2 su2Log su2Exp su2Angle su2NegOne)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_nonneg frobNorm_zero)
open AdalyFormal.Balaban.Bch2
  (IsSu2 expProd isSu2_su2Log bch2_telescope frobNorm_listMap_nonneg
   angle_le_of_frobNorm_sub_one ne_negOne_of_angle_le)

/-- Branch and norm control from the actual group deviation, not a postulated
small Lie algebra representative. -/
theorem log_branch_and_bound (g : SU2) (hg : frobNorm ((g : M2) - 1) ≤ 2) :
    su2Exp (su2Log g) = g ∧
      frobNorm (su2Log g) ≤ 2 * frobNorm ((g : M2) - 1) := by
  have hcap := angle_le_of_frobNorm_sub_one hg
  refine ⟨AdalyFormal.Balaban.RegularityGap.su2_exp_log_of_ne_negOne g
    (ne_negOne_of_angle_le hcap), ?_⟩
  have h := AdalyFormal.Balaban.Bch2.frobNorm_su2Log_le hcap
  have hd := frobNorm_nonneg ((g : M2) - 1)
  have hp : Real.pi / 2 ≤ 2 := by linarith [Real.pi_lt_four]
  exact h.trans (mul_le_mul_of_nonneg_right hp hd)

/-- Leading coefficient ONE. A fixed Lipschitz constant greater than one would
not suffice for (51); the loss here is genuinely quadratic in the deviation. -/
theorem log_bound_leading_one (g : SU2) (hg : frobNorm ((g : M2) - 1) ≤ 1) :
    frobNorm (su2Log g) ≤ frobNorm ((g : M2) - 1) +
      (frobNorm ((g : M2) - 1)) ^ 2 := by
  let d := frobNorm ((g : M2) - 1)
  let a := su2Angle g
  let r := Real.sqrt 2
  have hd : 0 ≤ d := frobNorm_nonneg _
  have hd1 : d ≤ 1 := hg
  have ha : 0 ≤ a := AdalyFormal.Balaban.Bch2.su2Angle_nonneg g
  have hr : 1 ≤ r := by dsimp [r]; exact Real.one_le_sqrt.mpr (by norm_num)
  have hr0 : 0 ≤ r := le_trans (by norm_num) hr
  have hcap := angle_le_of_frobNorm_sub_one (le_trans hg (by norm_num : (1:ℝ) ≤ 2))
  have hlog : frobNorm (su2Log g) = r * a :=
    AdalyFormal.Balaban.BlockingLinkEstimate.frobNorm_su2Log_eq g
      (ne_negOne_of_angle_le hcap)
  have hlin : r * a ≤ 2 * d := by
    rw [← hlog]
    exact (log_branch_and_bound g (le_trans hg (by norm_num))).2
  have ha2 : a ≤ 2 * d := by nlinarith
  have hsin : a / 2 - (a / 2) ^ 3 / 4 ≤ Real.sin (a / 2) := by
    rcases eq_or_lt_of_le ha with hz | hp
    · rw [← hz]; norm_num
    · exact le_of_lt (Real.sin_gt_sub_cube (by linarith) (by linarith))
  have hdev : d = 2 * r * Real.sin (a / 2) :=
    AdalyFormal.Balaban.BlockingLinkEstimate.frobNorm_sub_one_eq g
  have htaylor : r * a ≤ d + (r * a) * a ^ 2 / 16 := by
    have h := mul_le_mul_of_nonneg_left hsin (show 0 ≤ 2 * r by positivity)
    rw [← hdev] at h
    nlinarith [h]
  have hasq : a ^ 2 ≤ 4 * d ^ 2 := by nlinarith
  have hprod := mul_le_mul hlin hasq (sq_nonneg a) (mul_nonneg (by norm_num) hd)
  have hcube : d * d ^ 2 ≤ d ^ 2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hd1 (sq_nonneg d)
  rw [hlog]
  change r * a ≤ d + d ^ 2
  nlinarith [hprod, hcube]

/-- Match the existing exponential-list theorem to actual group-valued bonds. -/
theorem expProd_logs (gs : List SU2)
    (h : ∀ g ∈ gs, frobNorm ((g : M2) - 1) ≤ 2) :
    expProd (gs.map su2Log) = gs.prod := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.map_cons, AdalyFormal.Balaban.Bch2.expProd_cons, List.prod_cons]
      rw [(log_branch_and_bound g (h g (by simp))).1,
        ih (fun x hx => h x (by simp [hx]))]

/-- Discharge the BCH telescope's sum-smallness and branch obligations using
the sum of actual Frobenius bond deviations. Constants do not depend on length.
This is a genuine second-order path-log remainder, NOT the plaquette theorem. -/
theorem path_log_quadratic (gs : List SU2)
    (hsmall : (gs.map (fun g : SU2 => frobNorm ((g : M2) - 1))).sum ≤ 1/16) :
    frobNorm (su2Log gs.prod - (gs.map su2Log).sum) ≤
      56 * ((gs.map (fun g : SU2 => frobNorm ((g : M2) - 1))).sum) ^ 2 := by
  let d : SU2 → ℝ := fun g : SU2 => frobNorm ((g : M2) - 1)
  change (gs.map d).sum ≤ 1/16 at hsmall
  have hnonneg : ∀ g : SU2, 0 ≤ d g := fun g => frobNorm_nonneg _
  have hsum0 : 0 ≤ (gs.map d).sum := List.sum_nonneg (by
    intro x hx
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx
    exact hnonneg g)
  have hbond : ∀ g ∈ gs, d g ≤ 2 := by
    intro g hg
    have hs : d g ≤ (gs.map d).sum := List.single_le_sum
      (fun x hx => by
        obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
        exact hnonneg u) (d g) (List.mem_map.mpr ⟨g, hg, rfl⟩)
    exact hs.trans (hsmall.trans (by norm_num))
  have hlogs : ((gs.map su2Log).map frobNorm).sum ≤ 2 * (gs.map d).sum := by
    clear hsmall hsum0
    induction gs with
    | nil => simp
    | cons g gs ih =>
        simp only [List.map_cons, List.sum_cons] at *
        have htail : ∀ x ∈ gs, d x ≤ 2 := fun x hx => hbond x (by simp [hx])
        have hb := (log_branch_and_bound g (hbond g (by simp))).2
        have ht := ih htail
        dsimp [d] at *
        linarith
  have hlogs0 : 0 ≤ ((gs.map su2Log).map frobNorm).sum :=
    frobNorm_listMap_nonneg _
  have ht := bch2_telescope (gs.map su2Log) (by
    intro X hX
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hX
    exact isSu2_su2Log g) (by linarith)
  rw [expProd_logs gs hbond] at ht
  calc
    _ ≤ 14 * (((gs.map su2Log).map frobNorm).sum) ^ 2 := ht
    _ ≤ 56 * ((gs.map d).sum) ^ 2 := by nlinarith

end Prop1.ScaleFittedProof

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[`Prop1.ScaleFittedProof.log_branch_and_bound,
      `Prop1.ScaleFittedProof.log_bound_leading_one,
      `Prop1.ScaleFittedProof.expProd_logs,
      `Prop1.ScaleFittedProof.path_log_quadratic] do
    let axioms ← Lean.collectAxioms n
    Lean.logInfo m!"QUADRATIC_AXIOMS {n}: {axioms}"
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in {n}: {ax}"
