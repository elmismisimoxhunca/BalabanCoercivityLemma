import DK2DepthWitnessGate
import RawLinearization

set_option autoImplicit false
noncomputable section
namespace Prop1.ScaleFittedRepair

open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Exp)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_nonneg)
open AdalyFormal.Balaban.Bch2
  (IsSu2 isSu2_su2Log frobNorm_add_le log_exp nu nu_nonneg
   frobNorm_eq_sqrt_two_mul_nu angle_le_of_frobNorm_sub_one ne_negOne_of_angle_le)
open AdalyFormal.Balaban.BlockingLinkEstimate
  (frobNorm_su2Exp_sub_one_le frobNorm_sub_one_le_frobNorm_su2Log)
open AdalyFormal.Balaban.RegularUQChain (frobNorm_su_mul_sub_one_le)
open Prop1.ScaleFittedProof
  (convex_norm_bound isSu2_weighted_sum log_branch_and_bound log_bound_leading_one
   path_log_quadratic)

/-- Exact noncommutative transport. No bond or winding holonomy must be small.
The last two corrections are inverted because their edges are traversed backwards. -/
theorem plaquette_transport {G : Type*} [Group G]
    (a b c d e f g h : G) :
    (e*a) * (f*b) * (g*c)⁻¹ * (h*d)⁻¹ =
      e * (a*f*a⁻¹) * ((a*b*c⁻¹)*g⁻¹*(a*b*c⁻¹)⁻¹) *
        ((a*b*c⁻¹*d⁻¹)*h⁻¹*(a*b*c⁻¹*d⁻¹)⁻¹) * (a*b*c⁻¹*d⁻¹) := by
  group

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeEdge PeriodicLinkConfiguration)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)
open AdalyFormal.Balaban.UbarTowerCov (coarseBondVar loopVar stridedBlockedGauge)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)

/-- Exact specialization to the protected raw averaging operator. In particular
this never assumes the coarse bond is near the identity. -/
theorem raw_relative_exact {L : PeriodicLatticeExtent} (s ell : ℕ)
    (V : PeriodicLinkConfiguration SU2 L) (c : PeriodicLatticeEdge L) :
    ubarSU2 s ell V c * (coarseBondVar s ell V c)⁻¹ =
      su2Exp (∑ x ∈ stepBlockOf c.1 s ell,
        ((ell : ℚ)^3)⁻¹ • su2Log (loopVar s ell V c x)) := by
  change (su2Exp _ * coarseBondVar s ell V c) * (coarseBondVar s ell V c)⁻¹ = _
  simp only [mul_inv_cancel_right, AdalyFormal.Balaban.SuTwoLogExp.su2LogExp_log]

/-- The only logarithm branch condition concerns the small closed-loop correction,
not the open contour or the coarse bond. -/
theorem weighted_loop_control {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (hw : ∀ x ∈ S, 0 ≤ w x) (hsum : ∑ x ∈ S, w x = 1)
    (W : ι → SU2) (r : ℝ) (_hr : 0 ≤ r) (hrsmall : r ≤ 1/64)
    (hW : ∀ x ∈ S, frobNorm ((W x : M2) - 1) ≤ r) :
    let H := ∑ x ∈ S, w x • su2Log (W x)
    su2Log (su2Exp H) = H ∧ frobNorm ((su2Exp H : M2) - 1) ≤ 2*r := by
  dsimp only
  let H := ∑ x ∈ S, w x • su2Log (W x)
  have hH : frobNorm H ≤ 2*r := convex_norm_bound S w hw hsum _ _ (by
    intro x hx
    have h := (log_branch_and_bound (W x) ((hW x hx).trans (by linarith))).2
    linarith [hW x hx])
  have halg : IsSu2 H := isSu2_weighted_sum S w _ (fun x _ => isSu2_su2Log _)
  have hn : nu H ≤ frobNorm H := by
    rw [frobNorm_eq_sqrt_two_mul_nu]
    have hs : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
    nlinarith [nu_nonneg H]
  have hbranch : su2Log (su2Exp H) = H := log_exp halg (by linarith [Real.pi_gt_three])
  exact ⟨hbranch, (frobNorm_su2Exp_sub_one_le H hbranch).trans hH⟩

/-- Four transported small corrections and one small CLOSED rectangle.
The individual coarse bonds do not appear among these hypotheses. -/
theorem transported_log_error (F : Fin 4 → SU2) (P : SU2) (r b : ℝ)
    (hr : 0 ≤ r) (hb : 0 ≤ b) (hsmall : 4*r+b ≤ 1/16)
    (hF : ∀ i, frobNorm ((F i : M2) - 1) ≤ r)
    (hP : frobNorm ((P : M2) - 1) ≤ b) :
    frobNorm (su2Log (F 0 * F 1 * F 2 * F 3 * P) -
      (su2Log (F 0) + su2Log (F 1) + su2Log (F 2) + su2Log (F 3) + su2Log P))
        ≤ 56 * (4*r+b)^2 := by
  let gs : List SU2 := [F 0, F 1, F 2, F 3, P]
  have hsum : (gs.map (fun g : SU2 => frobNorm ((g : M2)-1))).sum ≤ 4*r+b := by
    simp only [gs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    linarith [hF 0, hF 1, hF 2, hF 3]
  have h0 : 0 ≤ (gs.map (fun g : SU2 => frobNorm ((g : M2)-1))).sum := by
    apply List.sum_nonneg
    intro v hv
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hv
    exact frobNorm_nonneg _
  have h := path_log_quadratic gs (hsum.trans hsmall)
  have hsquare : 56 * ((gs.map (fun g : SU2 => frobNorm ((g : M2)-1))).sum)^2
      ≤ 56 * (4*r+b)^2 := by nlinarith
  exact (by simpa [gs, mul_assoc, add_assoc] using h.trans hsquare)

/-- Generic transport-based averaging theorem. The leading coefficient is ONE.
`P` is the coarse rectangle; each `W i x` is a transported loop correction.
The pointwise products are the translated rectangles. All open coarse bonds may
be arbitrarily large. Geometry is an explicit premise, not a hidden axiom. -/
theorem transported_average_bound {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (hw : ∀ x ∈ S, 0 ≤ w x) (hsum : ∑ x ∈ S, w x = 1)
    (W : Fin 4 → ι → SU2) (P : SU2) (r b : ℝ)
    (hr : 0 ≤ r) (hb : 0 ≤ b) (hsmall : 8*r+b ≤ 1/16)
    (hW : ∀ i x, x ∈ S → frobNorm ((W i x : M2)-1) ≤ r)
    (hP : frobNorm ((P : M2)-1) ≤ b)
    (hrect : ∀ x ∈ S,
      frobNorm (((W 0 x * W 1 x * W 2 x * W 3 x * P : SU2) : M2)-1) ≤ b) :
    let A := fun i : Fin 4 => su2Exp (∑ x ∈ S, w x • su2Log (W i x))
    frobNorm (((A 0 * A 1 * A 2 * A 3 * P : SU2) : M2)-1) ≤
      b + b^2 + 56 * (8*r+b)^2 + 56 * (4*r+b)^2 := by
  let H := fun i : Fin 4 => ∑ x ∈ S, w x • su2Log (W i x)
  let A := fun i : Fin 4 => su2Exp (H i)
  let Q := fun x => W 0 x * W 1 x * W 2 x * W 3 x * P
  let Qbar := A 0 * A 1 * A 2 * A 3 * P
  let T := fun x => su2Log (W 0 x) + su2Log (W 1 x) + su2Log (W 2 x) +
    su2Log (W 3 x) + su2Log P
  let M := ∑ x ∈ S, w x • su2Log (Q x)
  let N := H 0 + H 1 + H 2 + H 3 + su2Log P
  have hac : ∀ i, su2Log (A i) = H i ∧ frobNorm ((A i : M2)-1) ≤ 2*r := by
    intro i
    exact weighted_loop_control S w hw hsum (W i) r hr (by linarith) (hW i)
  have hbar : frobNorm (su2Log Qbar - N) ≤ 56 * (8*r+b)^2 := by
    have h := transported_log_error A P (2*r) b (by positivity) hb
      (by linarith) (fun i => (hac i).2) hP
    simpa only [(hac 0).1, (hac 1).1, (hac 2).1, (hac 3).1,
      show 4*(2*r)+b = 8*r+b by ring] using h
  have hN : N = ∑ x ∈ S, w x • T x := by
    simp only [T, smul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_smul, hsum, one_smul]
  have hmeanerr : frobNorm (M-N) ≤ 56 * (4*r+b)^2 := by
    rw [hN]
    change frobNorm ((∑ x ∈ S, w x • su2Log (Q x)) - _) ≤ _
    rw [← Finset.sum_sub_distrib]
    simp only [← smul_sub]
    exact convex_norm_bound S w hw hsum _ _ (fun x hx =>
      transported_log_error (fun i => W i x) P r b hr hb (by linarith)
        (fun i => hW i x hx) hP)
  have hM : frobNorm M ≤ b+b^2 := convex_norm_bound S w hw hsum _ _ (by
    intro x hx
    have hd := frobNorm_nonneg ((Q x : M2)-1)
    have hdev : frobNorm ((Q x : M2)-1) ≤ b := hrect x hx
    have hlog := log_bound_leading_one (Q x) (hdev.trans (by linarith))
    nlinarith)
  have hdevbar : frobNorm ((Qbar : M2)-1) ≤ 8*r+b := by
    have h1 := frobNorm_su_mul_sub_one_le (A 0) (A 1)
    have h2 := frobNorm_su_mul_sub_one_le (A 0 * A 1) (A 2)
    have h3 := frobNorm_su_mul_sub_one_le (A 0 * A 1 * A 2) (A 3)
    have h4 := frobNorm_su_mul_sub_one_le (A 0 * A 1 * A 2 * A 3) P
    change frobNorm (((A 0 * A 1 * A 2 * A 3 * P : SU2) : M2)-1) ≤ _
    linarith [(hac 0).2, (hac 1).2, (hac 2).2, (hac 3).2]
  have hnot : Qbar ≠ AdalyFormal.Balaban.SuTwoLogExp.su2NegOne :=
    ne_negOne_of_angle_le (angle_le_of_frobNorm_sub_one (hdevbar.trans (by linarith)))
  have hlogbar : frobNorm (su2Log Qbar) ≤
      frobNorm (su2Log Qbar-N) + frobNorm (M-N) + frobNorm M := by
    have heq : su2Log Qbar = (su2Log Qbar-N) + (-(M-N)) + M := by abel
    calc
      _ = frobNorm ((su2Log Qbar-N) + (-(M-N)) + M) := by rw [← heq]
      _ ≤ frobNorm ((su2Log Qbar-N) + (-(M-N))) + frobNorm M := frobNorm_add_le _ _
      _ ≤ _ := by
        have ht := frobNorm_add_le (su2Log Qbar-N) (-(M-N))
        rw [AdalyFormal.Balaban.RegularityGap.frobNorm_neg] at ht
        linarith
  change frobNorm ((Qbar : M2)-1) ≤ _
  have hdevlog := frobNorm_sub_one_le_frobNorm_su2Log Qbar hnot
  linarith

/-- Concrete dimension-three constants once geometric loop and rectangle bounds
are supplied. This is not declared to be ScaleFittedPropagation. -/
theorem transported_average_prop1_shape {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (hw : ∀ x ∈ S, 0 ≤ w x) (hsum : ∑ x ∈ S, w x = 1)
    (W : Fin 4 → ι → SU2) (P : SU2) (b : ℝ)
    (hb : 0 ≤ b) (hsmall : b ≤ 1/400)
    (hW : ∀ i x, x ∈ S → frobNorm ((W i x : M2)-1) ≤ 3*b)
    (hP : frobNorm ((P : M2)-1) ≤ b)
    (hrect : ∀ x ∈ S,
      frobNorm (((W 0 x * W 1 x * W 2 x * W 3 x * P : SU2) : M2)-1) ≤ b) :
    let A := fun i : Fin 4 => su2Exp (∑ x ∈ S, w x • su2Log (W i x))
    frobNorm (((A 0 * A 1 * A 2 * A 3 * P : SU2) : M2)-1) ≤ b + 44465*b^2 := by
  have h := transported_average_bound S w hw hsum W P (3*b) b (by positivity) hb
    (by linarith) hW hP hrect
  have heq : b + b^2 + 56*(8*(3*b)+b)^2 + 56*(4*(3*b)+b)^2 =
      b+44465*b^2 := by ring
  rwa [heq] at h

end Prop1.ScaleFittedRepair

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[`Prop1.ScaleFittedRepair.plaquette_transport,
      `Prop1.ScaleFittedRepair.raw_relative_exact,
      `Prop1.ScaleFittedRepair.weighted_loop_control,
      `Prop1.ScaleFittedRepair.transported_log_error,
      `Prop1.ScaleFittedRepair.transported_average_bound,
      `Prop1.ScaleFittedRepair.transported_average_prop1_shape] do
    let axioms ← Lean.collectAxioms n
    Lean.logInfo m!"TRANSPORT_CORE_AXIOMS {n}: {axioms}"
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in {n}: {ax}"
  Lean.logInfo "TRANSPORT_CORE_COMPLETE"
