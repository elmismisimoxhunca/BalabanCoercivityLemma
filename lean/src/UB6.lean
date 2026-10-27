import UB5
import MA3

/-!
# UB6 -- U1 summed: covariant unit curl of `B` against the fine covariant curl of `y`, per-plaquette charts (lane m2_unit_20261014)

For a finite set `Qs` of good unit plaquettes (box inside `Ω_k`), each with its own chart (`ChartOK`, ONE gauge per plaquette,
uniform constants `s, κ, ε`):
  `n Σ_{q∈Qs} ‖curl_W B q‖² ≤ (1+ε')(2 Xbox + 64 (s/n)² ‖y‖²) + (1+1/ε')(64 κ² n ‖B‖² + 8 n⁻² δ² · 7776 ‖y‖²)`,
`Xbox = Σ_{p ∈ plaqIn Ω_k} ‖curl_U y p‖²`, `δ = delLoc ℓ ε k`, `n = ℓ^k`, `Q_U y = τ* B`.
Constants: `7776 = 4 · 3 · 648`: four bond positions, each hit by `≤ 3` plaquettes, footprint multiplicity `≤ 3·6³ = 648`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.M2Unit

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice blockOf mem_CoarseLattice)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.StatementLaneR8
open AdalyFormal.DLayer (Foot bondRestr Reach)
open AdalyFormal.GenuineU1 (plaqE)
open AdalyFormal.FlatEllGeneral (InBox)
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.TowerLoc (delLoc)

/-! ## multiplicities -/

theorem card_dirs : Fintype.card PeriodicPlaquetteDirections = 3 := by decide

/-- a plaquette-to-bond position map that is injective together with the plane hits each bond at most 3 times. -/
theorem sum_pos_le {L : PeriodicLatticeExtent} (φ : PeriodicLatticePlaquette L → Bond L)
    (hφ : ∀ q q' : PeriodicLatticePlaquette L, φ q = φ q' → q.2 = q'.2 → q = q')
    (g : Bond L → ℝ) (hg : ∀ b, 0 ≤ g b) (Qs : Finset (PeriodicLatticePlaquette L)) :
    ∑ q ∈ Qs, g (φ q) ≤ 3 * ∑ b : Bond L, g b := by
  classical
  set ψ : PeriodicLatticePlaquette L → Bond L × PeriodicPlaquetteDirections := fun q => (φ q, q.2) with hψ
  have hinj : Set.InjOn ψ Qs := by
    intro q _ q' _ h
    have h' : (φ q, q.2) = (φ q', q'.2) := h
    exact hφ q q' (Prod.ext_iff.mp h').1 (Prod.ext_iff.mp h').2
  have h1 : ∑ q ∈ Qs, g (φ q) = ∑ t ∈ Qs.image ψ, g t.1 := (Finset.sum_image (f := fun t => g t.1) hinj).symm
  have h2 : ∑ t ∈ Qs.image ψ, g t.1 ≤ ∑ t : Bond L × PeriodicPlaquetteDirections, g t.1 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun t _ _ => hg _)
  have h3 : ∑ t : Bond L × PeriodicPlaquetteDirections, g t.1 = 3 * ∑ b : Bond L, g b := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, card_dirs, nsmul_eq_mul]
    rw [Finset.mul_sum]; push_cast; ring_nf
  linarith

theorem shift_inj {L : PeriodicLatticeExtent} {x x' : PeriodicLatticeSite L} {μ : Fin 3}
    (h : periodicLatticeShift x μ = periodicLatticeShift x' μ) : x = x' :=
  AdalyFormal.Balaban.QOne.periodicLatticeShift_injective μ h

theorem qb_inj1 {L : PeriodicLatticeExtent} (q q' : PeriodicLatticePlaquette L) (h : qb1 q = qb1 q') (h2 : q.2 = q'.2) :
    q = q' := by
  have h1 : (q.1, q.2.1.1) = (q'.1, q'.2.1.1) := h
  exact Prod.ext (Prod.ext_iff.mp h1).1 h2
theorem qb_inj4 {L : PeriodicLatticeExtent} (q q' : PeriodicLatticePlaquette L) (h : qb4 q = qb4 q') (h2 : q.2 = q'.2) :
    q = q' := by
  have h1 : (q.1, q.2.1.2) = (q'.1, q'.2.1.2) := h
  exact Prod.ext (Prod.ext_iff.mp h1).1 h2
theorem qb_inj2 {L : PeriodicLatticeExtent} (q q' : PeriodicLatticePlaquette L) (h : qb2 q = qb2 q') (h2 : q.2 = q'.2) :
    q = q' := by
  have h0 : (periodicLatticeShift q.1 q.2.1.1, q.2.1.2) = (periodicLatticeShift q'.1 q'.2.1.1, q'.2.1.2) := h
  have h1 : periodicLatticeShift q.1 q.2.1.1 = periodicLatticeShift q'.1 q'.2.1.1 := (Prod.ext_iff.mp h0).1
  rw [h2] at h1
  exact Prod.ext (shift_inj h1) h2
theorem qb_inj3 {L : PeriodicLatticeExtent} (q q' : PeriodicLatticePlaquette L) (h : qb3 q = qb3 q') (h2 : q.2 = q'.2) :
    q = q' := by
  have h0 : (periodicLatticeShift q.1 q.2.1.2, q.2.1.1) = (periodicLatticeShift q'.1 q'.2.1.2, q'.2.1.1) := h
  have h1 : periodicLatticeShift q.1 q.2.1.2 = periodicLatticeShift q'.1 q'.2.1.2 := (Prod.ext_iff.mp h0).1
  rw [h2] at h1
  exact Prod.ext (shift_inj h1) h2

open Classical in
/-- footprint multiplicity over unit bonds: `Σ_b ‖y|Foot(row b)‖² ≤ 648 ‖y‖²`. -/
theorem sum_footT_le {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell2 : 2 ≤ ell) (y : BondFnL2 (scaleUp ell k Lu)) :
    ∑ b : Bond Lu, footT (by omega) y b ≤ 648 * ‖y‖ ^ 2 := by
  have hell : 0 < ell := by omega
  set n := ell ^ k with hn
  have hn0 : 0 < n := pow_pos hell k
  have hexp : ∀ b : Bond Lu, footT hell y b
      = ∑ e : Bond (scaleUp ell k Lu), (if Foot ell k (unitBondEmb ell k Lu hell b) e then ‖y e‖ ^ 2 else 0) := by
    intro b
    unfold footT
    rw [PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    simp only [bondRestr, PiLp.toLp_apply]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun b _ => hexp b), Finset.sum_comm]
  have hcount : ∀ e : Bond (scaleUp ell k Lu),
      ((Finset.univ.filter (fun b : Bond Lu => Foot ell k (unitBondEmb ell k Lu hell b) e)).card : ℝ) ≤ 648 := by
    intro e
    have h1 : (Finset.univ.filter (fun b : Bond Lu => Foot ell k (unitBondEmb ell k Lu hell b) e)).card
        ≤ (Finset.univ.filter (fun y : PeriodicLatticeSite (scaleUp ell k Lu) =>
            (∀ ν, n ∣ (y ν).val) ∧ Reach (AdalyFormal.DLayer.Rfoot ell k) y e.1)).card * 3 := by
      have hsub : (Finset.univ.filter (fun b : Bond Lu => Foot ell k (unitBondEmb ell k Lu hell b) e)).image
          (fun b => (embY ell k Lu hell b.1, b.2)) ⊆
          (Finset.univ.filter (fun y : PeriodicLatticeSite (scaleUp ell k Lu) =>
            (∀ ν, n ∣ (y ν).val) ∧ Reach (AdalyFormal.DLayer.Rfoot ell k) y e.1)) ×ˢ (Finset.univ : Finset (Fin 3)) := by
        intro t ht
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ht
        have hb' := (Finset.mem_filter.mp hb).2
        simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
        refine ⟨fun ν => Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp
          (AdalyFormal.GenuineU1.embY_mem_CL ell k Lu hell b.1) ν), ?_⟩
        exact AdalyFormal.DLayer.Foot_reach ell hell k _ e hb'
      have hinj : Set.InjOn (fun b : Bond Lu => (embY ell k Lu hell b.1, b.2))
          ↑(Finset.univ.filter (fun b : Bond Lu => Foot ell k (unitBondEmb ell k Lu hell b) e)) := by
        intro b _ b' _ h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (AdalyFormal.IngredientFamilyR2.embY_injective ell k Lu hell h.1) h.2
      have := Finset.card_le_card hsub
      rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_univ, Fintype.card_fin] at this
      exact this
    have h2 := AdalyFormal.DLayer.card_reach_coarse_le n hn0
      (fun ν => AdalyFormal.BondComposite.hdvd_scaleUp ell k Lu hell k le_rfl ν) (AdalyFormal.DLayer.Rfoot ell k) e.1
    have h3 : AdalyFormal.DLayer.Rfoot ell k / n ≤ 5 := by
      rw [Nat.div_le_iff_le_mul_add_pred hn0]
      have := AdalyFormal.DLayer.Rfoot_le ell hell2 k
      nlinarith
    have h4 : (AdalyFormal.DLayer.Rfoot ell k / n + 1) ^ 3 ≤ 216 := by
      have : AdalyFormal.DLayer.Rfoot ell k / n + 1 ≤ 6 := by omega
      calc (AdalyFormal.DLayer.Rfoot ell k / n + 1) ^ 3 ≤ 6 ^ 3 := Nat.pow_le_pow_left this 3
        _ = 216 := by norm_num
    have h5 : (Finset.univ.filter (fun b : Bond Lu => Foot ell k (unitBondEmb ell k Lu hell b) e)).card ≤ 648 := by
      calc _ ≤ _ := h1
        _ ≤ (AdalyFormal.DLayer.Rfoot ell k / n + 1) ^ 3 * 3 := Nat.mul_le_mul_right 3 h2
        _ ≤ 216 * 3 := Nat.mul_le_mul_right 3 h4
        _ = 648 := by norm_num
    exact_mod_cast h5
  have hrw : ∀ e : Bond (scaleUp ell k Lu),
      ∑ b : Bond Lu, (if Foot ell k (unitBondEmb ell k Lu hell b) e then ‖y e‖ ^ 2 else 0)
        = ((Finset.univ.filter (fun b : Bond Lu => Foot ell k (unitBondEmb ell k Lu hell b) e)).card : ℝ) * ‖y e‖ ^ 2 := by
    intro e
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl (fun e _ => hrw e), PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  exact Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_right (hcount e) (sq_nonneg _))

end AdalyFormal.M2Unit

#print axioms AdalyFormal.M2Unit.sum_pos_le
#print axioms AdalyFormal.M2Unit.sum_footT_le
