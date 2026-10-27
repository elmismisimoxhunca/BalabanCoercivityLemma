import R7Fork.DM10

/-!
# DM11 -- STRUCTURE OF A KERNEL ELEMENT of the form of `G1inv` at a flat admissible tower (partial progress on `IsUnit G1inv`; NOT a proof of it):
**[SUPERSEDED IN PLACE (S75, 2026-10-10): this partial structure is the first step of `DM13i.G1inv_kernel_trivial`, which proves `IsUnit G1inv` (`isUnit_G1inv_proper`).]**
if `<A, G1inv A> = 0` for `A in E_0` then (i) `Q A = 0` on all of `frakB`, (ii) `chi_{plaqIn} curl A = 0`, and (iii) the zero extension of `A` is a CLOSED 1-form of the
WHOLE torus (every plaquette outside `plaqIn Omega_0` has all four bonds in `frakB_0`, where `Q_0 = id` kills `A`), supported on bonds touching `Omega_1`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
namespace AdalyFormal.DirichletMono

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp Tower Admissible)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)
open AdalyFormal.Balaban.QOne (pathSite)

theorem lcr_one_eq {L : PeriodicLatticeExtent} (A : Bond L → SuTwo) (c : CoarseBond L 1) :
    lineCoarseRestrictSuTwo 1 A c = A (c.1.1, c.2) := by
  unfold lineCoarseRestrictSuTwo
  rw [AdalyFormal.Balaban.FourierFaithfulU1.blockOf_one]
  simp [pathSite]

/-- `OmGe i x  =>  x in Om_i` (under `Admissible`) -/
theorem mem_of_omGe {ell M R k : ℕ} (hell : 0 < ell) {L : PeriodicLatticeExtent} {S : Tower L}
    (hS : Admissible ell M R k S) {i : ℕ} {x : PeriodicLatticeSite L}
    (h : OmGe (geomOf ell k S) i x) : x ∈ S.Om i := by
  obtain ⟨i', hii', hik, y, hy, hb⟩ := h
  have hx : x ∈ S.Om i' :=
    block_sub_Om hell hS hik (fun ρ => hy.1 ρ) hy.2.1 (mem_blockOf.mpr hb)
  exact om_anti S hS.1 hii' hx

theorem plaq_bond_endpoints_inBox {L : PeriodicLatticeExtent} (p : PeriodicLatticePlaquette L)
    (e : PeriodicLatticeEdge L) (he : e ∈ periodicPlaquetteBoundaryEdges p) :
    InBox p.1 e.1 ∧ InBox p.1 (periodicLatticeShift e.1 e.2) := by
  have hμν : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact ⟨self_inBox _, shift_inBox _ _⟩
  · exact ⟨shift_inBox _ _, shift_shift_inBox _ _ _ hμν⟩
  · exact ⟨shift_inBox _ _, shift_shift_inBox _ _ _ (Ne.symm hμν)⟩
  · exact ⟨self_inBox _, shift_inBox _ _⟩

theorem kernel_extension_closed (P : IngrBParams) (hU : P.U = flatCfg) {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) (hRM : 3 ≤ R * M) (ha : 0 < P.a)
    (hu : ∀ μ, 1 ≤ P.Lu μ) (A : ↥(bondSupp P.G)) (hq : ⟪A, P.G1inv A⟫ = 0) :
    P.data.Q A = 0 ∧ (∀ p : PeriodicLatticePlaquette (scaleUp P.ell P.k P.Lu), p ∈ plaqIn (P.S.Om 0) →
      flatCurlValue (WithLp.ofLp (iE P.G A)) p = 0) ∧
    ∀ p : PeriodicLatticePlaquette (scaleUp P.ell P.k P.Lu), flatCurlValue (WithLp.ofLp (iE P.G A)) p = 0 := by
  classical
  have hform := G1inv_form_gen P hU A
  rw [hq] at hform
  have h1 := sq_nonneg ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn P.G.Om0)
          (AdalyFormal.Balaban.DeltaKFull.curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
            (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp P.ell P.k P.Lu)) (iE P.G A))‖
  have h2 := sq_nonneg ‖Tfull P.G P.U (iE P.G A)‖
  have h3 := mass_nonneg_gen P ha.le A
  have e1 : ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn P.G.Om0)
          (AdalyFormal.Balaban.DeltaKFull.curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
            (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp P.ell P.k P.Lu)) (iE P.G A))‖ ^ 2 = 0 := by linarith
  have e3 : ⟪A, P.data.Mass A⟫ = 0 := by linarith
  -- (i) Q A = 0
  have hQ : P.data.Q A = 0 := by
    rw [mass_inner_gen] at e3
    refine PiLp.ext (fun β => ?_)
    have hnn : ∀ p ∈ (Finset.univ : Finset (BIdx P.G)),
        0 ≤ P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.data.Q A p‖ ^ 2 :=
      fun p _ => mul_nonneg (mul_nonneg ha.le (by positivity)) (sq_nonneg _)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp e3 β (Finset.mem_univ _)
    have hpos : 0 < P.a * (P.ell : ℝ) ^ (β.1 : ℕ) := by
      have : (0 : ℝ) < P.ell := by exact_mod_cast P.hell
      positivity
    have h0 : ‖P.data.Q A β‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hpos.ne'
      · exact h
    simpa using h0
  -- (ii) curl vanishes on plaqIn
  have hcurl : ∀ p : PeriodicLatticePlaquette (scaleUp P.ell P.k P.Lu), p ∈ plaqIn (P.S.Om 0) →
      flatCurlValue (WithLp.ofLp (iE P.G A)) p = 0 := by
    intro p hp
    have := masked_curl_norm_sq (plaqIn P.G.Om0) (iE P.G A)
    rw [e1] at this
    have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => sq_nonneg ‖flatCurlValue (WithLp.ofLp (iE P.G A)) q‖)).mp
      this.symm p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hs)
  refine ⟨hQ, hcurl, fun p => ?_⟩
  by_cases hp : p ∈ plaqIn (P.S.Om 0)
  · exact hcurl p hp
  · -- a corner outside Omega_0
    have hN := scaleUp_ge_one P.ell P.k P.Lu P.hell hu
    obtain ⟨e0, he0, hbad⟩ : ∃ e0 ∈ periodicPlaquetteBoundaryEdges p,
        ¬ (e0.1 ∈ P.S.Om 0 ∧ periodicLatticeShift e0.1 e0.2 ∈ P.S.Om 0) := by
      by_contra h
      push_neg at h
      exact hp (fun e he => h e he)
    obtain ⟨z, hzbox, hz⟩ : ∃ z, InBox p.1 z ∧ z ∉ P.S.Om 0 := by
      have hb := plaq_bond_endpoints_inBox p e0 he0
      by_cases h1 : e0.1 ∈ P.S.Om 0
      · exact ⟨_, hb.2, fun h2 => hbad ⟨h1, h2⟩⟩
      · exact ⟨_, hb.1, h1⟩
    -- every end-point of every bond of p lies outside Omega_1
    have hout : ∀ c, InBox p.1 c → c ∉ P.S.Om 1 := by
      intro c hc hc1
      have := hS.2.2.2.2.1 0 (Nat.zero_le _) z hz c hc1
      have h3 := pdist_box_le hN hzbox hc
      unfold AdalyFormal.StatementLane.bigSide at this
      simp only [pow_zero, mul_one] at this
      omega
    have hbond : ∀ e ∈ periodicPlaquetteBoundaryEdges p, WithLp.ofLp (iE P.G A) e = 0 := by
      intro e he
      have hb := plaq_bond_endpoints_inBox p e he
      by_cases heE : e ∈ bondsOm0 P.G
      · -- e is a level-0 bond of frakB
        have h0 : e ∈ bondsLam P.G 0 := by
          have o1 := hout _ hb.1
          have o2 := hout _ hb.2
          refine ⟨?_, ?_⟩
          · rcases heE with h | h
            · exact Or.inl ⟨fun μ => by simp, h, o1⟩
            · refine Or.inr ?_
              have : coarseShift e.1 (P.G.ell ^ 0) e.2 = periodicLatticeShift e.1 e.2 := by
                simp [coarseShift]
              rw [this]
              exact ⟨fun μ => by simp, h, o2⟩
          · rintro (h | h)
            · exact o1 (mem_of_omGe P.hell hS h)
            · have hm := mem_of_omGe P.hell hS h
              have hsh : coarseShift e.1 (P.G.ell ^ 0) e.2 = periodicLatticeShift e.1 e.2 := by
                simp [coarseShift]
              rw [hsh] at hm
              exact o2 hm
        have := congrArg (fun F => (WithLp.ofLp F) (⟨⟨0, Nat.succ_pos _⟩, ⟨e, h0⟩⟩ : BIdx P.G)) hQ
        simp only [PiLp.zero_apply] at this
        rw [show (P.data.Q A) ⟨⟨0, Nat.succ_pos _⟩, ⟨e, h0⟩⟩ = _ from
          Qfull_row P hU (iE P.G A) ⟨0, Nat.succ_pos _⟩ e h0] at this
        exact (lcr_one_eq (WithLp.ofLp (iE P.G A)) _).symm.trans this
      · exact A.2 e heE
    unfold flatCurlValue
    have b1 := hbond (p.1, p.2.1.1) (by simp [periodicPlaquetteBoundaryEdges])
    have b2 := hbond (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) (by simp [periodicPlaquetteBoundaryEdges])
    have b3 := hbond (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) (by simp [periodicPlaquetteBoundaryEdges])
    have b4 := hbond (p.1, p.2.1.2) (by simp [periodicPlaquetteBoundaryEdges])
    simp only [b1, b2, b3, b4]; simp

#print axioms kernel_extension_closed

end AdalyFormal.DirichletMono
