import R7Fork.DM13h
import R7Fork.DM11

/-!
# DM13i -- THE KERNEL OF THE FORM OF `G1inv` IS TRIVIAL at every flat admissible tower (hence `IsUnit G1inv`).
Assembly: kernel => (Q A = 0, closed zero-extension) => Hodge `A = grad phi + c` => the adjacency induction (DM13f-h) gives `c = 0` and constant stratum means
=> `phi - s in N(Q')` => `R` fixes `lapDir (phi - s)` => `grad phi = 0`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 64000000
namespace AdalyFormal.DirichletMono

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp Tower Admissible bigSide BlockClosed)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GenuineU1
open AdalyFormal.GenuineU1H (constBond constSite hodge_K2 gradL2_flat_apply gradL2_flat_constSite)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice card_blockOf_of_coarse)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantCLM_L2_toLp)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.QjComposite (Qcomposite)

/-- pointwise formula of the flat covariant curl -/
theorem curl_apply_flat {L : PeriodicLatticeExtent} (x : BondFnL2 L) (p : PeriodicLatticePlaquette L) :
    (curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) x) p
      = flatCurlValue (WithLp.ofLp x) p := by
  have hx : x = WithLp.toLp 2 (WithLp.ofLp x) := rfl
  rw [hx, curlCovariantCLM_L2_toLp]
  have hc : AdalyFormal.Balaban.CovariantOperators.curlCovariantLM (trivialU L) (WithLp.ofLp (WithLp.toLp 2 (WithLp.ofLp x)))
      = flatCurlValue (WithLp.ofLp x) := by
    rw [AdalyFormal.Balaban.CovU1Reduction.curlCovariantLM_trivialU_eq_flatCurlLM]; rfl
  exact congrFun hc p

/-- a kernel element vanishes on every bond without an end-point in `Om_1` -/
theorem A_zero_off_Om1 (P : IngrBParams) (hU : P.U = flatCfg) {M R : ℕ} (hS : Admissible P.ell M R P.k P.S)
    (A : ↥(bondSupp P.G)) (hQ : P.data.Q A = 0) (e : Bond (scaleUp P.ell P.k P.Lu))
    (h1 : e.1 ∉ P.S.Om 1) (h2 : periodicLatticeShift e.1 e.2 ∉ P.S.Om 1) : (WithLp.ofLp (iE P.G A)) e = 0 := by
  by_cases heE : e ∈ bondsOm0 P.G
  · have h0 : e ∈ bondsLam P.G 0 := by
      refine ⟨?_, ?_⟩
      · rcases heE with h | h
        · exact Or.inl ⟨fun μ => by simp, h, h1⟩
        · refine Or.inr ?_
          have : coarseShift e.1 (P.G.ell ^ 0) e.2 = periodicLatticeShift e.1 e.2 := by simp [coarseShift]
          rw [this]
          exact ⟨fun μ => by simp, h, h2⟩
      · rintro (h | h)
        · exact h1 (mem_of_omGe P.hell hS h)
        · have hm := mem_of_omGe P.hell hS h
          have hsh : coarseShift e.1 (P.G.ell ^ 0) e.2 = periodicLatticeShift e.1 e.2 := by simp [coarseShift]
          rw [hsh] at hm
          exact h2 hm
    have := congrArg (fun F => (WithLp.ofLp F) (⟨⟨0, Nat.succ_pos _⟩, ⟨e, h0⟩⟩ : BIdx P.G)) hQ
    simp only [PiLp.zero_apply] at this
    rw [show (P.data.Q A) ⟨⟨0, Nat.succ_pos _⟩, ⟨e, h0⟩⟩ = _ from
      Qfull_row P hU (iE P.G A) ⟨0, Nat.succ_pos _⟩ e h0] at this
    exact (lcr_one_eq (WithLp.ofLp (iE P.G A)) _).symm.trans this
  · exact A.2 e heE

/-- **the kernel of the form is trivial** -/
theorem G1inv_kernel_trivial (P : IngrBParams) (hU : P.U = flatCfg) {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) (hRM : 3 ≤ R * M) (ha : 0 < P.a) (hu : ∀ μ, 1 ≤ P.Lu μ)
    (A : ↥(bondSupp P.G)) (hq : ⟪A, P.G1inv A⟫ = 0) : A = 0 := by
  classical
  obtain ⟨hQ, -, hcl⟩ := kernel_extension_closed P hU hS hRM ha hu A hq
  -- the gauge part of the form vanishes as well
  have hT : Tfull P.G P.U (iE P.G A) = 0 := by
    have hform := G1inv_form_gen P hU A
    rw [hq] at hform
    have h1 := sq_nonneg ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn P.G.Om0)
          (curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
            (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp P.ell P.k P.Lu)) (iE P.G A))‖
    have h2 := sq_nonneg ‖Tfull P.G P.U (iE P.G A)‖
    have h3 := mass_nonneg_gen P ha.le A
    have : ‖Tfull P.G P.U (iE P.G A)‖ ^ 2 = 0 := by linarith
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  -- Hodge
  have hcurl0 : curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp P.ell P.k P.Lu)) (iE P.G A) = 0 := by
    refine PiLp.ext (fun p => ?_)
    rw [curl_apply_flat]
    exact hcl p
  obtain ⟨φ, c, hAφ⟩ := hodge_K2 (iE P.G A) hcurl0
  have hAfun : ∀ e : Bond (scaleUp P.ell P.k P.Lu), (WithLp.ofLp (iE P.G A)) e
      = (WithLp.ofLp φ) (periodicLatticeShift e.1 e.2) - (WithLp.ofLp φ) e.1 + c e.2 := by
    intro e
    rw [hAφ]
    show (gradL2 flatCfg φ + constBond (scaleUp P.ell P.k P.Lu) c) e = _
    rw [PiLp.add_apply, gradL2_flat_apply]
    rfl
  -- the adjacency hypotheses
  have hN := scaleUp_ge_one P.ell P.k P.Lu P.hell hu
  have hell := P.hell
  have hAdj : AdjHyp P.ell M R P.k (scaleUp P.ell P.k P.Lu) P.S (WithLp.ofLp φ) c := by
    refine ⟨hell, hS, hN, ?_, ?_, ?_⟩
    · intro j hj ν
      have h := scaleUp_succ P.ell P.k P.Lu hell ν
      have h2 : 2 ≤ P.Lu ν + 1 := by have := hu ν; omega
      have h3 : P.ell ^ j ≤ P.ell ^ P.k := Nat.pow_le_pow_right hell hj
      rw [h]
      nlinarith [Nat.mul_le_mul h2 h3]
    · intro u μ hu1 hv1
      have h0 := A_zero_off_Om1 P hU hS A hQ (u, μ) hu1 hv1
      rw [hAfun] at h0
      exact h0
    · intro m hm hmk p hp μ hpm hp1 hq1
      -- the bond (p, mu) is a level-m bond of frakB
      have hdvdp : ∀ ρ, P.ell ^ m ∣ (p ρ).val := fun ρ => Nat.dvd_of_mod_eq_zero ((mem_CoarseLattice.mp hp) ρ)
      have hb : ((p, μ) : Bond (scaleUp P.ell P.k P.Lu)) ∈ bondsLam P.G m := by
        refine ⟨?_, ?_⟩
        · rcases hpm with h | h
          · exact Or.inl ⟨hdvdp, h, hp1⟩
          · refine Or.inr ?_
            have hdq : ∀ ρ, P.ell ^ m ∣ ((coarseShift p (P.ell ^ m) μ) ρ).val := fun ρ =>
              Nat.dvd_of_mod_eq_zero ((mem_CoarseLattice.mp
                (AdalyFormal.Balaban.CoarseCurl.coarseShift_mem_coarseLattice (level_dvd hS hmk) hp μ)) ρ)
            exact ⟨hdq, h, hq1⟩
        · rintro (h | h)
          · exact hp1 (mem_of_omGe P.hell hS h)
          · exact hq1 (mem_of_omGe P.hell hS h)
      have hrow := Qfull_row P hU (iE P.G A) ⟨m, Nat.lt_succ_of_le hmk⟩ (p, μ) hb
      have hz : (P.data.Q A) ⟨⟨m, Nat.lt_succ_of_le hmk⟩, ⟨(p, μ), hb⟩⟩ = 0 := by
        rw [hQ]; rfl
      have hz2 := hrow.symm.trans hz
      have hfun : WithLp.ofLp (iE P.G A) = (fun b : Bond (scaleUp P.ell P.k P.Lu) =>
          (WithLp.ofLp φ (periodicLatticeShift b.1 b.2) - WithLp.ofLp φ b.1)) + (fun b => c b.2) := by
        funext b; rw [hAfun b]; simp [Pi.add_apply]
      have hn : 0 < P.ell ^ m := pow_pos hell m
      have hdvdm : ∀ ν, P.ell ^ m ∣ scaleUp P.ell P.k P.Lu ν + 1 := level_dvd hS hmk
      change lineCoarseRestrictSuTwo (P.ell ^ m) (WithLp.ofLp (iE P.G A)) (⟨p, hp⟩, μ) = 0 at hz2
      rw [hfun, LCR_add, LCR_grad (P.ell ^ m) hn hdvdm (WithLp.ofLp φ) p hp μ,
        LCR_const (P.ell ^ m) hn hdvdm c p hp μ] at hz2
      simpa using hz2
  -- constants vanish, the stratum means are constant
  have hc0 : c = 0 := funext (c_zero hAdj)
  set s : SuTwo := meanB P.ell P.S (Theta (WithLp.ofLp φ) c) (origin (scaleUp P.ell P.k P.Lu)) with hs
  have hTh : ∀ w, Theta (WithLp.ofLp φ) c w = WithLp.ofLp φ w := by
    intro w; unfold Theta; rw [hc0]; simp
  have hmean : ∀ x, meanB P.ell P.S (WithLp.ofLp φ) x = s := by
    intro x
    have := meanB_const hAdj x
    have e : meanB P.ell P.S (Theta (WithLp.ofLp φ) c) = meanB P.ell P.S (WithLp.ofLp φ) := by
      funext y; unfold meanB; simp only [hTh]
    rw [e] at this
    rw [this, hs, e]
  -- the potential `phi' = phi - s`
  set φ' : SiteL2 (scaleUp P.ell P.k P.Lu) := φ - constSite (scaleUp P.ell P.k P.Lu) s with hφ'
  have hφ'x : ∀ x, WithLp.ofLp φ' x = WithLp.ofLp φ x - s := fun x => rfl
  have hbg : ∀ j, bgTower P.G P.U j = trivialU (scaleUp P.ell P.k P.Lu) := fun j => by
    rw [bgTower_flat P hU j]; rfl
  have hmem : φ' ∈ NQp P.G P.U := by
    refine ⟨?_, ?_⟩
    · intro x hx
      have hx0 : x ∉ P.S.Om 0 := hx
      have hlev0 : lev P.S x = 0 := by
        refine isLev_unique hS.1 (lev_spec hS x) ⟨Nat.zero_le _, Or.inl rfl, ?_⟩
        exact fun h => hx0 (hS.1 0 h)
      have := hmean x
      rw [meanB_zero P.S _ hlev0] at this
      rw [hφ'x, this, sub_self]
    · intro j hj y hy
      have hy' : y ∈ P.S.Om j ∧ y ∉ P.S.Om (j + 1) := ⟨hy.2.1, hy.2.2⟩
      have hyc : y ∈ CoarseLattice (scaleUp P.ell P.k P.Lu) (P.ell ^ j) := by
        rw [mem_CoarseLattice]; intro ρ; exact Nat.mod_eq_zero_of_dvd (hy.1 ρ)
      have hn : 0 < P.ell ^ j := pow_pos hell j
      have hlevy : lev P.S y = j := by
        refine isLev_unique hS.1 (lev_spec hS y) ⟨hj, ?_, hy'.2⟩
        rcases Nat.eq_zero_or_pos j with h0 | hpos
        · exact Or.inl h0
        · exact Or.inr hy'.1
      have hmy := hmean y
      have hancy : anc (P.ell ^ j) y = y := anc_eq_of_mem hn hyc (self_mem_block hn hyc)
      unfold meanB stBlock at hmy
      rw [hlevy, hancy] at hmy
      have hcard : (blockOf y (P.ell ^ j)).card = (P.ell ^ j) ^ 3 := card_blockOf_of_coarse (level_dvd hS hj) hyc
      rw [Qlev_apply]
      have hq := Qcomposite_closed P.ell hell (bgTower P.G P.U) hbg P.k (scaleUp_tiling P.ell P.k P.Lu hell)
        (WithLp.ofLp φ') j hj (P.ell ^ j) rfl y hyc
      refine hq.trans ?_
      simp only [hφ'x, Finset.sum_sub_distrib, Finset.sum_const, hcard]
      have hn3 : ((P.ell ^ j : ℕ) : ℝ) ^ 3 ≠ 0 := by positivity
      have h1 : ∑ x ∈ blockOf y (P.ell ^ j), WithLp.ofLp φ x = ((P.ell ^ j : ℕ) : ℝ) ^ 3 • s := by
        have := congrArg (fun v => (((P.ell ^ j : ℕ) : ℝ) ^ 3) • v) hmy
        simp only [smul_smul] at this
        have e : ((P.ell ^ j : ℕ) : ℝ) ^ 3 * (1 / ((P.ell ^ j : ℕ) : ℝ) ^ 3) = 1 := by field_simp
        rw [e, one_smul] at this
        exact this
      rw [h1, ← Nat.cast_smul_eq_nsmul ℝ]
      push_cast; simp
  -- R fixes lapDir phi'
  have hlap : lapDir P.G P.U φ' ∈ RImage P.G P.U := Submodule.mem_map.mpr ⟨φ', hmem, rfl⟩
  have hR : Rproj P.G P.U (lapDir P.G P.U φ') = lapDir P.G P.U φ' :=
    Submodule.starProjection_eq_self_iff.mpr hlap
  set u : SiteL2 (scaleUp P.ell P.k P.Lu) := gradAdj P.U (iE P.G A) with hu_def
  have hconst : gradL2 flatCfg (constSite (scaleUp P.ell P.k P.Lu) s) = 0 := gradL2_flat_constSite s
  have hgrad : gradL2 flatCfg φ' = gradL2 flatCfg φ := by rw [hφ', map_sub, hconst, sub_zero]
  have hAφ0 : iE P.G A = gradL2 flatCfg φ := by
    rw [hAφ, hc0]
    have : constBond (scaleUp P.ell P.k P.Lu) (0 : Fin 3 → SuTwo) = 0 := by ext b; rfl
    rw [this, add_zero]
  have hlapφ' : lapFull flatCfg φ' = u := by
    rw [hu_def, hU, hAφ0, ← hgrad]; rfl
  have hφ'supp : siteMask P.G.Om0 φ' = φ' := by
    ext x
    rw [siteMask_apply]
    split_ifs with hx
    · rfl
    · have hx0 : x ∉ P.S.Om 0 := hx
      have := hmem.1 x hx0
      rw [this]
  have hlapDir : lapDir P.G P.U φ' = siteMask P.G.Om0 u := by
    unfold lapDir
    simp only [ContinuousLinearMap.comp_apply]
    rw [hφ'supp, hU, hlapφ']
  -- T A = R u = 0  =>  <u, lapDir phi'> = 0
  have hRu : Rproj P.G P.U u = 0 := by
    have : Tfull P.G P.U (iE P.G A) = Rproj P.G P.U u := rfl
    rw [← this]; exact hT
  have horth : ⟪u, lapDir P.G P.U φ'⟫ = 0 := by
    calc ⟪u, lapDir P.G P.U φ'⟫ = ⟪u, Rproj P.G P.U (lapDir P.G P.U φ')⟫ := by rw [hR]
      _ = ⟪Rproj P.G P.U u, lapDir P.G P.U φ'⟫ := by rw [real_inner_comm, Rproj_symm, real_inner_comm]
      _ = 0 := by rw [hRu, inner_zero_left]
  rw [hlapDir] at horth
  have hmask : ⟪u, siteMask P.G.Om0 u⟫ = ‖siteMask P.G.Om0 u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, siteMask_symm, siteMask_idem]
  have hm0 : siteMask P.G.Om0 u = 0 := by
    have : ‖siteMask P.G.Om0 u‖ ^ 2 = 0 := by rw [← hmask]; exact horth
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  have hg0 : ‖gradL2 flatCfg φ'‖ ^ 2 = 0 := by
    rw [← inner_lapFull, hlapφ']
    calc ⟪φ', u⟫ = ⟪siteMask P.G.Om0 φ', u⟫ := by rw [hφ'supp]
      _ = ⟪φ', siteMask P.G.Om0 u⟫ := siteMask_symm _ _ _
      _ = 0 := by rw [hm0, inner_zero_right]
  have hg1 : gradL2 flatCfg φ' = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hg0)
  apply Subtype.ext
  show iE P.G A = 0
  rw [hAφ0, ← hgrad]
  exact hg1

#print axioms G1inv_kernel_trivial

/-- **`IsUnit G1inv` at every flat admissible tower** -/
theorem isUnit_G1inv_proper (P : IngrBParams) (hU : P.U = flatCfg) {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) (hRM : 3 ≤ R * M) (ha : 0 < P.a) (hu : ∀ μ, 1 ≤ P.Lu μ) :
    IsUnit P.G1inv := by
  have hinj : Function.Injective ((P.G1inv : ↥(bondSupp P.G) →L[ℝ] ↥(bondSupp P.G)) :
      ↥(bondSupp P.G) →ₗ[ℝ] ↥(bondSupp P.G)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    refine G1inv_kernel_trivial P hU hS hRM ha hu x ?_
    have : P.G1inv x = 0 := hx
    rw [this, inner_zero_right]
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr ⟨hinj, (LinearMap.injective_iff_surjective).mp hinj⟩

#print axioms isUnit_G1inv_proper

end AdalyFormal.DirichletMono
