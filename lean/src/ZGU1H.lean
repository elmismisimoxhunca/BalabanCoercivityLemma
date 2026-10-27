import ZGU1G

/-!
# GU1H -- KERNEL TRIVIALITY of the genuine flat form (all `k`):
`curl A = 0`, `R D* A = 0`, `Q_k A = 0`  ⟹  `A = 0`.
Route: discrete Hodge (hodge_K2: `A = ∇φ + const`), the gradient/constant calculus of GU1G,
the cycle sum killing the harmonic part, K3 on the unit torus, then `φ - mean ∈ N(Q')` so that
`R Δ φ' = Δ φ'` forces `∇φ' = 0`.   Standard axioms only (see the #print axioms lines).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.GenuineU1

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_CoarseLattice
  card_blockOf_of_coarse)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_val_eq coarseShift_apply_ne)
open AdalyFormal.Balaban.QjComposite (Qcomposite)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.GenuineU1H (constBond constSite hodge_K2 hodge_K3 hodge_converse gradL2_flat_apply)

theorem LCR_add {L : PeriodicLatticeExtent} (n : ℕ) (f g : Bond L → SuTwo)
    (b : CoarseBond L n) :
    lineCoarseRestrictSuTwo n (f + g) b = lineCoarseRestrictSuTwo n f b + lineCoarseRestrictSuTwo n g b := by
  unfold lineCoarseRestrictSuTwo
  simp only [Pi.add_apply, Finset.sum_add_distrib, smul_add]

/-- going once around the circle in direction `μ` returns to the start -/
theorem pathSite_period {L : PeriodicLatticeExtent} (y : PeriodicLatticeSite L) (μ : Fin 3) :
    pathSite y μ (L μ + 1) = y := by
  funext ν
  apply Fin.ext
  show ((coarseShift y (L μ + 1) μ) ν).val = (y ν).val
  by_cases h : ν = μ
  · subst h
    rw [coarseShift_val_eq]
    have := (y ν).isLt
    rw [Nat.add_comm (y ν).val, Nat.add_mod_left]
    exact Nat.mod_eq_of_lt this
  · rw [coarseShift_apply_ne y _ μ ν h]

theorem G_Om0 (ell k : ℕ) (Lu : PeriodicLatticeExtent) :
    (geomOf ell k (fullTower ell k Lu)).Om0 = Set.univ := by
  simp [geomOf, fullTower]

theorem siteMask_univ {L : PeriodicLatticeExtent} (f : SiteL2 L) :
    siteMask (Set.univ : Set (PeriodicLatticeSite L)) f = f := by
  ext x
  rw [siteMask_apply]
  simp

#print axioms pathSite_period
#print axioms G_Om0

/-- **KERNEL TRIVIALITY (flat, full tower, any `k`)** -/
theorem ker_trivial (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (hN : ∀ μ, 1 ≤ Lu μ)
    (A : BondFnL2 (scaleUp ell k Lu))
    (h1 : curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) A = 0)
    (h2 : Tfull (geomOf ell k (fullTower ell k Lu)) (flatCfg : PeriodicLinkConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) A = 0)
    (h3 : ∀ e : Bond Lu, lineCoarseRestrictSuTwo (ell ^ k) (WithLp.ofLp A) (bondsE ell k Lu hell e) = 0) :
    A = 0 := by
  classical
  set n : ℕ := ell ^ k with hn
  have hnpos : 0 < n := pow_pos hell k
  have hdvd : ∀ ν, n ∣ scaleUp ell k Lu ν + 1 := scaleUp_tiling ell k Lu hell
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
  obtain ⟨φ, c, hA⟩ := hodge_K2 A h1
  -- the block sums
  set Φ : PeriodicLatticeSite (scaleUp ell k Lu) → SuTwo :=
    fun z => ∑ x ∈ blockOf z n, WithLp.ofLp φ x with hΦ
  -- (*) the relation at every unit bond
  have hrel : ∀ (y : PeriodicLatticeSite Lu) (μ : Fin 3),
      (1 / (n : ℝ) ^ 4) • (Φ (coarseShift (embY ell k Lu hell y) n μ) - Φ (embY ell k Lu hell y)) + c μ = 0 := by
    intro y μ
    have h := h3 (y, μ)
    have hAf : WithLp.ofLp A = (fun b : Bond (scaleUp ell k Lu) =>
        WithLp.ofLp φ (periodicLatticeShift b.1 b.2) - WithLp.ofLp φ b.1) + (fun b : Bond (scaleUp ell k Lu) => c b.2) := by
      funext b
      rw [hA]
      show (gradL2 flatCfg φ + constBond (scaleUp ell k Lu) c) b = _
      rw [PiLp.add_apply, gradL2_flat_apply]
      rfl
    rw [hAf, LCR_add] at h
    have hz := embY_mem_CL ell k Lu hell y
    have e1 : bondsE ell k Lu hell (y, μ) = (⟨embY ell k Lu hell y, hz⟩, μ) := rfl
    rw [e1, LCR_grad n hnpos hdvd (WithLp.ofLp φ) _ hz μ, LCR_const n hnpos hdvd c _ hz μ] at h
    exact h
  -- Ψ on the unit torus and the cycle sum
  set Ψ : PeriodicLatticeSite Lu → SuTwo := fun y => Φ (embY ell k Lu hell y) with hΨ
  have hshift : ∀ (y : PeriodicLatticeSite Lu) (μ : Fin 3),
      Ψ (periodicLatticeShift y μ) = Ψ y - ((n : ℝ) ^ 4) • c μ := by
    intro y μ
    have h := hrel y μ
    rw [AdalyFormal.StatementLaneG.coarseShift_embY ell k Lu hell hN y μ] at h
    have h' : (1 / (n : ℝ) ^ 4) • (Ψ (periodicLatticeShift y μ) - Ψ y) = - c μ :=
      eq_neg_of_add_eq_zero_left h
    have h'' := congrArg (fun v => ((n : ℝ) ^ 4) • v) h'
    simp only [smul_smul] at h''
    have e : (n : ℝ) ^ 4 * (1 / (n : ℝ) ^ 4) = 1 := by field_simp
    rw [e, one_smul, smul_neg] at h''
    calc Ψ (periodicLatticeShift y μ) = (Ψ (periodicLatticeShift y μ) - Ψ y) + Ψ y := by abel
      _ = Ψ y - ((n : ℝ) ^ 4) • c μ := by rw [h'']; abel
  have hiter : ∀ (μ : Fin 3) (m : ℕ) (y : PeriodicLatticeSite Lu),
      Ψ (pathSite y μ m) = Ψ y - (((m : ℝ)) * (n : ℝ) ^ 4) • c μ := by
    intro μ m
    induction m with
    | zero => intro y; simp [pathSite_zero]
    | succ m ih =>
        intro y
        rw [pathSite_succ, hshift, ih]
        push_cast
        rw [add_mul, one_mul, add_smul]
        abel
  have hc0 : ∀ μ, c μ = 0 := by
    intro μ
    let y0 : PeriodicLatticeSite Lu := fun ν => ⟨0, Nat.succ_pos _⟩
    have h := hiter μ (Lu μ + 1) y0
    rw [pathSite_period] at h
    have h0 : (((Lu μ + 1 : ℕ) : ℝ) * (n : ℝ) ^ 4) • c μ = 0 := by
      have := sub_eq_self.mp h.symm
      exact this
    rcases smul_eq_zero.mp h0 with h1 | h1
    · exfalso
      have : (0 : ℝ) < ((Lu μ + 1 : ℕ) : ℝ) * (n : ℝ) ^ 4 := by positivity
      linarith
    · exact h1
  have hcf : c = 0 := funext hc0
  have hAφ : A = gradL2 flatCfg φ := by
    rw [hA, hcf]
    have : constBond (scaleUp ell k Lu) (0 : Fin 3 → SuTwo) = 0 := by
      ext b; rfl
    rw [this, add_zero]
  -- Ψ is constant: K3 on the unit torus
  have hΨinv : ∀ (y : PeriodicLatticeSite Lu) (μ : Fin 3), Ψ (periodicLatticeShift y μ) = Ψ y := by
    intro y μ; rw [hshift, hc0 μ]; simp
  obtain ⟨X, hX⟩ := hodge_K3 (WithLp.toLp 2 Ψ : SiteL2 Lu) (by
    refine PiLp.ext (fun b => ?_)
    rw [gradL2_flat_apply]
    show Ψ (periodicLatticeShift b.1 b.2) - Ψ b.1 = (0 : SuTwo)
    rw [hΨinv, sub_self])
  have hΦX : ∀ z ∈ CoarseLattice (scaleUp ell k Lu) n, Φ z = X := by
    intro z hz
    obtain ⟨y, hy⟩ := (coarse_k_iff_emb ell k Lu hell z).mp (fun μ =>
      Nat.dvd_of_mod_eq_zero ((mem_CoarseLattice.mp hz) μ))
    rw [hy]
    exact hX y
  -- the mean-subtracted potential
  set c0 : SuTwo := (1 / (n : ℝ) ^ 3) • X with hc0def
  set φ' : SiteL2 (scaleUp ell k Lu) := φ - constSite (scaleUp ell k Lu) c0 with hφ'
  have hφ'ker : ∀ z ∈ CoarseLattice (scaleUp ell k Lu) n,
      ∑ x ∈ blockOf z n, WithLp.ofLp φ' x = 0 := by
    intro z hz
    have : ∀ x, WithLp.ofLp φ' x = WithLp.ofLp φ x - c0 := fun x => rfl
    simp only [this, Finset.sum_sub_distrib, Finset.sum_const, card_blockOf_of_coarse hdvd hz]
    have h1 : (∑ x ∈ blockOf z n, WithLp.ofLp φ x) = X := hΦX z hz
    rw [h1, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    have : ((n ^ 3 : ℕ) : ℝ) * (1 / (n : ℝ) ^ 3) = 1 := by push_cast; field_simp
    rw [this, one_smul, sub_self]
  set G := geomOf ell k (fullTower ell k Lu) with hG
  have hbg : ∀ j, bgTower G (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) j
      = (trivialU (scaleUp ell k Lu)) := by
    intro j
    unfold bgTower
    exact Ubar_flat _ j
  have hmem : φ' ∈ NQp G flatCfg := by
    refine ⟨fun x hx => absurd (by rw [hG, G_Om0]; exact Set.mem_univ x) hx, ?_⟩
    intro j hj y hy
    by_cases hjk : j < k
    · exfalso
      have : G.Lam j = ∅ := fullTower_lam_lt ell k Lu j hjk
      rw [this] at hy
      exact hy
    · have hjk' : j = k := le_antisymm hj (not_lt.mp hjk)
      subst hjk'
      have hyc : y ∈ CoarseLattice (scaleUp ell j Lu) (ell ^ j) := by
        rw [mem_CoarseLattice]
        intro ν
        exact Nat.mod_eq_zero_of_dvd (((fullTower_lam_k ell j Lu y).mp hy) ν)
      rw [Qlev_apply]
      have hq := Qcomposite_closed ell hell (bgTower G flatCfg) hbg j (scaleUp_tiling ell j Lu hell)
        (WithLp.ofLp φ') j le_rfl (ell ^ j) rfl y hyc
      exact hq.trans (by rw [hφ'ker y hyc, smul_zero])
  -- R fixes `Δ φ'` because `φ' ∈ N(Q')`
  have hlap : lapFull flatCfg φ' ∈ RImage G flatCfg := by
    refine Submodule.mem_map.mpr ⟨φ', hmem, ?_⟩
    show lapDir G flatCfg φ' = lapFull flatCfg φ'
    unfold lapDir
    simp only [ContinuousLinearMap.comp_apply]
    rw [hG, G_Om0, siteMask_univ, siteMask_univ]
  have hR : Rproj G flatCfg (lapFull flatCfg φ') = lapFull flatCfg φ' :=
    Submodule.starProjection_eq_self_iff.mpr hlap
  -- the constant part is invisible to `D`
  have hconst : gradL2 flatCfg (constSite (scaleUp ell k Lu) c0) = 0 :=
    (hodge_converse (L := scaleUp ell k Lu) 0 c0).2.2
  have hgrad : gradL2 flatCfg φ' = gradL2 flatCfg φ := by
    rw [hφ', map_sub, hconst, sub_zero]
  have hlapeq : lapFull flatCfg φ' = gradAdj flatCfg A := by
    rw [hAφ, ← hgrad]; rfl
  have hT : Tfull G flatCfg A = lapFull flatCfg φ' := by
    show (Rproj G flatCfg).comp (gradAdj flatCfg) A = _
    rw [ContinuousLinearMap.comp_apply, ← hlapeq, hR]
  rw [hT] at h2
  have hn0 : ‖gradL2 flatCfg φ'‖ ^ 2 = 0 := by
    rw [← inner_lapFull, h2, inner_zero_right]
  have hg0 : gradL2 flatCfg φ' = 0 := by
    have : ‖gradL2 flatCfg φ'‖ = 0 := by
      have := pow_eq_zero_iff (two_ne_zero) |>.mp hn0
      exact this
    exact norm_eq_zero.mp this
  rw [hAφ, ← hgrad]
  exact hg0

#print axioms ker_trivial

end AdalyFormal.GenuineU1
