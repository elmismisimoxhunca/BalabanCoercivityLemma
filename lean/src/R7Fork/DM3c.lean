import R7Fork.DM3b

/-!
# DM3c -- local unit Stokes: `n * sum_q ||curl_unit Bf q||^2 <= sum_{p in plaqIn Om0} ||curl A p||^2`
for a fine field `A` whose level-`n` average reproduces the unit field `Bf` on every unit bond with both endpoints in `Om_k`, and `Bf` has
vanishing curl at every unit plaquette whose unit box is not contained in `Om_k`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.DirichletMono

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GenuineU1
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf)
open AdalyFormal.Balaban.CoarseCurl (coarseShift CoarsePlaquette)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)
open AdalyFormal.Balaban.ThirdLevelStokes (coarseCurlSuTwo)

/-- all four bonds of the plaquette with base `z` and its endpoints lie in the unit box of `z` -/
theorem shift_inBox {Lu : PeriodicLatticeExtent} (z : PeriodicLatticeSite Lu) (a : Fin 3) :
    InBox z (periodicLatticeShift z a) := by
  intro ρ
  rw [AdalyFormal.StatementLane2.shift_apply]
  by_cases h : ρ = a <;> simp [h]

theorem shift_shift_inBox {Lu : PeriodicLatticeExtent} (z : PeriodicLatticeSite Lu) (a b : Fin 3) (hab : a ≠ b) :
    InBox z (periodicLatticeShift (periodicLatticeShift z a) b) := by
  intro ρ
  rw [AdalyFormal.StatementLane2.shift_apply, AdalyFormal.StatementLane2.shift_apply]
  by_cases h1 : ρ = b
  · subst h1; simp [Ne.symm hab]
  · by_cases h2 : ρ = a
    · subst h2; simp [h1]
    · simp [h1, h2]

theorem self_inBox {Lu : PeriodicLatticeExtent} (z : PeriodicLatticeSite Lu) : InBox z z :=
  fun _ => Or.inl rfl

open Classical in
theorem local_unit_stokes {ell k : ℕ} (hell : 0 < ell) {Lu : PeriodicLatticeExtent} (hu : ∀ ρ, 1 ≤ Lu ρ)
    {M R : ℕ} {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S)
    (A : Bond (scaleUp ell k Lu) → SuTwo) (Bf : Bond Lu → SuTwo)
    (hQ : ∀ e : Bond Lu, embY ell k Lu hell e.1 ∈ S.Om k → embY ell k Lu hell (periodicLatticeShift e.1 e.2) ∈ S.Om k →
      lineCoarseRestrictSuTwo (ell ^ k) A (bondsE ell k Lu hell e) = Bf e)
    (hsupp : ∀ q : PeriodicLatticePlaquette Lu, ¬ (∀ c, InBox q.1 c → embY ell k Lu hell c ∈ S.Om k) →
      flatCurlValue Bf q = 0) :
    ((ell ^ k : ℕ) : ℝ) * ∑ q : PeriodicLatticePlaquette Lu, ‖flatCurlValue Bf q‖ ^ 2
      ≤ ∑ p ∈ (Finset.univ : Finset (PeriodicLatticePlaquette (scaleUp ell k Lu))).filter
            (fun p => p ∈ plaqIn (S.Om 0)), ‖flatCurlValue A p‖ ^ 2 := by
  classical
  set Qg : Finset (PeriodicLatticePlaquette Lu) := Finset.univ.filter
    (fun q => ∀ c, InBox q.1 c → embY ell k Lu hell c ∈ S.Om k) with hQg
  have hsum : ∑ q : PeriodicLatticePlaquette Lu, ‖flatCurlValue Bf q‖ ^ 2
      = ∑ q ∈ Qg, ‖flatCurlValue Bf q‖ ^ 2 := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) (fun q _ hq => ?_)
    have : ¬ (∀ c, InBox q.1 c → embY ell k Lu hell c ∈ S.Om k) := fun h =>
      hq (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    rw [hsupp q this]; simp
  rw [hsum]
  -- on Qg the unit curl of Bf is the coarse curl of the level-n average
  have hcurl : ∀ q ∈ Qg, flatCurlValue Bf q =
      coarseCurlSuTwo (scaleUp_tiling ell k Lu hell) (lineCoarseRestrictSuTwo (ell ^ k) A) (plaqE ell k Lu hell q) := by
    intro q hq
    have hg := (Finset.mem_filter.mp hq).2
    have hb : ∀ e : Bond Lu, (e = (q.1, q.2.1.1) ∨ e = (periodicLatticeShift q.1 q.2.1.1, q.2.1.2) ∨
        e = (periodicLatticeShift q.1 q.2.1.2, q.2.1.1) ∨ e = (q.1, q.2.1.2)) →
        Bf e = unitField ell k Lu hell (lineCoarseRestrictSuTwo (ell ^ k) A) e := by
      intro e he
      have hμν : q.2.1.1 ≠ q.2.1.2 := ne_of_lt q.2.2
      have hmem : embY ell k Lu hell e.1 ∈ S.Om k ∧ embY ell k Lu hell (periodicLatticeShift e.1 e.2) ∈ S.Om k := by
        rcases he with rfl | rfl | rfl | rfl
        · exact ⟨hg _ (self_inBox _), hg _ (shift_inBox _ _)⟩
        · exact ⟨hg _ (shift_inBox _ _), hg _ (shift_shift_inBox _ _ _ hμν)⟩
        · exact ⟨hg _ (shift_inBox _ _), hg _ (by
            have := shift_shift_inBox q.1 q.2.1.2 q.2.1.1 (Ne.symm hμν); exact this)⟩
        · exact ⟨hg _ (self_inBox _), hg _ (shift_inBox _ _)⟩
      exact (hQ e hmem.1 hmem.2).symm
    rw [← curl_reindex ell k Lu hell hu]
    unfold flatCurlValue
    rw [hb (q.1, q.2.1.1) (Or.inl rfl), hb (periodicLatticeShift q.1 q.2.1.1, q.2.1.2) (Or.inr (Or.inl rfl)),
      hb (periodicLatticeShift q.1 q.2.1.2, q.2.1.1) (Or.inr (Or.inr (Or.inl rfl))),
      hb (q.1, q.2.1.2) (Or.inr (Or.inr (Or.inr rfl)))]
  have h1 : ∑ q ∈ Qg, ‖flatCurlValue Bf q‖ ^ 2 =
      ∑ q ∈ Qg, ‖coarseCurlSuTwo (scaleUp_tiling ell k Lu hell) (lineCoarseRestrictSuTwo (ell ^ k) A)
        (plaqE ell k Lu hell q)‖ ^ 2 :=
    Finset.sum_congr rfl (fun q hq => by rw [hcurl q hq])
  set Y : Finset (CoarsePlaquette (scaleUp ell k Lu) (ell ^ k)) :=
    Qg.map (plaqE ell k Lu hell).toEmbedding with hY
  have h2 : ∑ q ∈ Qg, ‖coarseCurlSuTwo (scaleUp_tiling ell k Lu hell) (lineCoarseRestrictSuTwo (ell ^ k) A)
        (plaqE ell k Lu hell q)‖ ^ 2 =
      ∑ p ∈ Y, ‖coarseCurlSuTwo (scaleUp_tiling ell k Lu hell) (lineCoarseRestrictSuTwo (ell ^ k) A) p‖ ^ 2 := by
    rw [hY, Finset.sum_map]; rfl
  rw [h1, h2]
  refine local_stokes_suTwo (pow_pos hell k) (scaleUp_tiling ell k Lu hell) A Y _ ?_
  intro p hp x hx i hi j hj
  obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
  have hg := (Finset.mem_filter.mp hq).2
  rw [Finset.mem_range] at hi hj
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  exact window_plaqIn hell hu hS q.1 hg q.2 x hx i j hi hj

#print axioms local_unit_stokes

end AdalyFormal.DirichletMono
