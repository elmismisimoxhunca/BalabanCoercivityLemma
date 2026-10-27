import DrPath2

/-!
# DrPath3 -- the exterior-path separation criterion (see DrPath2 header).
The three operators along the path are given a constant carrier `E0 := bondSupp (geomOf ell k S)` by definition (`GinvLit`, `G1Lit`, `DeltaLoc0`),
because the carrier of `dataS ... (Ppt .. t)` mentions `t` syntactically.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Residual

open scoped RealInnerProductSpace
open Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.D1Guarded
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-- the common carrier. -/
noncomputable abbrev E0 {ell k : ℕ} {Lu : PeriodicLatticeExtent} (S : Tower (scaleUp ell k Lu)) : Type :=
  ↥(bondSupp (geomOf ell k S))

/-- literal `Ginv` along the path, on the constant carrier. -/
noncomputable def GinvLit {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) (S : Tower (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (U : ℝ → Cfg (scaleUp ell k Lu)) (t : ℝ) : E0 S →L[ℝ] E0 S :=
  (dataS selAll selAll (Ppt hell0 S a Lam U t)).Ginv

/-- literal `G1inv` along the path, on the constant carrier. -/
noncomputable def G1Lit {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) (S : Tower (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (U : ℝ → Cfg (scaleUp ell k Lu)) (t : ℝ) : E0 S →L[ℝ] E0 S :=
  G1invS selAll selAll (Ppt hell0 S a Lam U t)

/-- the localised correction at the start of the path. -/
noncomputable def DeltaLoc0 {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) (S : Tower (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (U : ℝ → Cfg (scaleUp ell k Lu)) : E0 S →L[ℝ] E0 S :=
  (dataS selIn selIn (Ppt hell0 S a Lam U 0)).Delta2 (dataS_laws selIn selIn (Ppt hell0 S a Lam U 0))

/-- abstract form of the separation criterion (no lattice objects, so no definitional unfolding of the data). -/
theorem sep_abstract {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (M : ℝ → (E →L[ℝ] E)) (Δ0 : E →L[ℝ] E) (G1 : ℝ → (E →L[ℝ] E)) (hc : Continuous M)
    (hs : ∀ t x y, ⟪M t x, y⟫ = ⟪x, M t y⟫) (hΔ : ∀ x y, ⟪Δ0 x, y⟫ = ⟪x, Δ0 y⟫)
    (hG1 : ∀ t, IsUnit (M t) → G1 t = M t - Δ0)
    (T : ℝ) (hT : 0 < T) (hco : ∀ t ∈ Icc (0 : ℝ) T, ∃ c' : ℝ, 0 < c' ∧ ∀ x, c' * ‖x‖ ^ 2 ≤ ⟪x, M t x⟫)
    (h0 : AdalyFormal.D1Literal.PSD (M 0 - Δ0)) (v : E) (hv : ⟪v, (M T - Δ0) v⟫ < 0) :
    ∃ t : ℝ, 0 ≤ t ∧ t < T ∧ IsUnit (M t) ∧ ¬ IsUnit (G1 t) := by
  obtain ⟨t, ht0, htT, hu, hnu⟩ := pencil_bracket M Δ0 hc hs hΔ T hT hco h0 v hv
  refine ⟨t, ht0, htT, hu, ?_⟩
  rw [hG1 t hu]
  exact hnu

section path
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)}
  (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
  (U : ℝ → Cfg (scaleUp ell k Lu)) (hUU : ∀ (t : ℝ) (e : Bond (scaleUp ell k Lu)), e ∉ Zb (S.Om 0) → U t e = U 0 e)

include hS hell hroom hUU in
/-- the literal `Ginv` is continuous in the path parameter when the path is. -/
theorem GinvLit_cont (hcont : ContFam U) : Continuous (GinvLit hell0 S a Lam U) := by
  have hfun : GinvLit hell0 S a Lam U = fun t =>
      GinvLit hell0 S a Lam U 0 +
      (pE (geomOf ell k S)).comp (((ContinuousLinearMap.adjoint (Wop (geomOf ell k S) (U 0) a)).comp
        (((AdalyFormal.StatementLaneR6.deltaKLocCLM (U t) Set.univ) -
          (AdalyFormal.StatementLaneR6.deltaKLocCLM (U 0) Set.univ)).comp
          (Wop (geomOf ell k S) (U 0) a))).comp (iE (geomOf ell k S))) :=
    funext fun t => Ginv_lit_path hell0 hS hell hroom a Lam U hUU selAll t
  rw [hfun]
  have hD := cont_deltaKLocCLM hcont (Set.univ : Set (PeriodicLatticePlaquette (scaleUp ell k Lu)))
  refine continuous_const.add ?_
  exact continuous_const.clm_comp ((continuous_const.clm_comp ((hD.sub continuous_const).clm_comp continuous_const)).clm_comp
    continuous_const)

include hS hell hroom hUU in
/-- pointwise pencil identity along the path (the literal `G1inv` is `Ginv_lit(t) - Delta2_loc(0)` wherever `Ginv_lit(t)` is a unit). -/
theorem G1Lit_eq (hWD0 : WellDefAt selIn selIn (Ppt hell0 S a Lam U 0)) (t : ℝ)
    (hu : IsUnit (GinvLit hell0 S a Lam U t)) :
    G1Lit hell0 S a Lam U t = GinvLit hell0 S a Lam U t - DeltaLoc0 hell0 S a Lam U :=
  (G1inv_lit_eq_pencil (Ppt hell0 S a Lam U t) hS hell0 hroom hu
    (WellDefAt_loc_const hell0 hS hell hroom a Lam U hUU t hWD0)).trans
    (congrArg (fun D => GinvLit hell0 S a Lam U t - D)
      (Delta2_loc_const hell0 hS hell hroom a Lam U hUU t))

include hS hell hroom hUU in
/-- **exterior-path separation criterion.**  Along a continuous exterior-only path, if `Ginv_lit` is coercive on `[0,T]`, `Ginv_lit(0) - Delta2_loc` is positive
semidefinite and `Ginv_lit(T) - Delta2_loc` has a negative direction, then at some `t < T` the configuration `U t` is in class (if `U 0` is),
`Ginv_lit` is a unit there and `G1inv_lit` is NOT a unit. -/
theorem exterior_path_separation (hcont : ContFam U) (hWD0 : WellDefAt selIn selIn (Ppt hell0 S a Lam U 0))
    (c : ℕ) (α₀ η : ℝ) (hcl : ClassCoupled ell M c k S α₀ η (U 0))
    (T : ℝ) (hT : 0 < T)
    (hco : ∀ t ∈ Icc (0 : ℝ) T, ∃ c' : ℝ, 0 < c' ∧ ∀ x, c' * ‖x‖ ^ 2 ≤ ⟪x, GinvLit hell0 S a Lam U t x⟫)
    (h0 : AdalyFormal.D1Literal.PSD (GinvLit hell0 S a Lam U 0 - DeltaLoc0 hell0 S a Lam U))
    (v : E0 S) (hv : ⟪v, (GinvLit hell0 S a Lam U T - DeltaLoc0 hell0 S a Lam U) v⟫ < 0) :
    ∃ t : ℝ, 0 ≤ t ∧ t < T ∧ ClassCoupled ell M c k S α₀ η (U t) ∧
      IsUnit (GinvLit hell0 S a Lam U t) ∧ ¬ IsUnit (G1Lit hell0 S a Lam U t) := by
  obtain ⟨t, ht0, htT, hu, hnu⟩ := sep_abstract (GinvLit hell0 S a Lam U) (DeltaLoc0 hell0 S a Lam U) (G1Lit hell0 S a Lam U)
    (GinvLit_cont hell0 hS hell hroom a Lam U hUU hcont)
    (fun t x y => (dataS selAll selAll (Ppt hell0 S a Lam U t)).Ginv_symm (dataS_laws selAll selAll (Ppt hell0 S a Lam U t)) x y)
    (((dataS selIn selIn (Ppt hell0 S a Lam U 0)).Delta2_spec (dataS_laws selIn selIn (Ppt hell0 S a Lam U 0))).1)
    (fun t hu => G1Lit_eq hell0 hS hell hroom a Lam U hUU hWD0 t hu)
    T hT hco h0 v hv
  exact ⟨t, ht0, htT, classCoupled_path hS hell hroom U hUU c α₀ η hcl t, hu, hnu⟩

end path

#print axioms sep_abstract
#print axioms GinvLit_cont
#print axioms G1Lit_eq
#print axioms exterior_path_separation

end AdalyFormal.D1Residual
