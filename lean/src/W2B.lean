import MI19
import W2A

/-!
# W2B -- the generic two-tower comparison of the decoupled form `G0` (M1 lane W2, 2026-10-13)

Two tower geometries on the SAME fine torus `L` and two link configurations `U₁, U₂`.  For a set of sites `K`:
* `suppIn K` : site fields vanishing off `K`;  `NK G U K = N(Q'_G(U)) ∩ suppIn K`;  `VK G U K = lapDir_G(U) (NK G U K)`;
* `defK G U K A = ‖R_G(U) D_U* A − P_{VK} D_U* A‖²` (the DECAY DEFECT: how much of the gauge-fixing square of `A` on the tower `G`
  is NOT captured by constraint-null fields supported in `K`);
* `VK_le_RImage` : `VK ≤ RImage = Δ_U N(Q')`;
* **`T_cmp`** : if every `f ∈ NK G₂ U₂ K` is also in `N(Q'_{G₁}(U₁))`, `lapDir` of the two towers agree on `NK G₂ U₂ K`, and
  `D_{U₁}* A = D_{U₂}* A`, then `‖T₂ A‖² − defK₂(A) ≤ ‖T₁ A‖²`  (EXACT, no decay assumed);
* **`G0_cmp`** : with in addition equal curl masks and equal mass squares,
  `G0₂(A) − defK₂(A) ≤ G0₁(A)`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M1W2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.StatementLaneR6 (plaqMask)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)
open AdalyFormal.M1IMS (G0form Ymass)

variable {L : PeriodicLatticeExtent}

/-- site fields supported in `K`. -/
def suppIn (K : Set (PeriodicLatticeSite L)) : Submodule ℝ (SiteL2 L) where
  carrier := {f | ∀ x, x ∉ K → f x = 0}
  zero_mem' := fun _ _ => by simp
  add_mem' := fun {f g} hf hg x hx => by simp [hf x hx, hg x hx]
  smul_mem' := fun c f hf x hx => by simp [hf x hx]

/-- constraint-null site fields of `G` at `U`, supported in `K`. -/
noncomputable def NK (G : TowerGeom L) (U : Cfg L) (K : Set (PeriodicLatticeSite L)) : Submodule ℝ (SiteL2 L) :=
  NQp G U ⊓ suppIn K

/-- their image under the Dirichlet Laplacian of `G`. -/
noncomputable def VK (G : TowerGeom L) (U : Cfg L) (K : Set (PeriodicLatticeSite L)) : Submodule ℝ (SiteL2 L) :=
  (NK G U K).map (lapDir G U : SiteL2 L →ₗ[ℝ] SiteL2 L)

/-- **the decay defect** of `A` on `(G, U)` relative to `K`. -/
noncomputable def defK (G : TowerGeom L) (U : Cfg L) (K : Set (PeriodicLatticeSite L)) (A : BondFnL2 L) : ℝ :=
  ‖Rproj G U (gradAdj U A) - (VK G U K).starProjection (gradAdj U A)‖ ^ 2

theorem defK_nonneg (G : TowerGeom L) (U : Cfg L) (K : Set (PeriodicLatticeSite L)) (A : BondFnL2 L) :
    0 ≤ defK G U K A := sq_nonneg _

theorem VK_le_RImage (G : TowerGeom L) (U : Cfg L) (K : Set (PeriodicLatticeSite L)) : VK G U K ≤ RImage G U :=
  Submodule.map_mono inf_le_left

theorem NK_mono (G : TowerGeom L) (U : Cfg L) {K K' : Set (PeriodicLatticeSite L)} (h : K ⊆ K') : NK G U K ≤ NK G U K' :=
  fun _ hf => ⟨hf.1, fun x hx => hf.2 x (fun hk => hx (h hk))⟩

/-- the defect decreases when `K` grows. -/
theorem defK_anti (G : TowerGeom L) (U : Cfg L) {K K' : Set (PeriodicLatticeSite L)} (h : K ⊆ K') (A : BondFnL2 L) :
    defK G U K' A ≤ defK G U K A := by
  unfold defK Rproj
  exact proj_defect_anti (VK G U K) (VK G U K') (RImage G U) (Submodule.map_mono (NK_mono G U h))
    (VK_le_RImage G U K') _

theorem Tfull_apply (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L) :
    Tfull G U A = (RImage G U).starProjection (gradAdj U A) := rfl

/-- **the gauge-fixing square through `K`** (exact). -/
theorem T_cmp (G₁ G₂ : TowerGeom L) (U₁ U₂ : Cfg L) (K : Set (PeriodicLatticeSite L)) (A : BondFnL2 L)
    (hN : ∀ f ∈ NK G₂ U₂ K, f ∈ NQp G₁ U₁)
    (hL : ∀ f ∈ NK G₂ U₂ K, lapDir G₁ U₁ f = lapDir G₂ U₂ f)
    (hD : gradAdj U₁ A = gradAdj U₂ A) :
    ‖Tfull G₂ U₂ A‖ ^ 2 - defK G₂ U₂ K A ≤ ‖Tfull G₁ U₁ A‖ ^ 2 := by
  have h1 : VK G₂ U₂ K ≤ RImage G₁ U₁ := by
    rintro v ⟨f, hf, rfl⟩
    refine ⟨f, hN f hf, ?_⟩
    exact hL f hf
  have h := proj_cmp (VK G₂ U₂ K) (RImage G₁ U₁) (RImage G₂ U₂) h1 (VK_le_RImage G₂ U₂ K) (gradAdj U₂ A)
  rw [Tfull_apply, Tfull_apply, hD]
  exact h

/-- **the `G0` comparison** (exact; the only loss is the decay defect of the comparison tower). -/
theorem G0_cmp {ell k₁ k₂ : ℕ} (S₁ S₂ : Tower L) (U₁ U₂ : Cfg L) (a : ℝ) (K : Set (PeriodicLatticeSite L))
    (A : BondFnL2 L)
    (hC : plaqMask (plaqIn (S₁.Om 0)) (curlCovariantLM_L2 U₁ A) = plaqMask (plaqIn (S₂.Om 0)) (curlCovariantLM_L2 U₂ A))
    (hM : ‖Ymass (geomOf ell k₁ S₁) U₁ a A‖ = ‖Ymass (geomOf ell k₂ S₂) U₂ a A‖)
    (hN : ∀ f ∈ NK (geomOf ell k₂ S₂) U₂ K, f ∈ NQp (geomOf ell k₁ S₁) U₁)
    (hL : ∀ f ∈ NK (geomOf ell k₂ S₂) U₂ K, lapDir (geomOf ell k₁ S₁) U₁ f = lapDir (geomOf ell k₂ S₂) U₂ f)
    (hD : gradAdj U₁ A = gradAdj U₂ A) :
    G0form S₂ ell k₂ U₂ a A - defK (geomOf ell k₂ S₂) U₂ K A ≤ G0form S₁ ell k₁ U₁ a A := by
  have hT := T_cmp (geomOf ell k₁ S₁) (geomOf ell k₂ S₂) U₁ U₂ K A hN hL hD
  unfold G0form
  rw [hC, hM]
  linarith

end AdalyFormal.M1W2

#print axioms AdalyFormal.M1W2.suppIn
#print axioms AdalyFormal.M1W2.NK
#print axioms AdalyFormal.M1W2.VK
#print axioms AdalyFormal.M1W2.defK
#print axioms AdalyFormal.M1W2.defK_nonneg
#print axioms AdalyFormal.M1W2.VK_le_RImage
#print axioms AdalyFormal.M1W2.NK_mono
#print axioms AdalyFormal.M1W2.defK_anti
#print axioms AdalyFormal.M1W2.Tfull_apply
#print axioms AdalyFormal.M1W2.T_cmp
#print axioms AdalyFormal.M1W2.G0_cmp
