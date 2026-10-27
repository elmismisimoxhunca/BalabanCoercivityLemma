import NP5
import WN11

/-!
# NP6 -- gauge covariance of the LOCAL decoupled form `locG0` (m1_patch_nonflat, 2026-10-14)

For a gauge function `γ` (`Ad_γ` on sites `adSL γ`, on bonds `adBL γ`):
* `mem_NK_gauge` : `Ad_γ f ∈ N_K(U^γ) ↔ f ∈ N_K(U)`  (`N(Q')` by GaugeCov `mem_NQp_gauge`; the support of `f` is unchanged);
* `VK_gauge` : `V_K(U^γ) = Ad_γ V_K(U)`;
* **`locG0_gauge`** : `locG0 S ell k (U^γ) a K (Ad_γ A) = locG0 S ell k U a K A` (`0 ≤ a`) — curl and mass as in W3NF
  `G0form_gauge`, the restricted projection by `V_K_gauge` and `map_starProjection`;
* `supp_adBL` : `Ad_γ A` has the same bond support as `A`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1NonFlat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.StatementLane (Tower)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.GaugeCov (adSL adBL mem_NQp_gauge lapDir_gauge gradAdj_gauge)
open AdalyFormal.M1W2 (NK VK suppIn locG0)

variable {L : PeriodicLatticeExtent}

theorem mem_NK_gauge (G : TowerGeom L) (γ : GaugeFn L) (U : Cfg L) (K : Set (PeriodicLatticeSite L)) (f : SiteL2 L) :
    adSL γ f ∈ NK G (periodicGaugeTransform γ U) K ↔ f ∈ NK G U K := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(mem_NQp_gauge G γ U f).mp h1, fun x hx => ?_⟩
    have := h2 x hx
    exact (AdalyFormal.GaugeCov.RMap_eq_zero_iff _ _).mp this
  · rintro ⟨h1, h2⟩
    refine ⟨(mem_NQp_gauge G γ U f).mpr h1, fun x hx => ?_⟩
    show RMap (γ x) (f x) = 0
    rw [h2 x hx, map_zero]

theorem VK_gauge (G : TowerGeom L) (γ : GaugeFn L) (U : Cfg L) (K : Set (PeriodicLatticeSite L)) :
    VK G (periodicGaugeTransform γ U) K = (VK G U K).map (adSL γ).toLinearIsometry.toLinearMap := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨f, rfl⟩ := (adSL γ).surjective w
    refine ⟨lapDir G U f, ⟨f, (mem_NK_gauge G γ U K f).mp hw, rfl⟩, ?_⟩
    exact (lapDir_gauge G γ U f).symm
  · rintro ⟨u, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨adSL γ f, (mem_NK_gauge G γ U K f).mpr hf, (lapDir_gauge G γ U f)⟩

theorem VKproj_gauge (G : TowerGeom L) (γ : GaugeFn L) (U : Cfg L) (K : Set (PeriodicLatticeSite L)) (f : SiteL2 L) :
    (VK G (periodicGaugeTransform γ U) K).starProjection (adSL γ f) = adSL γ ((VK G U K).starProjection f) := by
  have key : ∀ (K1 K2 : Submodule ℝ (SiteL2 L)) [K1.HasOrthogonalProjection] [K2.HasOrthogonalProjection],
      K1 = K2 → ∀ x, K1.starProjection x = K2.starProjection x := by
    intro K1 K2 _ _ h x; subst h; rfl
  rw [key _ _ (VK_gauge G γ U K)]
  exact ((adSL γ).toLinearIsometry.map_starProjection (VK G U K) f).symm

/-- **`locG0` is gauge invariant**. -/
theorem locG0_gauge (S : Tower L) (ell k : ℕ) (U : Cfg L) (a : ℝ) (γ : GaugeFn L) (K : Set (PeriodicLatticeSite L))
    (A : BondFnL2 L) :
    locG0 S ell k (periodicGaugeTransform γ U) a K (adBL γ A) = locG0 S ell k U a K A := by
  unfold locG0
  have h1 : ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn (S.Om 0))
        (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (periodicGaugeTransform γ U) (adBL γ A))‖ ^ 2
      = ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn (S.Om 0))
        (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U A)‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    exact AdalyFormal.GaugeCov.plaq_form_gauge γ U (plaqIn (S.Om 0)) A A
  have h2 : ‖(VK (geomOf ell k S) (periodicGaugeTransform γ U) K).starProjection
        (gradAdj (periodicGaugeTransform γ U) (adBL γ A))‖
      = ‖(VK (geomOf ell k S) U K).starProjection (gradAdj U A)‖ := by
    rw [gradAdj_gauge, VKproj_gauge, LinearIsometryEquiv.norm_map]
  have h3 : ‖AdalyFormal.M1IMS.Ymass (geomOf ell k S) (periodicGaugeTransform γ U) a (adBL γ A)‖
      = ‖AdalyFormal.M1IMS.Ymass (geomOf ell k S) U a A‖ := by
    show ‖diagW (geomOf ell k S) _ (QfullOf (geomOf ell k S) (periodicGaugeTransform γ U) (adBL γ A))‖
      = ‖diagW (geomOf ell k S) _ (QfullOf (geomOf ell k S) U A)‖
    rw [AdalyFormal.GaugeCov.QfullOf_gauge, AdalyFormal.GaugeCov.diagW_adFL, LinearIsometryEquiv.norm_map]
  rw [h1, h2, h3]

theorem supp_adBL (γ : GaugeFn L) (A : BondFnL2 L) (b : Bond L) :
    (WithLp.ofLp (adBL γ A)) b ≠ 0 ↔ (WithLp.ofLp A) b ≠ 0 := by
  have e : (WithLp.ofLp (adBL γ A)) b = RMap (γ b.1) ((WithLp.ofLp A) b) := rfl
  rw [e]
  exact not_congr (AdalyFormal.GaugeCov.RMap_eq_zero_iff _ _)

end AdalyFormal.M1NonFlat

#print axioms AdalyFormal.M1NonFlat.mem_NK_gauge
#print axioms AdalyFormal.M1NonFlat.VK_gauge
#print axioms AdalyFormal.M1NonFlat.VKproj_gauge
#print axioms AdalyFormal.M1NonFlat.locG0_gauge
#print axioms AdalyFormal.M1NonFlat.supp_adBL
