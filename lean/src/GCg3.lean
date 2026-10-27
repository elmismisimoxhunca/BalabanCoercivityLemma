import GC3

/-!
# GCg3 -- unit-level equivariance of `ι_D`, `H₀`, `H₀⁻¹`, `h`, `C` (ZXR2Unit2) and of `D2in` (ZXR2Wire2).

Frames: coarse bond `c` in frame `g c.1.1` (its base site); on `Dset` two actions:
`adD`  (frame `g c.1.1.1`, the coarse site -- what `ρ` produces from `adCg`), and
`adD2` (frame `g (droppedBondLast ell c.1).1`, the base site of the dropped bond -- what `ι_D` needs).
The hypothesis on `Q` is POINTWISE: `Q' (gaugeActA g B) c = RMap (g c.1.1) (Q B c)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace AdalyFormal.GaugeCov
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_mul_apply RMap_one)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA gaugeActA_apply)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.ReparamCDisjoint (droppedBondLast)
open AdalyFormal.IngredientFamilyR2

/-- pointwise `Ad_φ` on plain functions `ι → 𝔰𝔲(2)`, as a linear equivalence. -/
def adFun {ι : Type*} (φ : ι → SU2g) : (ι → SuTwo) ≃ₗ[ℝ] (ι → SuTwo) where
  toFun w := fun i => RMap (φ i) (w i)
  invFun w := fun i => RMap ((φ i)⁻¹) (w i)
  map_add' v w := by funext i; simp
  map_smul' r w := by funext i; simp
  left_inv w := by funext i; simp [RMap_mul_apply, RMap_one]
  right_inv w := by funext i; simp [RMap_mul_apply, RMap_one]

theorem adFun_apply {ι : Type*} (φ : ι → SU2g) (w : ι → SuTwo) (i : ι) :
    adFun φ w i = RMap (φ i) (w i) := rfl

theorem gaugeActA_eq_adFun {L : PeriodicLatticeExtent} (g : GaugeFn L) (B : Bond L → SuTwo) :
    gaugeActA g B = adFun (fun b : Bond L => g b.1) B := rfl

variable {Lu : PeriodicLatticeExtent} (ell : ℕ) (Lam : Set (PeriodicLatticeSite Lu)) (g : GaugeFn Lu)

/-- coarse bonds, frame = base site. -/
abbrev adCg : (CoarseBond Lu ell → SuTwo) ≃ₗ[ℝ] (CoarseBond Lu ell → SuTwo) :=
  adFun (fun c : CoarseBond Lu ell => g c.1.1)
/-- `Dset`, frame = coarse site. -/
abbrev adD : (Dset Lu ell Lam → SuTwo) ≃ₗ[ℝ] (Dset Lu ell Lam → SuTwo) :=
  adFun (fun c : Dset Lu ell Lam => g c.1.1.1)
/-- `Dset`, frame = base site of the dropped bond. -/
abbrev adD2 : (Dset Lu ell Lam → SuTwo) ≃ₗ[ℝ] (Dset Lu ell Lam → SuTwo) :=
  adFun (fun c : Dset Lu ell Lam => g (droppedBondLast ell c.1).1)

theorem iotaD_adD2 (w : Dset Lu ell Lam → SuTwo) :
    iotaD ell Lam (adD2 ell Lam g w) = gaugeActA g (iotaD ell Lam w) := by
  classical
  funext b
  simp only [iotaD, LinearMap.coe_mk, AddHom.coe_mk, gaugeActA_apply, map_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  by_cases h : b = droppedBondLast ell c.1
  · subst h; simp [adFun_apply]
  · simp [h]

theorem rhoD_adC (f : CoarseBond Lu ell → SuTwo) :
    rhoD ell Lam (adCg ell g f) = adD ell Lam g (rhoD ell Lam f) := rfl

variable {ell Lam g}
variable {Q Q' : (Bond Lu → SuTwo) →ₗ[ℝ] (CoarseBond Lu ell → SuTwo)}

/-- `H₀' ∘ adD2 = adD ∘ H₀`. -/
theorem H0_gauge (hQ : ∀ B c, Q' (gaugeActA g B) c = RMap (g c.1.1) (Q B c))
    (w : Dset Lu ell Lam → SuTwo) :
    H0 Lam Q' (adD2 ell Lam g w) = adD ell Lam g (H0 Lam Q w) := by
  show rhoD ell Lam (Q' (iotaD ell Lam (adD2 ell Lam g w))) = _
  rw [iotaD_adD2]
  funext c
  exact hQ _ c.1

theorem H0_bijective_iff (hQ : ∀ B c, Q' (gaugeActA g B) c = RMap (g c.1.1) (Q B c)) :
    Function.Bijective (H0 Lam Q') ↔ Function.Bijective (H0 Lam Q) := by
  have h1 : (H0 Lam Q' : (Dset Lu ell Lam → SuTwo) → _) =
      (adD ell Lam g) ∘ (H0 Lam Q) ∘ (adD2 ell Lam g).symm := by
    funext w
    have := H0_gauge (Lam := Lam) hQ ((adD2 ell Lam g).symm w)
    rw [LinearEquiv.apply_symm_apply] at this
    simpa using this
  rw [h1, EquivLike.comp_bijective, EquivLike.bijective_comp]

theorem H0inv_gauge (hQ : ∀ B c, Q' (gaugeActA g B) c = RMap (g c.1.1) (Q B c))
    (w : Dset Lu ell Lam → SuTwo) :
    H0inv Lam Q' (adD ell Lam g w) = adD2 ell Lam g (H0inv Lam Q w) := by
  classical
  by_cases hb : Function.Bijective (H0 Lam Q)
  · have hb' := (H0_bijective_iff (Lam := Lam) hQ).mpr hb
    apply hb'.1
    rw [H0_H0inv Lam Q' hb', H0_gauge hQ, H0_H0inv Lam Q hb]
  · have hb' : ¬ Function.Bijective (H0 Lam Q') := fun h => hb ((H0_bijective_iff hQ).mp h)
    unfold H0inv
    rw [dif_neg hb, dif_neg hb']
    simp

theorem hLift_gauge (hQ : ∀ B c, Q' (gaugeActA g B) c = RMap (g c.1.1) (Q B c))
    (w : CoarseBond Lu ell → SuTwo) :
    hLift Lam Q' (adCg ell g w) = gaugeActA g (hLift Lam Q w) := by
  show iotaD ell Lam (H0inv Lam Q' (rhoD ell Lam (adCg ell g w))) = _
  rw [rhoD_adC, H0inv_gauge hQ, iotaD_adD2]
  rfl

theorem Cop_gauge (hQ : ∀ B c, Q' (gaugeActA g B) c = RMap (g c.1.1) (Q B c))
    (B : Bond Lu → SuTwo) :
    Cop Lam Q' (gaugeActA g B) = gaugeActA g (Cop Lam Q B) := by
  have hQ' : Q' (gaugeActA g B) = adCg ell g (Q B) := funext (hQ B)
  show gaugeActA g B - hLift Lam Q' (Q' (gaugeActA g B)) = gaugeActA g (B - hLift Lam Q (Q B))
  rw [hQ', hLift_gauge hQ, gaugeActA_eq_adFun, gaugeActA_eq_adFun, gaugeActA_eq_adFun, map_sub]

/-! ## G4: `D2in` -/

/-- **G4.** `P'.D2in (adBL g B) = adBL g (P.D2in B)` for `P' = {P with U := U'}`, from the
pointwise `Q₁`- and `C̃⁽²⁾`-equivariance at the unit level. -/
theorem D2in_gauge (P : IngrBParams) (U' : PeriodicLinkConfiguration SU2g P.Lf)
    (g : GaugeFn P.Lu)
    (hQ1 : ∀ B c, ({ P with U := U' } : IngrBParams).Q1 (gaugeActA g B) c = RMap (g c.1.1) (P.Q1 B c))
    (hC2 : ∀ B c, C2tilde P.ell ({ P with U := U' } : IngrBParams).unitBgU (gaugeActA g B) c =
      RMap (g c.1.1) (C2tilde P.ell P.unitBgU B c))
    (B : BondFnL2 P.Lu) :
    ({ P with U := U' } : IngrBParams).D2in (adBL g B) = adBL g (P.D2in B) := by
  have hC : C2tilde P.ell ({ P with U := U' } : IngrBParams).unitBgU (gaugeActA g (WithLp.ofLp B)) =
      adCg P.ell g (C2tilde P.ell P.unitBgU (WithLp.ofLp B)) := funext (hC2 _)
  have hL := hLift_gauge (Lam := P.Lam) hQ1 (C2tilde P.ell P.unitBgU (WithLp.ofLp B))
  refine PiLp.ext (fun e => ?_)
  show ((P.ell : ℝ)⁻¹ • hLift P.Lam ({ P with U := U' } : IngrBParams).Q1
      (C2tilde P.ell ({ P with U := U' } : IngrBParams).unitBgU (gaugeActA g (WithLp.ofLp B)))) e =
    RMap (g e.1) (((P.ell : ℝ)⁻¹ • hLift P.Lam P.Q1 (C2tilde P.ell P.unitBgU (WithLp.ofLp B))) e)
  rw [hC, hL, Pi.smul_apply, Pi.smul_apply, gaugeActA_apply, map_smul]

#print axioms iotaD_adD2
#print axioms H0_gauge
#print axioms H0_bijective_iff
#print axioms H0inv_gauge
#print axioms hLift_gauge
#print axioms Cop_gauge
#print axioms D2in_gauge

end AdalyFormal.GaugeCov
