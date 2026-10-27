import NsCvOU2

/-!
# CvOU3 -- `τ*` of a unit Z-field (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (scaleUp Tower)

theorem hsInner_zero_left' (X : SuTwo) : hsInner 0 X = 0 := by
  rw [AdalyFormal.Balaban.SuTwoInner.hsInner_symm]; exact AdalyFormal.Balaban.DeltaKU.hsInner_zero_right X

open Classical in
theorem tau_adjoint_zfield (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (hcrs : ∀ b ∈ bondsLam (geomOf ell k S) k, Crs (ell ^ k) b.1) (g : ℕ → ℝ) :
    ContinuousLinearMap.adjoint (tauExt ell k Lu hell S) (zfield g) =
      zrow (geomOf ell k S) (fun j r => if j = k then g (r / ell ^ k) else 0) := by
  apply ext_inner_left ℝ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [PiLp.inner_apply, PiLp.inner_apply]
  show ∑ e : Bond Lu, hsInner ((tauExt ell k Lu hell S f) e) ((zfield g : BondFnL2 Lu) e) = ∑ p : BIdx (geomOf ell k S), hsInner (f p) ((zrow (geomOf ell k S) _) p)
  rw [sum_BIdx_dep (geomOf ell k S) (fun p => hsInner (f p) ((zrow (geomOf ell k S) (fun j r => if j = k then g (r / ell ^ k) else 0)) p))]
  rw [Finset.sum_eq_single (Fin.last (geomOf ell k S).k)]
  · -- main level
    have hsupp : ∀ b : Bond (scaleUp ell k Lu), b ∉ Finset.univ.image (unitBondEmb ell k Lu hell) →
        (if h : b ∈ bondsLam (geomOf ell k S) (Fin.last (geomOf ell k S).k : Fin ((geomOf ell k S).k + 1)) then hsInner (f ⟨Fin.last (geomOf ell k S).k, ⟨b, h⟩⟩)
          ((zrow (geomOf ell k S) (fun j r => if j = k then g (r / ell ^ k) else 0)) ⟨Fin.last (geomOf ell k S).k, ⟨b, h⟩⟩) else 0) = 0 := by
      intro b hb
      rw [dif_neg]
      intro hmem
      obtain ⟨e, he⟩ := unitBondEmb_surj ell k Lu hell b (hcrs b hmem)
      exact hb (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, he⟩)
    rw [← Finset.sum_subset (Finset.subset_univ _) (fun b _ hb => hsupp b hb)]
    rw [Finset.sum_image (fun e _ e' _ h => unitBondEmb_inj ell k Lu hell h)]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    show hsInner ((tauExt ell k Lu hell S f) e) (zfun g e) = _
    by_cases hb : unitBondEmb ell k Lu hell e ∈ bondsLam (geomOf ell k S) (Fin.last (geomOf ell k S).k : Fin ((geomOf ell k S).k + 1))
    · rw [dif_pos hb]
      have hb' : unitBondEmb ell k Lu hell e ∈ bondsLam (geomOf ell k S) k := hb
      have ht : (tauExt ell k Lu hell S f) e = f ⟨Fin.last (geomOf ell k S).k, ⟨unitBondEmb ell k Lu hell e, hb⟩⟩ := by
        show (if h : unitBondEmb ell k Lu hell e ∈ bondsLam (geomOf ell k S) k then WithLp.ofLp f ⟨Fin.last k, ⟨unitBondEmb ell k Lu hell e, h⟩⟩ else 0) = _
        rw [dif_pos hb']
        rfl
      rw [ht]
      congr 1
      show zfun g e = _
      unfold zfun
      show _ = (if (unitBondEmb ell k Lu hell e).2 = 1 then dgS ((if ((Fin.last (geomOf ell k S).k : Fin ((geomOf ell k S).k + 1)) : ℕ) = k then g (((unitBondEmb ell k Lu hell e).1 0).val / ell ^ k) else 0)) else 0)
      have hk : (geomOf ell k S).k = k := rfl
      simp [unitBondEmb, embY, hk, Nat.mul_div_cancel_left _ (pow_pos hell k)]
    · rw [dif_neg hb]
      have hb'' : unitBondEmb ell k Lu hell e ∉ bondsLam (geomOf ell k S) k := hb
      have ht : (tauExt ell k Lu hell S f) e = 0 := by
        show (if hb' : unitBondEmb ell k Lu hell e ∈ bondsLam (geomOf ell k S) k then WithLp.ofLp f ⟨Fin.last k, ⟨unitBondEmb ell k Lu hell e, hb'⟩⟩ else 0) = 0
        rw [dif_neg hb'']
      rw [ht]; exact hsInner_zero_left' _
  · intro j _ hj
    refine Finset.sum_eq_zero (fun b _ => ?_)
    by_cases hb : b ∈ bondsLam (geomOf ell k S) j
    · rw [dif_pos hb]
      have : (j : ℕ) ≠ k := fun h => hj (Fin.ext (by simpa [geomOf] using h))
      show hsInner _ ((if b.2 = 1 then dgS (if (j : ℕ) = k then g ((b.1 0).val / ell ^ k) else 0) else 0)) = 0
      rw [if_neg this, dgS_zero, ite_self]
      exact AdalyFormal.Balaban.DeltaKU.hsInner_zero_right _
    · rw [dif_neg hb]
  · intro h; exact absurd (Finset.mem_univ _) h

#print axioms tau_adjoint_zfield

end AdalyFormal.CoverOmega
