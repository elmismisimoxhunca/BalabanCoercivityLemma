import MF6c
import NJ11bNum
import NJ13bReg
import ZXR2Wire2

/-!
# MF6d (TEXT COPY of nonflat_jet R5Final, recompiled against the r7 fork) -- on the r5 statement-lane carrier: `hb` (`H₀` bijective) at a non-flat unit background, and surjectivity of `Q₁`.
`Dset` = coarse bonds TOUCHING `Λ'` (r5 (3)).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.M0Finish.R7

open Matrix
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.StatementLane (CRowIn)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.NonflatJet (rhoOf numeric_small regBg_of_small r0)
open SmallnessBridge.Assemble (loopFactorBound)
open EstimatesLayer.E1E3

variable {L : PeriodicLatticeExtent}

theorem H0_bijective_of_small {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (Lam : Set (PeriodicLatticeSite L)) (V : PeriodicLinkConfiguration SU2 L) (ε0 : ℝ)
    (hε0 : 0 ≤ ε0) (hV : ∀ e, frobNorm ((V e : M2) - 1) ≤ ε0)
    (hsmall : rhoOf ell ε0 < Real.pi / 2) (hreg : RegBg 1 ell V)
    (hε : 8 * ell * ε0 + 8 * e2Majorant (rhoOf ell ε0) < 1 / (ell : ℝ) ^ 3) :
    Function.Bijective (H0 Lam (Q1jet ell V)) := by
  have hinj := H0_injective_of_small hell hdvd Lam V ε0 hε0 hV hsmall hreg hε
  exact ⟨hinj, (LinearMap.injective_iff_surjective).mp hinj⟩

/-- **`hb` of `toIngr` on the r5 carrier, from per-link smallness alone.** -/
theorem hb_of_small (P : IngrBParams) (hdvd : ∀ μ, P.ell ∣ (P.Lu μ + 1)) (ε0 : ℝ) (hε0 : 0 ≤ ε0)
    (hle : ε0 ≤ 1 / (1000 * (P.ell : ℝ) ^ 4))
    (hr : Real.pi / 2 * ((loopFactorBound P.ell : ℝ) * ε0) < r0)
    (hV : ∀ e, frobNorm ((P.unitBgU e : M2) - 1) ≤ ε0) :
    Function.Bijective (H0 P.Lam P.Q1) := by
  have hn := numeric_small P.hell ε0 hε0 hle
  exact H0_bijective_of_small P.hell hdvd P.Lam P.unitBgU ε0 hε0 hV hn.1
    (regBg_of_small Nat.one_pos P.unitBgU ε0 hε0 hV hr) hn.2

theorem Q1jet_surjective_of_small {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (V : PeriodicLinkConfiguration SU2 L) (ε0 : ℝ) (hε0 : 0 ≤ ε0)
    (hle : ε0 ≤ 1 / (1000 * (ell : ℝ) ^ 4))
    (hr : Real.pi / 2 * ((loopFactorBound ell : ℝ) * ε0) < r0)
    (hV : ∀ e, frobNorm ((V e : M2) - 1) ≤ ε0) :
    Function.Surjective (Q1jet ell V) := by
  have hn := numeric_small hell ε0 hε0 hle
  have hb := H0_bijective_of_small hell hdvd (Set.univ : Set (PeriodicLatticeSite L)) V ε0 hε0 hV hn.1
    (regBg_of_small Nat.one_pos V ε0 hε0 hV hr) hn.2
  intro f
  obtain ⟨w, hw⟩ := hb.2 (rhoD ell Set.univ f)
  refine ⟨iotaD ell Set.univ w, funext fun c => ?_⟩
  have := congrFun hw ⟨c, Or.inl ⟨c.1.2, fun _ _ => Set.mem_univ _⟩⟩
  exact this

#print axioms hb_of_small
#print axioms Q1jet_surjective_of_small

end AdalyFormal.M0Finish.R7
