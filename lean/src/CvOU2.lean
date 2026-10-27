import CvOU1
import CvO47

/-!
# CvOU2 -- `τ*` of a unit Z-field is a row field; `Cop`, `D2in` on unit Z-fields (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (scaleUp Tower)

open Classical in
theorem sum_BIdx_dep {L : PeriodicLatticeExtent} (G : TowerGeom L) (F : BIdx G → ℝ) :
    ∑ p : BIdx G, F p = ∑ j : Fin (G.k + 1), ∑ b : Bond L, (if h : b ∈ bondsLam G j then F ⟨j, ⟨b, h⟩⟩ else 0) := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  let f : Bond L → ℝ := fun b => if h : b ∈ bondsLam G j then F ⟨j, ⟨b, h⟩⟩ else 0
  have h1 : ∑ y : {b // b ∈ bondsLam G j}, F ⟨j, y⟩ = ∑ y : {b // b ∈ bondsLam G j}, f y.1 := by
    refine Finset.sum_congr rfl (fun y _ => ?_)
    simp only [f, dif_pos y.2]
  rw [h1]
  have h2 : ∑ y : {b // b ∈ bondsLam G j}, f y.1 = ∑ b ∈ Finset.univ.filter (fun b : Bond L => b ∈ bondsLam G j), f b :=
    (Finset.sum_subtype (Finset.univ.filter (fun b : Bond L => b ∈ bondsLam G j)) (by simp) f).symm
  rw [h2, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  by_cases hb : b ∈ bondsLam G j
  · rw [if_pos hb]
  · simp only [f, dif_neg hb]; simp [hb]

theorem unitBondEmb_inj (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) :
    Function.Injective (unitBondEmb ell k Lu hell) := by
  intro e e' h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  refine Prod.ext ?_ h2
  funext μ
  have := congrFun h1 μ
  apply Fin.ext
  have h3 : ell ^ k * (e.1 μ).val = ell ^ k * (e'.1 μ).val := by
    have := congrArg Fin.val this
    simpa [unitBondEmb, embY] using this
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hell k) h3

theorem unitBondEmb_surj (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (b : Bond (scaleUp ell k Lu))
    (hb : Crs (ell ^ k) b.1) : ∃ e : Bond Lu, unitBondEmb ell k Lu hell e = b := by
  have hlt : ∀ μ : Fin 3, (b.1 μ).val / ell ^ k < Lu μ + 1 := by
    intro μ
    have h1 := (b.1 μ).isLt
    have h2 : scaleUp ell k Lu μ + 1 = (Lu μ + 1) * ell ^ k := by
      unfold scaleUp
      have : 1 ≤ (Lu μ + 1) * ell ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    have h1' : (b.1 μ).val < (Lu μ + 1) * ell ^ k := by omega
    exact (Nat.div_lt_iff_lt_mul (pow_pos hell k)).mpr h1'
  refine ⟨(fun μ => ⟨(b.1 μ).val / ell ^ k, hlt μ⟩, b.2), ?_⟩
  refine Prod.ext ?_ rfl
  funext μ
  apply Fin.ext
  obtain ⟨q, hq⟩ := hb μ
  simp only [unitBondEmb, embY]
  rw [hq, Nat.mul_div_cancel_left _ (pow_pos hell k)]

end AdalyFormal.CoverOmega
