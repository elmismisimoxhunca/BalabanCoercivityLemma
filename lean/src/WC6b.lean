import MI29
import WC6a

/-!
# WC6b -- counting the rows near a site (M2 W6 lane)

`card_rows_near` : the rows of level `l` whose base is within `m` of `c` number at most `3 (2m/ℓ^l + 1)³`.
`card_inter` : with `Inter p' p := |lev p' - lev p| ≤ 1 ∧ pdist z_{p'} z_p ≤ 8 ℓ^{lev p'} + 4 ℓ^{lev p}`, each row `p'` has at most
`9 (24 ℓ + 1)³` partners `p`, a `k`-free constant.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M2W6

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.StatementLane (Tower scaleUp pdist)
open AdalyFormal.BondComposite (hdvd_scaleUp)

section rows
variable {ell k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

open Classical in
theorem card_rows_near (hell : 0 < ell) (l : ℕ) (hl : l ≤ k) (c : PeriodicLatticeSite (scaleUp ell k Lu)) (m : ℕ) :
    (Finset.univ.filter (fun p : BIdx (geomOf ell k S) => (p.1 : ℕ) = l ∧ pdist p.2.1.1 c ≤ m)).card
      ≤ 3 * (2 * m / ell ^ l + 1) ^ 3 := by
  have hn : 0 < ell ^ l := pow_pos hell l
  have hdvd : ∀ ν : Fin 3, ell ^ l ∣ scaleUp ell k Lu ν + 1 := fun ν => hdvd_scaleUp ell k Lu hell l hl ν
  have hA := card_pball_aligned (ell ^ l) hn hdvd m c
  have hprod : (((Finset.univ.filter (fun y : PeriodicLatticeSite (scaleUp ell k Lu) =>
      (∀ ν, ell ^ l ∣ (y ν).val) ∧ pdist y c ≤ m)) ×ˢ (Finset.univ : Finset (Fin 3)))).card
      ≤ (2 * m / ell ^ l + 1) ^ 3 * 3 := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    exact Nat.mul_le_mul_right 3 hA
  have hinj : (Finset.univ.filter (fun p : BIdx (geomOf ell k S) => (p.1 : ℕ) = l ∧ pdist p.2.1.1 c ≤ m)).card
      ≤ (((Finset.univ.filter (fun y : PeriodicLatticeSite (scaleUp ell k Lu) =>
      (∀ ν, ell ^ l ∣ (y ν).val) ∧ pdist y c ≤ m)) ×ˢ (Finset.univ : Finset (Fin 3)))).card := by
    refine Finset.card_le_card_of_injOn (fun p : BIdx (geomOf ell k S) => (p.2.1.1, p.2.1.2)) ?_ ?_
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp
      rw [Finset.mem_coe, Finset.mem_product, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, fun ν => ?_, hp.2⟩, Finset.mem_univ _⟩
      have h2 := mem_CoarseLattice.mp (AdalyFormal.M1IMS.row_aligned (S := S) hell p) ν
      have h3 : ell ^ (p.1 : ℕ) = ell ^ l := by rw [hp.1]
      rw [h3] at h2
      exact Nat.dvd_of_mod_eq_zero h2
    · rintro ⟨j, ⟨b, hb⟩⟩ hp ⟨j2, ⟨b', hb'⟩⟩ hp' h
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp hp'
      simp only [Prod.mk.injEq] at h
      have hj : j = j2 := Fin.ext (by rw [hp.1, hp'.1])
      subst hj
      have : b = b' := Prod.ext h.1 h.2
      subst this
      rfl
  calc _ ≤ _ := hinj
    _ ≤ (2 * m / ell ^ l + 1) ^ 3 * 3 := hprod
    _ = 3 * (2 * m / ell ^ l + 1) ^ 3 := by ring

/-- the interaction relation: a target row `p'` and a source row `p` -/
def Inter (p' p : BIdx (geomOf ell k S)) : Prop :=
  (p.1 : ℕ) + 1 ≥ (p'.1 : ℕ) ∧ (p'.1 : ℕ) + 1 ≥ (p.1 : ℕ) ∧
    pdist p'.2.1.1 p.2.1.1 ≤ 8 * ell ^ (p'.1 : ℕ) + 4 * ell ^ (p.1 : ℕ)

open Classical in
theorem card_inter (hell : 0 < ell) (p' : BIdx (geomOf ell k S)) :
    (Finset.univ.filter (fun p : BIdx (geomOf ell k S) => Inter p' p)).card ≤ 9 * (24 * ell + 1) ^ 3 := by
  have hsub : (Finset.univ.filter (fun p : BIdx (geomOf ell k S) => Inter p' p))
      ⊆ (Finset.Icc ((p'.1 : ℕ) - 1) ((p'.1 : ℕ) + 1)).biUnion (fun l =>
          Finset.univ.filter (fun p : BIdx (geomOf ell k S) =>
            (p.1 : ℕ) = l ∧ pdist p.2.1.1 p'.2.1.1 ≤ 8 * ell ^ (p'.1 : ℕ) + 4 * ell ^ l)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨(p.1 : ℕ), ⟨by have := hp.1; omega, by have := hp.2.1; omega⟩, rfl, ?_⟩
    rw [AdalyFormal.StatementLaneR8.pdist_comm]
    exact hp.2.2
  refine (Finset.card_le_card hsub).trans ?_
  refine Finset.card_biUnion_le.trans ?_
  have hterm : ∀ l ∈ Finset.Icc ((p'.1 : ℕ) - 1) ((p'.1 : ℕ) + 1),
      (Finset.univ.filter (fun p : BIdx (geomOf ell k S) =>
        (p.1 : ℕ) = l ∧ pdist p.2.1.1 p'.2.1.1 ≤ 8 * ell ^ (p'.1 : ℕ) + 4 * ell ^ l)).card ≤ 3 * (24 * ell + 1) ^ 3 := by
    intro l hl
    rw [Finset.mem_Icc] at hl
    by_cases hlk : l ≤ k
    · refine (card_rows_near hell l hlk p'.2.1.1 _).trans ?_
      refine Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (Nat.add_le_add_right ?_ 1) 3)
      have hp : ell ^ (p'.1 : ℕ) ≤ ell * ell ^ l := by
        rw [← pow_succ']; exact Nat.pow_le_pow_right hell (by omega)
      have hq : ell ^ l * (24 * ell) ≥ 2 * (8 * ell ^ (p'.1 : ℕ) + 4 * ell ^ l) := by nlinarith [Nat.one_le_pow l ell hell]
      calc 2 * (8 * ell ^ (p'.1 : ℕ) + 4 * ell ^ l) / ell ^ l ≤ (ell ^ l * (24 * ell)) / ell ^ l :=
            Nat.div_le_div_right hq
        _ = 24 * ell := Nat.mul_div_cancel_left _ (pow_pos hell l)
    · -- no rows of level `l > k`
      have : (Finset.univ.filter (fun p : BIdx (geomOf ell k S) =>
          (p.1 : ℕ) = l ∧ pdist p.2.1.1 p'.2.1.1 ≤ 8 * ell ^ (p'.1 : ℕ) + 4 * ell ^ l)) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr (fun p _ => ?_)
        have : (p.1 : ℕ) ≤ k := Nat.lt_succ_iff.mp p.1.isLt
        omega
      rw [this]; simp
  calc ∑ l ∈ Finset.Icc ((p'.1 : ℕ) - 1) ((p'.1 : ℕ) + 1), _ ≤ ∑ l ∈ Finset.Icc ((p'.1 : ℕ) - 1) ((p'.1 : ℕ) + 1), 3 * (24 * ell + 1) ^ 3 :=
        Finset.sum_le_sum hterm
    _ = (Finset.Icc ((p'.1 : ℕ) - 1) ((p'.1 : ℕ) + 1)).card * (3 * (24 * ell + 1) ^ 3) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 3 * (3 * (24 * ell + 1) ^ 3) := Nat.mul_le_mul_right _ (by rw [Nat.card_Icc]; omega)
    _ = 9 * (24 * ell + 1) ^ 3 := by ring

end rows

end AdalyFormal.M2W6

#print axioms AdalyFormal.M2W6.card_rows_near
#print axioms AdalyFormal.M2W6.card_inter
