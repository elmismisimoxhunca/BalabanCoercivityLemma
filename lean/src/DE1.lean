import DD

/-!
# DE1 -- abstract constraint classes (cubes) and the class-sum identities (m1_w2_decay, 2026-10-13)

`Classes L B ell` : a partition of the sites into cubes `blockOf (anc x) (nn x)` with sides `B ≤ nn ≤ ell·B`, fitting in the torus.
* `cls x` (the class of `x`, as a `Finset`), `cls_eq_block`, `card_cls` (`= nn x ^ 3`), `pdist_anc` (`|anc x − z| ≤ 3 nn x` on the class);
* `sum_cls_swap` : `Σ_x w(x) Σ_{z ∈ cls x} F z = Σ_z F z · Σ_{x ∈ cls z} w x` (double counting);
* **`sum_anc_zero`** : if `μ` has zero class sums and `Δh` is constant on every class where `γ ∘ anc ≠ 0`, then
  `Σ_x ⟪Δh x, γ(anc x) μ x⟫ = 0`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M1Decay

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (pdist pcd)
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf)

variable {L : PeriodicLatticeExtent}

/-- a partition of the torus into cubes of sides between `B` and `ell·B`. -/
structure Classes (L : PeriodicLatticeExtent) (B ell : ℕ) where
  anc : PeriodicLatticeSite L → PeriodicLatticeSite L
  nn : PeriodicLatticeSite L → ℕ
  nn_ge : ∀ x, B ≤ nn x
  nn_le : ∀ x, nn x ≤ ell * B
  mem : ∀ x z, anc z = anc x ↔ z ∈ blockOf (anc x) (nn x)
  fit : ∀ x μ, (anc x μ).val + nn x ≤ L μ + 1
  nn_eq : ∀ x z, anc z = anc x → nn z = nn x

namespace Classes
variable {B ell : ℕ} (Cl : Classes L B ell)

/-- the class of `x`. -/
def cls (x : PeriodicLatticeSite L) : Finset (PeriodicLatticeSite L) :=
  Finset.univ.filter (fun z => Cl.anc z = Cl.anc x)

theorem mem_cls (x z : PeriodicLatticeSite L) : z ∈ Cl.cls x ↔ Cl.anc z = Cl.anc x := by
  simp [cls]

theorem cls_eq_block (x : PeriodicLatticeSite L) : Cl.cls x = blockOf (Cl.anc x) (Cl.nn x) := by
  ext z; rw [mem_cls]; exact Cl.mem x z

theorem self_mem (x : PeriodicLatticeSite L) : x ∈ Cl.cls x := (Cl.mem_cls x x).mpr rfl

theorem card_cls (x : PeriodicLatticeSite L) : ((Cl.cls x).card : ℝ) = (Cl.nn x : ℝ) ^ 3 := by
  rw [cls_eq_block, AdalyFormal.M1Site.card_blockOf _ _ (Cl.fit x)]; push_cast; ring

theorem pdist_anc (x z : PeriodicLatticeSite L) (hz : z ∈ Cl.cls x) : pdist (Cl.anc x) z ≤ 3 * Cl.nn x := by
  rw [cls_eq_block, mem_blockOf] at hz
  unfold pdist
  rw [Fin.sum_univ_three]
  have h : ∀ μ, pcd (L μ + 1) (Cl.anc x μ).val (z μ).val ≤ Cl.nn x := by
    intro μ
    exact (AdalyFormal.StatementLaneR8.pcd_le_diff _ _ _ (hz μ).1).trans (by have := (hz μ).2; omega)
  have := h 0; have := h 1; have := h 2
  omega

theorem pdist_self_anc (x : PeriodicLatticeSite L) : pdist x (Cl.anc x) ≤ 3 * Cl.nn x := by
  rw [pdist_comm]; exact Cl.pdist_anc x x (Cl.self_mem x)

theorem pdist_in_cls (x z : PeriodicLatticeSite L) (hz : z ∈ Cl.cls x) : pdist x z ≤ 6 * Cl.nn x := by
  have h1 := pdist_triangle x (Cl.anc x) z
  have h2 := Cl.pdist_self_anc x
  have h3 := Cl.pdist_anc x z hz
  omega

theorem cls_symm (x z : PeriodicLatticeSite L) : z ∈ Cl.cls x ↔ x ∈ Cl.cls z := by
  rw [mem_cls, mem_cls]; exact eq_comm

theorem nn_cls (x z : PeriodicLatticeSite L) (hz : z ∈ Cl.cls x) : Cl.nn z = Cl.nn x :=
  Cl.nn_eq x z ((Cl.mem_cls x z).mp hz)

open Classical in
theorem sum_cls_swap (w F : PeriodicLatticeSite L → ℝ) :
    ∑ x, w x * ∑ z ∈ Cl.cls x, F z = ∑ z, F z * ∑ x ∈ Cl.cls z, w x := by
  have e1 : ∀ x, w x * ∑ z ∈ Cl.cls x, F z = ∑ z, if Cl.anc z = Cl.anc x then w x * F z else 0 := by
    intro x
    rw [Finset.mul_sum, cls, Finset.sum_filter]
  have e2 : ∀ z, F z * ∑ x ∈ Cl.cls z, w x = ∑ x, if Cl.anc z = Cl.anc x then w x * F z else 0 := by
    intro z
    rw [Finset.mul_sum, cls, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : Cl.anc x = Cl.anc z
    · rw [if_pos h, if_pos h.symm]; ring
    · rw [if_neg h, if_neg (fun e => h e.symm)]
  simp only [e1, e2]
  exact Finset.sum_comm

/-- the class-weighted double count with class-constant weights. -/
theorem sum_cls_const (p : ℕ → ℝ) (F : PeriodicLatticeSite L → ℝ) :
    ∑ x, p (Cl.nn x) * ∑ z ∈ Cl.cls x, F z = ∑ z, F z * (p (Cl.nn z) * (Cl.nn z : ℝ) ^ 3) := by
  rw [Cl.sum_cls_swap (fun x => p (Cl.nn x)) F]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  congr 1
  rw [Finset.sum_congr rfl (fun x hx => by rw [Cl.nn_cls z x hx]), Finset.sum_const, nsmul_eq_mul, Cl.card_cls]
  ring

/-- **zero class sums kill the class-constant part**. -/
theorem sum_anc_zero (μ k : SiteL2 L) (γ : PeriodicLatticeSite L → ℝ)
    (hsum : ∀ x, ∑ z ∈ Cl.cls x, μ z = 0)
    (hconst : ∀ x, γ (Cl.anc x) ≠ 0 → ∀ z ∈ Cl.cls x, k z = k x) :
    ∑ x, ⟪k x, γ (Cl.anc x) • μ x⟫ = 0 := by
  rw [← Finset.sum_fiberwise Finset.univ Cl.anc (fun x => ⟪k x, γ (Cl.anc x) • μ x⟫)]
  refine Finset.sum_eq_zero (fun y _ => ?_)
  by_cases hy : ∃ x0, Cl.anc x0 = y
  · obtain ⟨x0, rfl⟩ := hy
    have hf : (Finset.univ.filter (fun x => Cl.anc x = Cl.anc x0)) = Cl.cls x0 := rfl
    rw [hf]
    by_cases hg : γ (Cl.anc x0) = 0
    · refine Finset.sum_eq_zero (fun x hx => ?_)
      rw [(Cl.mem_cls x0 x).mp hx, hg, zero_smul, inner_zero_right]
    · have hk := hconst x0 hg
      rw [Finset.sum_congr rfl (fun x hx => by rw [hk x hx, (Cl.mem_cls x0 x).mp hx])]
      rw [← inner_sum, ← Finset.smul_sum, hsum x0, smul_zero, inner_zero_right]
  · push_neg at hy
    refine Finset.sum_eq_zero (fun x hx => ?_)
    exact absurd (Finset.mem_filter.mp hx).2 (hy x)

end Classes

end AdalyFormal.M1Decay

#print axioms AdalyFormal.M1Decay.Classes.card_cls
#print axioms AdalyFormal.M1Decay.Classes.pdist_in_cls
#print axioms AdalyFormal.M1Decay.Classes.sum_cls_swap
#print axioms AdalyFormal.M1Decay.Classes.sum_cls_const
#print axioms AdalyFormal.M1Decay.Classes.sum_anc_zero
