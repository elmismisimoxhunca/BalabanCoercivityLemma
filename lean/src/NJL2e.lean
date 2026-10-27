import NJL2d

/-!
# NJL2e -- the FAMILY BOUND.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.NonflatJet

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLatticeEdge)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)

variable {L : PeriodicLatticeExtent}

/-- rows are (coarse base point, direction): sum over rows ≤ sum over all base points and directions. -/
theorem sum_rows_le {n : ℕ} (F : PeriodicLatticeSite L → Fin 3 → ℝ) (hF : ∀ y μ, 0 ≤ F y μ) :
    ∑ c : CoarseBond L n, F c.1.1 c.2 ≤ ∑ μ : Fin 3, ∑ y : PeriodicLatticeSite L, F y μ := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_le_sum (fun μ _ => ?_)
  have : ∑ y : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L n}, F y.1 μ
      = ∑ y ∈ Finset.univ.filter (fun z : PeriodicLatticeSite L => z ∈ CoarseLattice L n), F y μ :=
    (Finset.sum_subtype (Finset.univ.filter (fun z : PeriodicLatticeSite L => z ∈ CoarseLattice L n))
      (by simp) (fun y => F y μ)).symm
  rw [this]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun y _ _ => hF y μ)

theorem fam_bound {ell : ℕ} (g : PeriodicLatticeEdge L → ℝ) (hg : ∀ e, 0 ≤ g e) (m : ℕ)
    (a : PeriodicLatticeSite L → Fin 3 → PeriodicLatticeSite L)
    (q : PeriodicLatticeSite L → Fin 3 → List (Fin 3))
    (hq : ∀ d ∈ Doff L ell, ∀ μ, (q d μ).length ≤ m) :
    ∑ c : CoarseBond L (1 * ell), ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1,
        pathSum g (c.1.1 + a (u.1 - c.1.1) c.2) (q (u.1 - c.1.1) c.2)
      ≤ 3 * (ell : ℝ) ^ 3 * m * l1 g := by
  have hps : ∀ y d μ, 0 ≤ pathSum g (y + a d μ) (q d μ) := by
    intro y d μ
    unfold pathSum
    exact List.sum_nonneg (fun x hx => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
      exact hg e)
  have h1 : ∀ c : CoarseBond L (1 * ell), ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1,
        pathSum g (c.1.1 + a (u.1 - c.1.1) c.2) (q (u.1 - c.1.1) c.2)
      ≤ ∑ d ∈ Doff L ell, pathSum g (c.1.1 + a d c.2) (q d c.2) := fun c =>
    sum_block_le_sum_D (F := fun d => pathSum g (c.1.1 + a d c.2) (q d c.2)) c.1.1
      (fun d => hps _ d _)
  refine le_trans (Finset.sum_le_sum (fun c _ => h1 c)) ?_
  refine le_trans (sum_rows_le (fun y μ => ∑ d ∈ Doff L ell, pathSum g (y + a d μ) (q d μ))
    (fun y μ => Finset.sum_nonneg (fun d _ => hps y d μ))) ?_
  have h2 : ∀ μ : Fin 3, ∑ y : PeriodicLatticeSite L, ∑ d ∈ Doff L ell, pathSum g (y + a d μ) (q d μ)
      ≤ (Doff L ell).card * (m * l1 g) := by
    intro μ
    rw [Finset.sum_comm]
    have : ∀ d ∈ Doff L ell, ∑ y : PeriodicLatticeSite L, pathSum g (y + a d μ) (q d μ) ≤ m * l1 g := by
      intro d hd
      refine le_trans (sum_pathSum_translate g hg (a d μ) (q d μ)) ?_
      have hl1 : 0 ≤ l1 g := Finset.sum_nonneg (fun e _ => hg e)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hq d hd μ) hl1
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ this) ?_
    rw [nsmul_eq_mul]
  refine le_trans (Finset.sum_le_sum (fun μ _ => h2 μ)) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hD : ((Doff L ell).card : ℝ) ≤ (ell : ℝ) ^ 3 := by exact_mod_cast card_Doff_le ell
  have hl1 : 0 ≤ l1 g := Finset.sum_nonneg (fun e _ => hg e)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  push_cast
  nlinarith [mul_nonneg hm hl1, mul_le_mul_of_nonneg_right hD (mul_nonneg hm hl1)]

#print axioms fam_bound

end AdalyFormal.NonflatJet
