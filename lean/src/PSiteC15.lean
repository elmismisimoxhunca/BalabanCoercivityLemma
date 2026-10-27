import PSiteC14
import PSiteC7

/-!
# SiteC15 -- chains of centre sets down a tower, and the PROPER-TOWER (Dirichlet) site coercivity.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
namespace AdalyFormal.SiteCoercivity

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf stepAverage Qcomposite)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap gradValueCovariant)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobNorm_le_frobSupBond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.PoincareBridge (coarseLattice_fits)

variable {L : PeriodicLatticeExtent}

/-- the chain of centre sets obtained from the top set `Λ ⊆ Y_{ell^j}` by `upZ` -/
noncomputable def chainZ (ell : ℕ) : ℕ → Finset (PeriodicLatticeSite L) → ℕ → Finset (PeriodicLatticeSite L)
  | 0, Λ, _ => Λ
  | j + 1, Λ, i => if i = j + 1 then Λ else chainZ ell j (upZ (ell ^ j) ell Λ) i

theorem chainZ_top (ell : ℕ) : ∀ (j : ℕ) (Λ : Finset (PeriodicLatticeSite L)), chainZ ell j Λ j = Λ := by
  intro j
  cases j with
  | zero => intro Λ; rfl
  | succ j => intro Λ; simp [chainZ]

theorem chainZ_sub (ell : ℕ) : ∀ (j : ℕ) (Λ : Finset (PeriodicLatticeSite L)), Λ ⊆ CoarseLattice L (ell ^ j) →
    ∀ i, i ≤ j → chainZ ell j Λ i ⊆ CoarseLattice L (ell ^ i) := by
  intro j
  induction j with
  | zero =>
    intro Λ hΛ i hi
    have : i = 0 := by omega
    subst this; exact hΛ
  | succ j ih =>
    intro Λ hΛ i hi
    by_cases hij : i = j + 1
    · subst hij; simp only [chainZ, if_true]; exact hΛ
    · simp only [chainZ, if_neg hij]
      refine ih _ ?_ i (by omega)
      have h1 : Λ ⊆ CoarseLattice L (ell ^ j * ell) := by rwa [← pow_succ]
      exact upZ_subset_coarse h1

theorem chainZ_step (ell : ℕ) : ∀ (j : ℕ) (Λ : Finset (PeriodicLatticeSite L)), Λ ⊆ CoarseLattice L (ell ^ j) →
    ∀ i, i < j → chainZ ell j Λ i = upZ (ell ^ i) ell (chainZ ell j Λ (i + 1)) := by
  intro j
  induction j with
  | zero => intro Λ _ i hi; omega
  | succ j ih =>
    intro Λ hΛ i hi
    by_cases hij : i = j
    · subst hij
      have e1 : chainZ ell (i + 1) Λ (i + 1) = Λ := chainZ_top ell (i + 1) Λ
      have e2 : chainZ ell (i + 1) Λ i = upZ (ell ^ i) ell Λ := by
        simp only [chainZ, if_neg (show ¬ (i = i + 1) by omega)]
        exact chainZ_top ell i _
      rw [e1, e2]
    · have hlt : i < j := by omega
      have e1 : chainZ ell (j + 1) Λ i = chainZ ell j (upZ (ell ^ j) ell Λ) i := by
        simp only [chainZ, if_neg (show ¬ (i = j + 1) by omega)]
      have e2 : chainZ ell (j + 1) Λ (i + 1) = chainZ ell j (upZ (ell ^ j) ell Λ) (i + 1) := by
        simp only [chainZ, if_neg (show ¬ (i + 1 = j + 1) by omega)]
      rw [e1, e2]
      have h1 : Λ ⊆ CoarseLattice L (ell ^ j * ell) := by rwa [← pow_succ]
      exact ih _ (upZ_subset_coarse h1) i hlt

theorem chainZ_blocks (ell : ℕ) (hell : 0 < ell) : ∀ (j : ℕ) (Λ : Finset (PeriodicLatticeSite L)),
    Λ ⊆ CoarseLattice L (ell ^ j) → ∀ i, i ≤ j → ∀ c ∈ chainZ ell j Λ i,
      blockOf c (ell ^ i) ⊆ Λ.biUnion (fun y => blockOf y (ell ^ j)) := by
  intro j
  induction j with
  | zero =>
    intro Λ hΛ i hi c hc
    have : i = 0 := by omega
    subst this
    simp only [chainZ] at hc
    intro x hx
    rw [Finset.mem_biUnion]
    exact ⟨c, hc, hx⟩
  | succ j ih =>
    intro Λ hΛ i hi c hc
    by_cases hij : i = j + 1
    · subst hij
      simp only [chainZ, if_true] at hc
      intro x hx
      rw [Finset.mem_biUnion]
      exact ⟨c, hc, hx⟩
    · simp only [chainZ, if_neg hij] at hc
      have h1 : Λ ⊆ CoarseLattice L (ell ^ j * ell) := by rwa [← pow_succ]
      have hup := upZ_subset_coarse h1
      have key := ih _ hup i (by omega) c hc
      refine key.trans ?_
      intro x hx
      rw [Finset.mem_biUnion] at hx ⊢
      obtain ⟨c', hc', hxc'⟩ := hx
      unfold upZ at hc'
      rw [Finset.mem_biUnion] at hc'
      obtain ⟨y, hy, hc'y⟩ := hc'
      refine ⟨y, hy, ?_⟩
      have hbu := blockOf_biUnion (L := L) (y := y) (s := ell ^ j) (ell := ell) (pow_pos hell j)
      rw [← pow_succ] at hbu
      rw [← hbu, Finset.mem_biUnion]
      exact ⟨c', hc'y, hxc'⟩


open Classical in
/-- `Λ_j` as a finset -/
noncomputable def LamF (G : TowerGeom L) (j : ℕ) : Finset (PeriodicLatticeSite L) :=
  Finset.univ.filter (fun y => y ∈ G.Lam j)

theorem mem_LamF {G : TowerGeom L} {j : ℕ} {y : PeriodicLatticeSite L} : y ∈ LamF G j ↔ y ∈ G.Lam j := by
  simp [LamF]

/-- the geometric structure of a (proper, multi-level) tower that the print gives: `Ω₀ = ⊔_j B^j(Λ_j)`. -/
structure ProperTower (G : TowerGeom L) (ell k : ℕ) : Prop where
  ell_eq : G.ell = ell
  k_eq : G.k = k
  coarse : ∀ j, j ≤ k → ∀ y ∈ G.Lam j, y ∈ CoarseLattice L (ell ^ j)
  disj : ∀ j j', j ≤ k → j' ≤ k → ∀ y ∈ G.Lam j, ∀ y' ∈ G.Lam j', (j ≠ j' ∨ y ≠ y') →
    Disjoint (blockOf y (ell ^ j)) (blockOf y' (ell ^ j'))
  cover : ∀ x, x ∈ G.Om0 ↔ ∃ j, j ≤ k ∧ ∃ y ∈ G.Lam j, x ∈ blockOf y (ell ^ j)

/-- the level-`j` region -/
noncomputable def Rj (G : TowerGeom L) (ell j : ℕ) : Finset (PeriodicLatticeSite L) :=
  (LamF G j).biUnion (fun y => blockOf y (ell ^ j))

/-- the sigma index set of all blocks -/
noncomputable def IdxB (G : TowerGeom L) (k : ℕ) : Finset (Σ _ : ℕ, PeriodicLatticeSite L) :=
  (Finset.range (k + 1)).sigma (fun j => LamF G j)

theorem IdxB_disj {G : TowerGeom L} {ell k : ℕ} (hP : ProperTower G ell k) :
    ∀ p ∈ IdxB G k, ∀ q ∈ IdxB G k, p ≠ q → Disjoint (blockOf p.2 (ell ^ p.1)) (blockOf q.2 (ell ^ q.1)) := by
  rintro ⟨j, y⟩ hp ⟨j', y'⟩ hq hne
  simp only [IdxB, Finset.mem_sigma, Finset.mem_range, mem_LamF] at hp hq
  refine hP.disj j j' (by omega) (by omega) y hp.2 y' hq.2 ?_
  by_contra hcon
  push Not at hcon
  apply hne
  rw [hcon.1, hcon.2]

theorem sum_partition {G : TowerGeom L} {ell k : ℕ} (hP : ProperTower G ell k) (φ : PeriodicLatticeSite L → ℝ)
    (hφ : ∀ x, x ∉ G.Om0 → φ x = 0) :
    ∑ x, φ x = ∑ j ∈ Finset.range (k + 1), ∑ y ∈ LamF G j, ∑ x ∈ blockOf y (ell ^ j), φ x := by
  rw [Finset.sum_sigma' (Finset.range (k + 1)) (fun j => LamF G j)
    (fun j y => ∑ x ∈ blockOf y (ell ^ j), φ x)]
  have hb := Finset.sum_biUnion (s := IdxB G k) (t := fun p => blockOf p.2 (ell ^ p.1)) (f := φ)
    (by
      intro p hp q hq hne
      exact IdxB_disj hP p hp q hq hne)
  unfold IdxB at hb
  rw [← hb]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro x _ hx
  apply hφ
  intro hxR
  apply hx
  rw [hP.cover] at hxR
  obtain ⟨j, hj, y, hy, hxy⟩ := hxR
  rw [Finset.mem_biUnion]
  exact ⟨⟨j, y⟩, by simp [IdxB, mem_LamF, hy, Nat.lt_succ_of_le hj], hxy⟩

theorem sum_blockbonds_le {G : TowerGeom L} {ell k : ℕ} (hP : ProperTower G ell k) (φ : Bond L → ℝ)
    (hφ : ∀ b, 0 ≤ φ b) :
    ∑ j ∈ Finset.range (k + 1), ∑ y ∈ LamF G j, ∑ b ∈ inBlockBonds y (ell ^ j), φ b ≤ ∑ b, φ b := by
  rw [Finset.sum_sigma' (Finset.range (k + 1)) (fun j => LamF G j)
    (fun j y => ∑ b ∈ inBlockBonds y (ell ^ j), φ b)]
  have hb := Finset.sum_biUnion (s := IdxB G k) (t := fun p => inBlockBonds p.2 (ell ^ p.1)) (f := φ)
    (by
      intro p hp q hq hne
      exact inBlockBonds_disjoint (IdxB_disj hP p hp q hq hne))
  unfold IdxB at hb
  rw [← hb]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => hφ b)


theorem blocks_disj_level {G : TowerGeom L} {ell k : ℕ} (hP : ProperTower G ell k) {j : ℕ} (hj : j ≤ k) :
    ∀ y ∈ LamF G j, ∀ y' ∈ LamF G j, y ≠ y' → Disjoint (blockOf y (ell ^ j)) (blockOf y' (ell ^ j)) := by
  intro y hy y' hy' hne
  rw [mem_LamF] at hy hy'
  exact hP.disj j j hj hj y hy y' hy' (Or.inr hne)

theorem sum_Rj {G : TowerGeom L} {ell k : ℕ} (hP : ProperTower G ell k) {j : ℕ} (hj : j ≤ k)
    (φ : PeriodicLatticeSite L → ℝ) :
    ∑ x ∈ Rj G ell j, φ x = ∑ y ∈ LamF G j, ∑ x ∈ blockOf y (ell ^ j), φ x := by
  unfold Rj
  rw [Finset.sum_biUnion]
  intro y hy y' hy' hne
  exact blocks_disj_level hP hj y hy y' hy' hne

/-- the level-`j` data: block Poincaré + local telescoping -/
theorem level_data (ell k : ℕ) (hell : 2 ≤ ell) (hdvd : ∀ μ, ell ^ k ∣ L μ + 1)
    {G : TowerGeom L} (hP : ProperTower G ell k) (U : Cfg L) (δ : ℕ → ℝ) (hδ0 : ∀ i, 0 ≤ δ i)
    (hT : ∀ i, i < k → ∀ z ∈ G.Om0, ∀ μ : Fin 3,
      frobNorm ((bgTower G U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ δ i)
    {j : ℕ} (hj : j ≤ k) (E : ℝ) (hE : ∑ i ∈ Finset.range j, 6 * ((ell : ℝ) - 1) * δ i ≤ E)
    (g : PeriodicLatticeSite L → SuTwo) :
    (∑ x ∈ Rj G ell j, ‖g x‖ ^ 2
      ≤ 3 * ((ell : ℝ) ^ j) ^ 2 * ∑ y ∈ LamF G j, ∑ b ∈ inBlockBonds y (ell ^ j),
            ‖g (periodicLatticeShift b.1 b.2) - g b.1‖ ^ 2
        + 2 * NsZ (ell ^ j) (LamF G j) (Qcomposite (fun _ => trivialU L) ell j g) ^ 2)
    ∧ NsZ (ell ^ j) (LamF G j) (Qcomposite (fun _ => trivialU L) ell j g)
        ≤ NsZ (ell ^ j) (LamF G j) (Qcomposite (bgTower G U) ell j g) + E * NsZ 1 (Rj G ell j) g := by
  have hell0 : 0 < ell := by omega
  have hdvdj : ∀ μ, ell ^ j ∣ L μ + 1 := fun μ => Dvd.dvd.trans (pow_dvd_pow ell hj) (hdvd μ)
  have hLY : LamF G j ⊆ CoarseLattice L (ell ^ j) := fun y hy => hP.coarse j hj y (mem_LamF.mp hy)
  have hncast : (((ell ^ j : ℕ)) : ℝ) = (ell : ℝ) ^ j := by push_cast; rfl
  constructor
  · -- Poincare
    rw [sum_Rj hP hj]
    have hp : ∀ y ∈ LamF G j, ∑ x ∈ blockOf y (ell ^ j), ‖g x‖ ^ 2 ≤
        3 * ((ell : ℝ) ^ j) ^ 2 * ∑ b ∈ inBlockBonds y (ell ^ j), ‖g (periodicLatticeShift b.1 b.2) - g b.1‖ ^ 2
          + 2 * (((ell : ℝ) ^ j) ^ 3 * ‖Qcomposite (fun _ => trivialU L) ell j g y‖ ^ 2) := by
      intro y hy
      have hfit := coarseLattice_fits hdvdj (hLY hy)
      have h := block_poincare_vector (pow_pos hell0 j) hfit g
      rw [hncast] at h
      have hF := Qflat_eq_blockMean ell hell0 g j y (hLY hy)
      rw [hF]
      simp only [hncast]
      nlinarith [h]
    have hs := Finset.sum_le_sum hp
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
    have hN := NsZ_sq (ell ^ j) (LamF G j) (Qcomposite (fun _ => trivialU L) ell j g)
    rw [hncast] at hN
    rw [hN]
    linarith [hs]
  · -- telescoping
    have hZc := chainZ_sub ell j (LamF G j) hLY
    have hchain := chainZ_step ell j (LamF G j) hLY
    have htel := NsZ_telescope_local ell hell0 (bgTower G U) δ hδ0 j (chainZ ell j (LamF G j))
      (fun i hi => hZc i hi) (fun i hi => hchain i hi)
      (by
        intro i hi y hy μ
        have hy' := hZc (i + 1) (by omega) hy
        have hdv : ∀ ν, ell ^ (i + 1) ∣ L ν + 1 := fun ν =>
          Dvd.dvd.trans (pow_dvd_pow ell (by omega : i + 1 ≤ k)) (hdvd ν)
        have := coarseLattice_fits hdv hy' μ
        rwa [pow_succ] at this)
      (by
        intro i hi y hy z hz μ
        have hy' := hZc (i + 1) (by omega) hy
        have hblk := chainZ_blocks ell hell0 j (LamF G j) hLY (i + 1) (by omega) y hy
        have hz' : z ∈ blockOf y (ell ^ (i + 1)) := by rwa [pow_succ]
        have hzR := hblk hz'
        rw [Finset.mem_biUnion] at hzR
        obtain ⟨y0, hy0, hzy0⟩ := hzR
        have hzOm : z ∈ G.Om0 := by
          rw [hP.cover]
          exact ⟨j, hj, y0, mem_LamF.mp hy0, hzy0⟩
        exact hT i (by omega) z hzOm μ)
      g j le_rfl
    rw [chainZ_top] at htel
    have hmono : NsZ 1 (chainZ ell j (LamF G j) 0) g ≤ NsZ 1 (Rj G ell j) g := by
      refine NsZ_mono 1 ?_ g
      intro c hc
      have hblk := chainZ_blocks ell hell0 j (LamF G j) hLY 0 (Nat.zero_le j) c hc
      have hcb : c ∈ blockOf c (ell ^ 0) := by
        rw [mem_blockOf]; intro μ; simp
      exact hblk hcb
    have hE0 : 0 ≤ E := by
      refine le_trans ?_ hE
      refine Finset.sum_nonneg (fun i _ => ?_)
      have hℓ1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell0
      have : (0 : ℝ) ≤ (ell : ℝ) - 1 := by linarith
      have := hδ0 i
      positivity
    set Q : PeriodicLatticeSite L → SuTwo := Qcomposite (bgTower G U) ell j g with hQ
    set F : PeriodicLatticeSite L → SuTwo := Qcomposite (fun _ => trivialU L) ell j g with hF
    have hFeq : F = Q - (Q - F) := by abel
    have hsum0 : 0 ≤ ∑ i ∈ Finset.range j, 6 * ((ell : ℝ) - 1) * δ i := by
      refine Finset.sum_nonneg (fun i _ => ?_)
      have hℓ1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell0
      have : (0 : ℝ) ≤ (ell : ℝ) - 1 := by linarith
      have := hδ0 i
      positivity
    calc NsZ (ell ^ j) (LamF G j) F = NsZ (ell ^ j) (LamF G j) (Q - (Q - F)) := by rw [← hFeq]
      _ ≤ NsZ (ell ^ j) (LamF G j) Q + NsZ (ell ^ j) (LamF G j) (Q - F) := NsZ_sub_le _ _ _ _
      _ ≤ NsZ (ell ^ j) (LamF G j) Q + (∑ i ∈ Finset.range j, 6 * ((ell : ℝ) - 1) * δ i) * NsZ 1 (chainZ ell j (LamF G j) 0) g := by
          linarith [htel]
      _ ≤ NsZ (ell ^ j) (LamF G j) Q + E * NsZ 1 (Rj G ell j) g := by
          have h1 : (∑ i ∈ Finset.range j, 6 * ((ell : ℝ) - 1) * δ i) * NsZ 1 (chainZ ell j (LamF G j) 0) g
              ≤ E * NsZ 1 (Rj G ell j) g :=
            mul_le_mul hE hmono (NsZ_nonneg _ _ _) hE0
          linarith

end AdalyFormal.SiteCoercivity
