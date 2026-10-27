import W2C1

/-!
# W2C2 -- the real tower against the patch tower on a region `Z` (M1 lane W2, 2026-10-13)

Setting: `S` admissible (`ell, M, R, k`), room `17 ell ≤ R M`, a level `i` with `i + 1 ≤ k`, the comparison tower
`S₂ = patchTower i (Ω_{i+1})` ON THE SAME TORUS (height `i + 1`), and a region `Z` with `Z ⊆ Ω_i`, `Z ∩ Ω_{i+2} = ∅`
(on `Z` every stratum is `i` or `i + 1`).  "Deep" = the ball of radius `32 ell^{i+2}` lies in `Z`.
* `towerAgree` : on `Z` the two towers have the same `Ω_m` for every `m`;
* **`lam_near`** : a real level-`m` constraint site within `9 ell^m` of a deep point has `m = i` or `m = i + 1`
  (low levels are excluded by `Z ⊆ Ω_i`, level `i+2` by `Z ∩ Ω_{i+2} = ∅`, levels `≥ i+3` by the collar of `Admissible`);
* `lam_agree`, `bondsLam_agree` : on `Z` the constraint sites / constraint bonds of the two towers coincide;
* `wnorm_agree` : the stratum weights agree on fields supported near deep points.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M1W2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower BlockClosed Admissible bigSide pdist)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.StatementLaneR8 (Ball mem_Ball_self Ball_sub Ball_mono rhoT rhoT_le rhoT_mono pdist_comm pdist_triangle
  pdist_self pdist_coarseShift_le pdist_shift_le admissible_ball)
open AdalyFormal.M1Patch (patchTower om_le om_succ om_gt)

variable {L : PeriodicLatticeExtent}

/-- `Admissible` blocks of `Ω_j` (side `M ell^j`) are unions of `ell^j` blocks. -/
theorem blockClosed_of_mul {s t : ℕ} {X : Set (PeriodicLatticeSite L)} (h : BlockClosed (t * s) X) :
    BlockClosed s X := by
  intro x hx y hy
  refine h x hx y (fun μ => ?_)
  rw [Nat.mul_comm t s, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hy μ]

section region
variable {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M)
  {i : ℕ} (hik : i + 1 ≤ k) {Z : Set (PeriodicLatticeSite L)} (hZi : Z ⊆ S.Om i) (hZ2 : ∀ z ∈ Z, z ∉ S.Om (i + 2))

include hS hZi hZ2 in
theorem towerAgree (z : PeriodicLatticeSite L) (hz : z ∈ Z) (m : ℕ) :
    z ∈ S.Om m ↔ z ∈ (patchTower i (S.Om (i + 1))).Om m := by
  rcases Nat.lt_or_ge (i + 1) m with hgt | hle
  · rw [om_gt i _ hgt]
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hm
    exact hZ2 z hz (AdalyFormal.M1.om_anti hS (show i + 2 ≤ m by omega) hm)
  · rcases Nat.eq_or_lt_of_le hle with e | hlt
    · subst e; rw [om_succ]
    · rw [om_le i _ (by omega : m ≤ i)]
      simp only [Set.mem_univ, iff_true]
      exact AdalyFormal.M1.om_anti hS (show m ≤ i by omega) (hZi hz)

include hS hell hroom hZi hZ2 in
/-- **constraint sites near a deep point live on levels `i`, `i+1`.** -/
theorem lam_near (x : PeriodicLatticeSite L) (hx : Ball x (32 * ell ^ (i + 2)) ⊆ Z) (m : ℕ) (hm : m ≤ k)
    (y : PeriodicLatticeSite L) (hy : y ∈ (geomOf ell k S).Lam m) (hxy : pdist x y ≤ 9 * ell ^ m) :
    m = i ∨ m = i + 1 := by
  have hell1 : 1 ≤ ell := by omega
  obtain ⟨-, hyOm, hyOm1⟩ := hy
  rcases Nat.lt_or_ge m i with hlt | hge
  · -- low level: y ∈ Z ⊆ Ω_i ⊆ Ω_{m+1}
    exfalso
    have hp : 9 * ell ^ m ≤ 32 * ell ^ (i + 2) := by
      have := Nat.pow_le_pow_right hell1 (show m ≤ i + 2 by omega); omega
    have hyZ : y ∈ Z := hx (le_trans hxy hp)
    exact hyOm1 (AdalyFormal.M1.om_anti hS (show m + 1 ≤ i by omega) (hZi hyZ))
  · rcases Nat.lt_or_ge (i + 1) m with hgt | hle
    · exfalso
      rcases Nat.eq_or_lt_of_le hgt with e | hgt2
      · -- m = i + 2
        have hm2 : m = i + 2 := by omega
        subst hm2
        have hyZ : y ∈ Z := hx (show pdist x y ≤ 32 * ell ^ (i + 2) by omega)
        exact hZ2 y hyZ hyOm
      · -- m ≥ i + 3: collar at level m - 1
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        have hball := admissible_ball hS (j := m') (by omega) hyOm
        have hxin : x ∈ Ball y (R * bigSide M ell m') := by
          show pdist y x ≤ R * bigSide M ell m'
          rw [pdist_comm]
          refine le_trans hxy ?_
          unfold bigSide
          rw [pow_succ]
          have hp : 0 < ell ^ m' := pow_pos (by omega) m'
          nlinarith
        have hxm := hball hxin
        exact hZ2 x (hx (mem_Ball_self _ _)) (AdalyFormal.M1.om_anti hS (show i + 2 ≤ m' by omega) hxm)
    · omega

include hS hZi hZ2 in
theorem lam_agree (y : PeriodicLatticeSite L) (hy : y ∈ Z) (m : ℕ) :
    y ∈ (geomOf ell k S).Lam m ↔ y ∈ (geomOf ell (i + 1) (patchTower i (S.Om (i + 1)))).Lam m := by
  show ((∀ μ : Fin 3, ell ^ m ∣ (y μ).val) ∧ y ∈ S.Om m ∧ y ∉ S.Om (m + 1)) ↔
    ((∀ μ : Fin 3, ell ^ m ∣ (y μ).val) ∧ y ∈ (patchTower i (S.Om (i + 1))).Om m ∧
      y ∉ (patchTower i (S.Om (i + 1))).Om (m + 1))
  rw [towerAgree hS hZi hZ2 y hy m, towerAgree hS hZi hZ2 y hy (m + 1)]

include hS hell hik hZi hZ2 in
theorem omGe_agree (y : PeriodicLatticeSite L) (hy : y ∈ Z) (m : ℕ) (hm : 1 ≤ m) :
    OmGe (geomOf ell k S) m y ↔ OmGe (geomOf ell (i + 1) (patchTower i (S.Om (i + 1)))) m y := by
  have hRg : BlockClosed (ell ^ (i + 1)) (S.Om (i + 1)) :=
    blockClosed_of_mul (by
      have := hS.2.2.2.1 (i + 1) hik
      unfold bigSide at this; exact this)
  rw [omGe_iff_om ell M R k (by omega) S hS m y, omGe_patch_iff (by omega) hRg m hm y]
  exact towerAgree hS hZi hZ2 y hy m

include hS hell hik hZi hZ2 in
theorem bondsLam_agree (m : ℕ) (b : Bond L) (h1 : b.1 ∈ Z) (h2 : coarseShift b.1 (ell ^ m) b.2 ∈ Z) :
    b ∈ bondsLam (geomOf ell k S) m ↔ b ∈ bondsLam (geomOf ell (i + 1) (patchTower i (S.Om (i + 1)))) m := by
  show ((b.1 ∈ (geomOf ell k S).Lam m ∨ coarseShift b.1 ((geomOf ell k S).ell ^ m) b.2 ∈ (geomOf ell k S).Lam m) ∧
      ¬ (OmGe (geomOf ell k S) (m + 1) b.1 ∨ OmGe (geomOf ell k S) (m + 1) (coarseShift b.1 ((geomOf ell k S).ell ^ m) b.2))) ↔
    ((b.1 ∈ (geomOf ell (i + 1) (patchTower i (S.Om (i + 1)))).Lam m ∨
        coarseShift b.1 (ell ^ m) b.2 ∈ (geomOf ell (i + 1) (patchTower i (S.Om (i + 1)))).Lam m) ∧
      ¬ (OmGe (geomOf ell (i + 1) (patchTower i (S.Om (i + 1)))) (m + 1) b.1 ∨
        OmGe (geomOf ell (i + 1) (patchTower i (S.Om (i + 1)))) (m + 1) (coarseShift b.1 (ell ^ m) b.2)))
  have e : (geomOf ell k S).ell = ell := rfl
  rw [e, lam_agree hS hZi hZ2 b.1 h1 m, lam_agree hS hZi hZ2 _ h2 m,
    omGe_agree hS hell hik hZi hZ2 b.1 h1 (m + 1) (by omega),
    omGe_agree hS hell hik hZi hZ2 _ h2 (m + 1) (by omega)]

include hS hik hZi hZ2 in
theorem strat_agree (z : PeriodicLatticeSite L) (hz : z ∈ Z) :
    AdalyFormal.M1.strat S k z = AdalyFormal.M1.strat (patchTower i (S.Om (i + 1))) (i + 1) z :=
  strat_eq_of_agree S _ k (i + 1) hik z (towerAgree hS hZi hZ2 z hz)
    (fun m hm => by rw [om_gt i _ hm]; exact fun h => h)

include hS hik hZi hZ2 in
theorem wnorm_agree (A : BondFnL2 L)
    (hA : ∀ b : Bond L, (WithLp.ofLp A) b ≠ 0 → b.1 ∈ Z ∧ periodicLatticeShift b.1 b.2 ∈ Z) :
    AdalyFormal.M1.wnormSq S ell k A = AdalyFormal.M1.wnormSq (patchTower i (S.Om (i + 1))) ell (i + 1) A := by
  unfold AdalyFormal.M1.wnormSq
  refine Finset.sum_congr rfl (fun b _ => ?_)
  by_cases h0 : (WithLp.ofLp A) b = 0
  · rw [h0, norm_zero]; ring
  · obtain ⟨h1, h2⟩ := hA b h0
    unfold AdalyFormal.M1.bstrat
    rw [strat_agree hS hik hZi hZ2 _ h1, strat_agree hS hik hZi hZ2 _ h2]

end region

end AdalyFormal.M1W2

#print axioms AdalyFormal.M1W2.blockClosed_of_mul
#print axioms AdalyFormal.M1W2.towerAgree
#print axioms AdalyFormal.M1W2.lam_near
#print axioms AdalyFormal.M1W2.lam_agree
#print axioms AdalyFormal.M1W2.omGe_agree
#print axioms AdalyFormal.M1W2.bondsLam_agree
#print axioms AdalyFormal.M1W2.strat_agree
#print axioms AdalyFormal.M1W2.wnorm_agree
