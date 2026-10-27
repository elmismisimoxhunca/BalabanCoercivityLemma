import FE5
import NJE8
import NJ20c

/-!
# BC2 -- geometry for the bond-composite drift

* `sum_embE`: sums over the level-`(s·m)` aligned bonds of the fine torus = sums over the `m`-aligned bonds of the
  `s`-sublattice torus `Lq` (the embedding `embE` of the nonflat-jet lane is a bijection onto the aligned bonds).
* `T1_flat_l2`: SHARP volume-free `L²` bound of the FLAT covariant main term, `Σ_c ‖T1(1)A(c)‖² ≤ ell^-3 ‖A‖²`
  (the lane-internal `sum_x2` bound has constant 3, no decay in `ell`; the decay `ell^-3` is what makes the
  level recursion geometric).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.BondComposite

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLatticeEdge PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice blockOf mem_blockOf)
open AdalyFormal.Balaban.StridedAveraging (mem_coarseLattice_one)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.TowerLawCov (unitToCoarseCov unitToCoarseCov_trivialU)
open AdalyFormal.Balaban.ThirdLevelArrows (unitToCoarse)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2 (XS)
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L Lq : PeriodicLatticeExtent} {s : ℕ}

section emb

theorem embS_surj (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (z : PeriodicLatticeSite L)
    (hz : ∀ μ, s ∣ (z μ).val) : ∃ y : PeriodicLatticeSite Lq, embS hs y = z := by
  have hs0 := s_pos_of hs
  have hlt : ∀ μ, (z μ).val / s < Lq μ + 1 := by
    intro μ
    exact Nat.div_lt_of_lt_mul (lt_of_lt_of_eq (z μ).isLt (hs μ))
  refine ⟨fun μ => ⟨(z μ).val / s, hlt μ⟩, ?_⟩
  funext μ
  apply Fin.ext
  show s * ((z μ).val / s) = (z μ).val
  exact Nat.mul_div_cancel' (hz μ)

/-- the embedding of `m`-aligned bonds of `Lq` into `(s·m)`-aligned bonds of `L`. -/
def embCB (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (m : ℕ) (c : CoarseBond Lq m) : CoarseBond L (s * m) :=
  (⟨embS hs c.1.1, mem_CoarseLattice.mpr (fun μ => by
      have h := mem_CoarseLattice.mp c.1.2 μ
      rw [embS_val]
      exact Nat.mod_eq_zero_of_dvd (Nat.mul_dvd_mul_left s (Nat.dvd_of_mod_eq_zero h)))⟩, c.2)

theorem embCB_bijective (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (m : ℕ) : Function.Bijective (embCB hs m) := by
  have hs0 := s_pos_of hs
  constructor
  · intro c c' h
    have h1 : embS hs c.1.1 = embS hs c'.1.1 := congrArg (fun d : CoarseBond L (s * m) => d.1.1) h
    have h2 : c.2 = c'.2 := congrArg (fun d : CoarseBond L (s * m) => d.2) h
    exact Prod.ext (Subtype.ext (embS_injective hs h1)) h2
  · intro c'
    have hz : ∀ μ, s * m ∣ (c'.1.1 μ).val := fun μ =>
      Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp c'.1.2 μ)
    obtain ⟨y, hy⟩ := embS_surj hs c'.1.1 (fun μ => dvd_trans (Dvd.intro m rfl) (hz μ))
    have hym : y ∈ CoarseLattice Lq m := by
      rw [mem_CoarseLattice]
      intro μ
      have h1 := hz μ
      rw [← hy, embS_val] at h1
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mul_dvd_mul_left hs0 h1)
    refine ⟨(⟨y, hym⟩, c'.2), ?_⟩
    exact Prod.ext (Subtype.ext hy) rfl

theorem sum_embE (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (m : ℕ) (g : PeriodicLatticeEdge L → ℝ) :
    ∑ c : CoarseBond Lq m, g (embE hs (c.1.1, c.2)) = ∑ c : CoarseBond L (s * m), g (c.1.1, c.2) :=
  Fintype.sum_bijective (embCB hs m) (embCB_bijective hs m) _ _ (fun c => rfl)

theorem sum_edge_eq_coarse1 (h : PeriodicLatticeEdge Lq → ℝ) :
    ∑ e : PeriodicLatticeEdge Lq, h e = ∑ c : CoarseBond Lq 1, h (c.1.1, c.2) := by
  refine (Fintype.sum_bijective (fun c : CoarseBond Lq 1 => ((c.1.1, c.2) : PeriodicLatticeEdge Lq))
    ⟨?_, ?_⟩ _ _ (fun c => rfl)).symm
  · intro c c' hc
    have hc' : ((c.1.1, c.2) : PeriodicLatticeEdge Lq) = (c'.1.1, c'.2) := hc
    obtain ⟨h1, h2⟩ := Prod.mk.inj hc'
    exact Prod.ext (Subtype.ext h1) h2
  · intro e
    exact ⟨(⟨e.1, mem_coarseLattice_one e.1⟩, e.2), rfl⟩

theorem sum_embE_edge (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (g : PeriodicLatticeEdge L → ℝ) :
    ∑ e : PeriodicLatticeEdge Lq, g (embE hs e) = ∑ c : CoarseBond L (s * 1), g (c.1.1, c.2) := by
  rw [sum_edge_eq_coarse1 (fun e => g (embE hs e))]
  exact sum_embE hs 1 g

end emb

section flatT1

theorem blocks_disjoint {ell : ℕ} (hell : 0 < ell) (y1 y2 : PeriodicLatticeSite L)
    (h1 : y1 ∈ CoarseLattice L ell) (h2 : y2 ∈ CoarseLattice L ell) (hne : y1 ≠ y2) :
    Disjoint (blockOf y1 ell) (blockOf y2 ell) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  apply hne
  funext μ
  apply Fin.ext
  rw [mem_blockOf] at hx1 hx2
  obtain ⟨a, ha⟩ := Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp h1 μ)
  obtain ⟨b, hb⟩ := Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp h2 μ)
  have g1 := hx1 μ
  have g2 := hx2 μ
  have e1 : ell * a < ell * (b + 1) := by rw [Nat.mul_succ]; omega
  have e2 : ell * b < ell * (a + 1) := by rw [Nat.mul_succ]; omega
  have f1 := Nat.lt_of_mul_lt_mul_left e1
  have f2 := Nat.lt_of_mul_lt_mul_left e2
  have hab : a = b := by omega
  rw [ha, hb, hab]

theorem sum_blocks_le {ell : ℕ} (hell : 0 < ell) (h : PeriodicLatticeSite L → ℝ) (hh : ∀ z, 0 ≤ h z) :
    ∑ cs : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}, ∑ z ∈ blockOf cs.1 ell, h z
      ≤ ∑ z, h z := by
  classical
  have hdisj : (↑(Finset.univ : Finset {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}) :
      Set {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}).PairwiseDisjoint
        (fun y => blockOf y.1 ell) :=
    fun y1 _ y2 _ hne => blocks_disjoint hell y1.1 y2.1 y1.2 y2.2 (fun e => hne (Subtype.ext e))
  rw [← Finset.sum_biUnion hdisj]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hh x)

theorem pathSite_injective (μ : Fin 3) (i : ℕ) :
    Function.Injective (fun z : PeriodicLatticeSite L => pathSite z μ i) := by
  have he : (fun z : PeriodicLatticeSite L => pathSite z μ i)
      = (fun z => AdalyFormal.Target.ClayStatement.periodicLatticeShift z μ)^[i] := by funext z; rfl
  rw [he]
  exact (AdalyFormal.Balaban.CoarseCurl.periodicLatticeShift_injective μ).iterate i

theorem sum_pathSite (μ : Fin 3) (i : ℕ) (h : PeriodicLatticeSite L → ℝ) :
    ∑ z : PeriodicLatticeSite L, h (pathSite z μ i) = ∑ z, h z :=
  Fintype.sum_bijective _ (pathSite_injective μ i).bijective_of_finite _ _ (fun z => rfl)

theorem T1_flat_pointwise {ell : ℕ} (hell : 0 < ell) (A : CoarseBond L 1 → SuTwo) (c : CoarseBond L (1 * ell)) :
    ‖unitToCoarseCov 1 ell (trivialU L) A c‖ ^ 2 ≤ (1 / (ell : ℝ) ^ 4) *
      ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1, ∑ i ∈ Finset.range ell, gA A (pathSite u.1 c.2 (i * 1), c.2) := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  rw [unitToCoarseCov_trivialU]
  set S := unitSitesOf 1 (1 * ell) c.1.1 with hS
  set F : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L 1} → ℕ → ℝ :=
    fun u i => fA A (pathSite u.1 c.2 (i * 1), c.2) with hF
  have hP : ∀ u i, ‖(if h : pathSite u.1 c.2 (i * 1) ∈ CoarseLattice L 1 then
      A (⟨pathSite u.1 c.2 (i * 1), h⟩, c.2) else 0)‖ = F u i := by
    intro u i
    rw [dif_pos (mem_coarseLattice_one _)]
    rfl
  have hnorm : ‖unitToCoarse 1 ell A c‖ ≤ (1 / (ell : ℝ) ^ 4) * ∑ u ∈ S, ∑ i ∈ Finset.range ell, F u i := by
    unfold unitToCoarse
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact le_of_eq (hP u i)
  have hcard : (S.card : ℝ) ≤ (ell : ℝ) ^ 3 := card_unitSites_le hell c.1.1
  have hFn : ∀ u i, 0 ≤ F u i := fun u i => norm_nonneg _
  have hin : ∀ u : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L 1},
      (∑ i ∈ Finset.range ell, F u i) ^ 2 ≤ (ell : ℝ) * ∑ i ∈ Finset.range ell, F u i ^ 2 := by
    intro u
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range ell) (f := fun i => F u i)
    simpa using this
  have hcs : (∑ u ∈ S, ∑ i ∈ Finset.range ell, F u i) ^ 2
      ≤ (ell : ℝ) ^ 4 * ∑ u ∈ S, ∑ i ∈ Finset.range ell, F u i ^ 2 := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := S) (f := fun u => ∑ i ∈ Finset.range ell, F u i)
    have h2 : ∑ u ∈ S, (∑ i ∈ Finset.range ell, F u i) ^ 2
        ≤ (ell : ℝ) * ∑ u ∈ S, ∑ i ∈ Finset.range ell, F u i ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun u _ => hin u
    have hsn : 0 ≤ ∑ u ∈ S, ∑ i ∈ Finset.range ell, F u i ^ 2 :=
      Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun i _ => sq_nonneg _
    calc (∑ u ∈ S, ∑ i ∈ Finset.range ell, F u i) ^ 2
        ≤ (S.card : ℝ) * ∑ u ∈ S, (∑ i ∈ Finset.range ell, F u i) ^ 2 := h1
      _ ≤ (S.card : ℝ) * ((ell : ℝ) * ∑ u ∈ S, ∑ i ∈ Finset.range ell, F u i ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
      _ = ((S.card : ℝ) * ell) * ∑ u ∈ S, ∑ i ∈ Finset.range ell, F u i ^ 2 := by ring
      _ ≤ ((ell : ℝ) ^ 3 * ell) * ∑ u ∈ S, ∑ i ∈ Finset.range ell, F u i ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hellR.le) hsn
      _ = (ell : ℝ) ^ 4 * ∑ u ∈ S, ∑ i ∈ Finset.range ell, F u i ^ 2 := by ring
  have hsumF : 0 ≤ ∑ u ∈ S, ∑ i ∈ Finset.range ell, F u i :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun i _ => hFn u i
  calc ‖unitToCoarse 1 ell A c‖ ^ 2
      ≤ ((1 / (ell : ℝ) ^ 4) * ∑ u ∈ S, ∑ i ∈ Finset.range ell, F u i) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = (1 / (ell : ℝ) ^ 4) ^ 2 * (∑ u ∈ S, ∑ i ∈ Finset.range ell, F u i) ^ 2 := by ring
    _ ≤ (1 / (ell : ℝ) ^ 4) ^ 2 * ((ell : ℝ) ^ 4 * ∑ u ∈ S, ∑ i ∈ Finset.range ell, F u i ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = (1 / (ell : ℝ) ^ 4) * ∑ u ∈ S, ∑ i ∈ Finset.range ell, F u i ^ 2 := by
        field_simp
    _ = _ := rfl

theorem T1_flat_l2 {ell : ℕ} (hell : 0 < ell) (A : CoarseBond L 1 → SuTwo) :
    ∑ c : CoarseBond L (1 * ell), ‖unitToCoarseCov 1 ell (trivialU L) A c‖ ^ 2
      ≤ (1 / (ell : ℝ) ^ 3) * l1 (gA A) := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hell1 : 0 < 1 * ell := by omega
  have h1 : ∑ c : CoarseBond L (1 * ell), ‖unitToCoarseCov 1 ell (trivialU L) A c‖ ^ 2
      ≤ ∑ c : CoarseBond L (1 * ell), (1 / (ell : ℝ) ^ 4) *
        ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1, ∑ i ∈ Finset.range ell, gA A (pathSite u.1 c.2 (i * 1), c.2) :=
    Finset.sum_le_sum fun c _ => T1_flat_pointwise hell A c
  refine h1.trans ?_
  rw [← Finset.mul_sum]
  -- reorganise: sum over (cs, mu)
  have h2 : ∑ c : CoarseBond L (1 * ell),
        ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1, ∑ i ∈ Finset.range ell, gA A (pathSite u.1 c.2 (i * 1), c.2)
      ≤ ∑ μ : Fin 3, ∑ i ∈ Finset.range ell, ∑ z : PeriodicLatticeSite L, gA A (z, μ) := by
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_le_sum fun μ _ => ?_
    -- fixed direction
    have hswap : ∑ cs : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L (1 * ell)},
          ∑ u ∈ unitSitesOf 1 (1 * ell) cs.1, ∑ i ∈ Finset.range ell, gA A (pathSite u.1 μ (i * 1), μ)
        = ∑ i ∈ Finset.range ell, ∑ cs : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L (1 * ell)},
          ∑ u ∈ unitSitesOf 1 (1 * ell) cs.1, gA A (pathSite u.1 μ (i * 1), μ) := by
      calc _ = ∑ cs : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L (1 * ell)},
            ∑ i ∈ Finset.range ell, ∑ u ∈ unitSitesOf 1 (1 * ell) cs.1,
              gA A (pathSite u.1 μ (i * 1), μ) :=
            Finset.sum_congr rfl fun cs _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    refine le_trans (le_of_eq hswap) (Finset.sum_le_sum fun i _ => ?_)
    set H : PeriodicLatticeSite L → ℝ := fun z => gA A (pathSite z μ (i * 1), μ) with hH
    have hHn : ∀ z, 0 ≤ H z := fun z => gA_nonneg A _
    have hin : ∀ cs : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L (1 * ell)},
        ∑ u ∈ unitSitesOf 1 (1 * ell) cs.1, gA A (pathSite u.1 μ (i * 1), μ)
          ≤ ∑ z ∈ blockOf cs.1 (1 * ell), H z := by
      intro cs
      have hsub : (unitSitesOf 1 (1 * ell) cs.1).image Subtype.val ⊆ blockOf cs.1 (1 * ell) := by
        intro z hz
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
        simpa [unitSitesOf] using hu
      calc ∑ u ∈ unitSitesOf 1 (1 * ell) cs.1, gA A (pathSite u.1 μ (i * 1), μ)
          = ∑ z ∈ (unitSitesOf 1 (1 * ell) cs.1).image Subtype.val, H z :=
            (Finset.sum_image (f := H) (g := Subtype.val) (s := unitSitesOf 1 (1 * ell) cs.1)
              (fun a _ b _ h => Subtype.ext h)).symm
        _ ≤ ∑ z ∈ blockOf cs.1 (1 * ell), H z :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => hHn z)
    refine (Finset.sum_le_sum fun cs _ => hin cs).trans ?_
    refine (sum_blocks_le hell1 H hHn).trans (le_of_eq ?_)
    exact sum_pathSite μ (i * 1) (fun z => gA A (z, μ))
  have h3 : ∑ μ : Fin 3, ∑ i ∈ Finset.range ell, ∑ z : PeriodicLatticeSite L, gA A (z, μ)
      = (ell : ℝ) * l1 (gA A) := by
    unfold l1
    rw [Fintype.sum_prod_type_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc (1 / (ell : ℝ) ^ 4) * _ ≤ (1 / (ell : ℝ) ^ 4) * ((ell : ℝ) * l1 (gA A)) :=
        mul_le_mul_of_nonneg_left (h2.trans (le_of_eq h3)) (by positivity)
    _ = (1 / (ell : ℝ) ^ 3) * l1 (gA A) := by field_simp

end flatT1

#print axioms embS_surj
#print axioms embCB_bijective
#print axioms sum_embE
#print axioms sum_embE_edge
#print axioms sum_blocks_le
#print axioms T1_flat_pointwise
#print axioms T1_flat_l2

end AdalyFormal.BondComposite
