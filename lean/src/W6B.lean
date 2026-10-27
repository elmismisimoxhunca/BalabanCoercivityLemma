import W6A
import MI29
import MI6
import FE2b
import FE4a

/-!
# W6B -- the FLAT bond `Q` on a proper tower, row by row, and the row geometry (W6 lane, 2026-10-13)

`G = geomOf ℓ k S` on `L = scaleUp ℓ k Lu`; a row `p = (j, b)` of `𝔅` is a level-`j` bond, `rowCB p` the same bond as a coarse
bond of stride `n_j = ℓ^j` (MI29 `row_aligned`).
* **`Qflat_row`** : `(Q₁ A)(p) = lineCoarseRestrictSuTwo n_j A (rowCB p)` at EVERY level `j ≤ k` (generalises FE2b, top level).
* `pathSite_eq_coarseShift`, `reads_site` : a flat level-`j` row reads only bonds based in `B(z) ∪ B(z⁺)` (`z` its base,
  `z⁺ = z + n_j e_μ`).
* `pdist_block_le` : `x ∈ B(y, n) ⇒ |y − x| ≤ 3n`.
* `not_om_of_block` : an aligned `z ∉ Ω_{j+1}` has its whole `ℓ^j`-block outside `Ω_{j+1}` (admissible).
* `strat_of_block` : sites of the block of a `Λ_j` point have stratum `j`.
* `read_strat_le` : every site read by a flat level-`j` row has stratum `≤ j`.
* `read_anchor` : every site read by a flat level-`j` row is within `4 n_j` of a point of `Λ_j` (stratum `j`, in `Ω_j`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.W6

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq coarseShift_mem_coarseLattice)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.StatementLane (Tower Admissible scaleUp bigSide pdist pcd BlockClosed)
open AdalyFormal.StatementLaneR8 (pdist_triangle pdist_comm pdist_self pdist_coarseShift_le)
open AdalyFormal.GenuineU1 (Qcomp_closed)
open AdalyFormal.BondComposite (hdvd_scaleUp)

section rows
variable {ell k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

/-- a row of `𝔅` as a coarse bond of its own stride -/
def rowCB (hell : 0 < ell) (p : BIdx (geomOf ell k S)) : CoarseBond (scaleUp ell k Lu) (ell ^ (p.1 : ℕ)) :=
  (⟨p.2.1.1, AdalyFormal.M1IMS.row_aligned hell p⟩, p.2.1.2)

theorem hdvdL (hell : 0 < ell) (p : BIdx (geomOf ell k S)) : ∀ ν, ell ^ (p.1 : ℕ) ∣ scaleUp ell k Lu ν + 1 :=
  fun ν => hdvd_scaleUp ell k Lu hell _ (Nat.lt_succ_iff.mp p.1.isLt) ν

theorem bgTower_trivial (j : ℕ) : bgTower (geomOf ell k S) (trivialU (scaleUp ell k Lu)) j = flatCfg := by
  unfold bgTower
  exact Ubar_flat _ j

/-- **the flat row at any level** -/
theorem Qflat_row (hell : 0 < ell) (A : BondFnL2 (scaleUp ell k Lu)) (p : BIdx (geomOf ell k S)) :
    (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull A p
      = lineCoarseRestrictSuTwo (ell ^ (p.1 : ℕ)) (WithLp.ofLp A) (rowCB hell p) := by
  have hell' : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  have hj : (p.1 : ℕ) ≤ k := Nat.lt_succ_iff.mp p.1.isLt
  have key := Qcomp_closed ell hell (bgTower (geomOf ell k S) (trivialU _)) bgTower_trivial k
    (AdalyFormal.GenuineU1.scaleUp_tiling ell k Lu hell)
    (suCoordF (WithLp.ofLp A)) (p.1 : ℕ) hj (ell ^ (p.1 : ℕ)) rfl (rowCB hell p)
  rw [suCoordFInv_suCoordF] at key
  show (((ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (QlinB (geomOf ell k S) (trivialU _) (p.1 : ℕ) A)) p.2.1 = _
  have hQ : (WithLp.ofLp (QlinB (geomOf ell k S) (trivialU _) (p.1 : ℕ) A)) p.2.1
      = suCoordFInv (QlinCompX ell (bgTower (geomOf ell k S) (trivialU _)) (p.1 : ℕ) (suCoordF (WithLp.ofLp A)))
        ((rowCB hell p).1.1, (rowCB hell p).2) := by
    have hb := QlinCompL_eq_QlinCompX ell (bgTower (geomOf ell k S) (trivialU _)) k
      (fun j _ => by rw [bgTower_trivial]; exact RegBg_flat _ _) (p.1 : ℕ) hj
    rw [← hb]; rfl
  rw [hQ, key]
  rw [smul_smul]
  push_cast
  rw [inv_mul_cancel₀ (pow_ne_zero _ hell'), one_smul]

end rows

/-! ## block geometry -/

section geo
variable {L : PeriodicLatticeExtent}

theorem pathSite_eq_coarseShift (x : PeriodicLatticeSite L) (μ : Fin 3) (i : ℕ) :
    pathSite x μ i = coarseShift x i μ := rfl

/-- `x ∈ B(y,n)` ⇒ `|y − x| ≤ 3n` -/
theorem pdist_block_le {y x : PeriodicLatticeSite L} {n : ℕ} (hx : x ∈ blockOf y n) : pdist y x ≤ 3 * n := by
  rw [mem_blockOf] at hx
  unfold pdist
  have h : ∀ μ : Fin 3, pcd (L μ + 1) (y μ).val (x μ).val ≤ n := by
    intro μ
    obtain ⟨h1, h2⟩ := hx μ
    unfold pcd
    rw [if_pos h1]
    exact le_trans (min_le_left _ _) (by omega)
  calc ∑ μ : Fin 3, pcd (L μ + 1) (y μ).val (x μ).val ≤ ∑ _μ : Fin 3, n := Finset.sum_le_sum (fun μ _ => h μ)
    _ = 3 * n := by simp

/-- a flat row reads only bonds based in the two end-point blocks -/
theorem reads_site {n : ℕ} (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (c : CoarseBond L n)
    {x : PeriodicLatticeSite L} (hx : x ∈ blockOf c.1.1 n) {i : ℕ} (hi : i < n) :
    pathSite x c.2 i ∈ blockOf c.1.1 n ∨ pathSite x c.2 i ∈ blockOf (coarseShift c.1.1 n c.2) n := by
  rw [pathSite_eq_coarseShift]
  exact AdalyFormal.FlatEllGeneral.coarseShift_block hn hdvd c.1.2 hx c.2 i hi.le

/-- support of the generic product kernel: `gbK ≠ 0 ⇒` same direction and the bond is based in the block of `c`. -/
theorem gbK_support {g h : ℕ → ℝ} {n : ℕ} (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1)
    (hgz : ∀ t, n ≤ t → g t = 0) (hhz : ∀ t, n ≤ t → h t = 0) {x : PeriodicLatticeSite L} {μ : Fin 3}
    {c : CoarseBond L n} (h0 : AdalyFormal.W6P.gbK g h n x μ c ≠ 0) : c.2 = μ ∧ x ∈ blockOf c.1.1 n := by
  unfold AdalyFormal.W6P.gbK at h0
  by_cases hc : c.2 = μ
  · rw [if_pos hc] at h0
    refine ⟨hc, ?_⟩
    rw [mem_blockOf]
    intro ν
    have hν : AdalyFormal.W6P.gfac g h μ ν ((x ν - c.1.1 ν).val) ≠ 0 := fun hz => h0 (Finset.prod_eq_zero (mem_univ ν) hz)
    have hlt : (x ν - c.1.1 ν).val < n := by
      by_contra hge
      push_neg at hge
      apply hν
      unfold AdalyFormal.W6P.gfac
      split_ifs
      · exact hgz _ hge
      · exact hhz _ hge
    have hcd : n ∣ (c.1.1 ν).val := Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp c.1.2 ν)
    have hfit := AdalyFormal.M0Finish.coord_fit hn (hdvd ν) (c.1.1 ν) hcd
    rw [AdalyFormal.M0Finish.fin_sub_val] at hlt
    have hxl := (x ν).isLt
    rcases Nat.lt_or_ge (x ν).val (c.1.1 ν).val with hlt' | hge'
    · rw [Nat.mod_eq_of_lt (by omega)] at hlt; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hlt; omega
  · rw [if_neg hc] at h0; exact absurd rfl h0

end geo

/-! ## strata of blocks (admissible tower) -/

section strata
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

/-- an `ℓ^j`-aligned site outside `Ω_{j+1}` has its whole `ℓ^j`-block outside `Ω_{j+1}` -/
theorem not_om_of_block (hell : 0 < ell) (hS : Admissible ell M R k S) {j : ℕ} {z : PeriodicLatticeSite (scaleUp ell k Lu)}
    (hz : ∀ μ, ell ^ j ∣ (z μ).val) (hzn : z ∉ S.Om (j + 1)) {s : PeriodicLatticeSite (scaleUp ell k Lu)}
    (hs : s ∈ blockOf z (ell ^ j)) : s ∉ S.Om (j + 1) := by
  intro hs1
  by_cases hk : j + 1 ≤ k
  · apply hzn
    refine hS.2.2.2.1 (j + 1) hk s hs1 z (fun μ => ?_)
    obtain ⟨h1, h2⟩ := (mem_blockOf.mp hs) μ
    have := AdalyFormal.IngredientFamilyR2.blk_div (ell ^ j) (M * ell) (z μ).val (s μ).val (pow_pos hell j) (hz μ) h1 h2
    have e : ell ^ j * (M * ell) = bigSide M ell (j + 1) := by unfold bigSide; ring
    rw [e] at this
    exact this
  · rw [hS.2.1 (j + 1) (by omega)] at hs1; exact hs1

/-- sites of the block of a `Λ_j` point have stratum `j` -/
theorem strat_of_block (hell : 0 < ell) (hS : Admissible ell M R k S) {j : ℕ} (hj : j ≤ k)
    {y : PeriodicLatticeSite (scaleUp ell k Lu)} (hy : y ∈ (geomOf ell k S).Lam j)
    {s : PeriodicLatticeSite (scaleUp ell k Lu)} (hs : s ∈ blockOf y (ell ^ j)) : AdalyFormal.M1.strat S k s = j := by
  rw [AdalyFormal.M1IMS.strat_eq_stratG hell hS s]
  exact AdalyFormal.M1Site.stratG_eq (AdalyFormal.M1Site.properTower_geomOf hell hS) hj hy hs

/-- stratum `≤ j` from `s ∉ Ω_{j+1}` -/
theorem strat_le_of_not (hS : Admissible ell M R k S) {j : ℕ} {s : PeriodicLatticeSite (scaleUp ell k Lu)}
    (hs : s ∉ S.Om (j + 1)) : AdalyFormal.M1.strat S k s ≤ j := by
  by_contra hlt
  push_neg at hlt
  have hk := AdalyFormal.M1.strat_le S k s
  exact hs ((AdalyFormal.M1.le_strat_iff hS (by omega) (by omega) s).mp hlt)

/-- `s ∉ Ω_i` from stratum `< i` (`1 ≤ i`) -/
theorem not_om_of_strat_lt (hS : Admissible ell M R k S) {i : ℕ} (hi : 1 ≤ i) {s : PeriodicLatticeSite (scaleUp ell k Lu)}
    (hs : AdalyFormal.M1.strat S k s < i) : s ∉ S.Om i := by
  intro hm
  by_cases hik : i ≤ k
  · have := (AdalyFormal.M1.le_strat_iff hS hi hik s).mpr hm; omega
  · rw [hS.2.1 i (by omega)] at hm; exact hm

/-- the bonds of a row of `𝔅` have no end-point in `Ω_{j+1}`. -/
theorem row_out (hell : 0 < ell) (hS : Admissible ell M R k S) (p : BIdx (geomOf ell k S)) :
    p.2.1.1 ∉ S.Om ((p.1 : ℕ) + 1) ∧ coarseShift p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2 ∉ S.Om ((p.1 : ℕ) + 1) := by
  have h := p.2.2.2
  push_neg at h
  exact ⟨fun hm => h.1 ((omGe_iff_om ell M R k hell S hS _ _).mpr hm),
    fun hm => h.2 ((omGe_iff_om ell M R k hell S hS _ _).mpr hm)⟩

/-- **every site read by a flat level-`j` row has stratum `≤ j`** -/
theorem read_strat_le (hell : 0 < ell) (hS : Admissible ell M R k S) (p : BIdx (geomOf ell k S))
    {x : PeriodicLatticeSite (scaleUp ell k Lu)} (hx : x ∈ blockOf p.2.1.1 (ell ^ (p.1 : ℕ))) {i : ℕ}
    (hi : i < ell ^ (p.1 : ℕ)) : AdalyFormal.M1.strat S k (pathSite x p.2.1.2 i) ≤ (p.1 : ℕ) := by
  have hn : 0 < ell ^ (p.1 : ℕ) := pow_pos hell _
  have hal := AdalyFormal.M1IMS.row_aligned hell p
  have hzd : ∀ μ, ell ^ (p.1 : ℕ) ∣ (p.2.1.1 μ).val := fun μ => Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp hal μ)
  have hup : coarseShift p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2 ∈ CoarseLattice _ (ell ^ (p.1 : ℕ)) :=
    coarseShift_mem_coarseLattice (hdvdL hell p) hal _
  have hud : ∀ μ, ell ^ (p.1 : ℕ) ∣ ((coarseShift p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2) μ).val :=
    fun μ => Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp hup μ)
  obtain ⟨ho1, ho2⟩ := row_out hell hS p
  rcases reads_site hn (hdvdL hell p) (rowCB hell p) hx hi with h | h
  · exact strat_le_of_not hS (not_om_of_block hell hS hzd ho1 h)
  · exact strat_le_of_not hS (not_om_of_block hell hS hud ho2 h)

/-- **every site read by a flat level-`j` row is within `4 n_j` of a `Λ_j` point** -/
theorem read_anchor (hell : 0 < ell) (p : BIdx (geomOf ell k S))
    {x : PeriodicLatticeSite (scaleUp ell k Lu)} (hx : x ∈ blockOf p.2.1.1 (ell ^ (p.1 : ℕ))) {i : ℕ}
    (hi : i < ell ^ (p.1 : ℕ)) :
    ∃ a ∈ (geomOf ell k S).Lam (p.1 : ℕ), pdist a (pathSite x p.2.1.2 i) ≤ 4 * ell ^ (p.1 : ℕ) := by
  have hn : 0 < ell ^ (p.1 : ℕ) := pow_pos hell _
  have hzz : pdist p.2.1.1 (coarseShift p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2) ≤ ell ^ (p.1 : ℕ) :=
    pdist_coarseShift_le p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2
  have hread : pdist p.2.1.1 (pathSite x p.2.1.2 i) ≤ 4 * ell ^ (p.1 : ℕ) ∧
      pdist (coarseShift p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2) (pathSite x p.2.1.2 i) ≤ 4 * ell ^ (p.1 : ℕ) := by
    rcases reads_site hn (hdvdL hell p) (rowCB hell p) hx hi with h | h
    · have h1 : pdist p.2.1.1 (pathSite x p.2.1.2 i) ≤ 3 * ell ^ (p.1 : ℕ) := pdist_block_le h
      refine ⟨by omega, ?_⟩
      have := pdist_triangle (coarseShift p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2) p.2.1.1 (pathSite x p.2.1.2 i)
      rw [pdist_comm (coarseShift p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2) p.2.1.1] at this; omega
    · have h1 : pdist (coarseShift p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2) (pathSite x p.2.1.2 i) ≤ 3 * ell ^ (p.1 : ℕ) :=
        pdist_block_le h
      refine ⟨?_, by omega⟩
      have := pdist_triangle p.2.1.1 (coarseShift p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2) (pathSite x p.2.1.2 i); omega
  rcases p.2.2.1 with h | h
  · exact ⟨p.2.1.1, h, hread.1⟩
  · exact ⟨coarseShift p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2, h, hread.2⟩

/-- a `Λ_j` point lies in `Ω_j` and has stratum `j`. -/
theorem lam_strat (hell : 0 < ell) (hS : Admissible ell M R k S) {j : ℕ} (hj : j ≤ k)
    {a : PeriodicLatticeSite (scaleUp ell k Lu)} (ha : a ∈ (geomOf ell k S).Lam j) :
    a ∈ S.Om j ∧ AdalyFormal.M1.strat S k a = j := by
  refine ⟨ha.2.1, strat_of_block hell hS hj ha ?_⟩
  rw [mem_blockOf]; intro μ; exact ⟨le_rfl, by have := pow_pos hell j; omega⟩

end strata

end AdalyFormal.W6

#print axioms AdalyFormal.W6.rowCB
#print axioms AdalyFormal.W6.hdvdL
#print axioms AdalyFormal.W6.bgTower_trivial
#print axioms AdalyFormal.W6.Qflat_row
#print axioms AdalyFormal.W6.pathSite_eq_coarseShift
#print axioms AdalyFormal.W6.pdist_block_le
#print axioms AdalyFormal.W6.reads_site
#print axioms AdalyFormal.W6.gbK_support
#print axioms AdalyFormal.W6.not_om_of_block
#print axioms AdalyFormal.W6.strat_of_block
#print axioms AdalyFormal.W6.strat_le_of_not
#print axioms AdalyFormal.W6.not_om_of_strat_lt
#print axioms AdalyFormal.W6.row_out
#print axioms AdalyFormal.W6.read_strat_le
#print axioms AdalyFormal.W6.read_anchor
#print axioms AdalyFormal.W6.lam_strat
