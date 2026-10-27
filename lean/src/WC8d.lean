import WC8b
import WC8c

/-!
# WC8d -- the cone geometry and `qs_injective_class` (M2 W6 lane)

* `cone_deep`, `cone_near` : a ball of radius `≤ 5 M ℓ^i` around a site lies in ONE class cube of index `j` (ball deep in `Ω_j`)
  or of index `j-1` (a point of `Ω_j^c` within the ball).
* `ConeBand` : the rows NOT covered by these two cases (precise Lean predicate).
* `ConeAt` holds outside the band (`coneAt_of_not_band`); `ConeAt` forces `Ball z (36 ℓ^{j+1}) ⊆ Ω_0` (`coneAt_ball_subset_Om0`).
* `qs_injective_class` : `Q_U*` injective at the printed class, `ConeInCube` as an explicit hypothesis.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace AdalyFormal.M2W6

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist IsClassCube CubeBond siteBox GridCorner bigSide towerBj)
open AdalyFormal.StatementLane2 (PerCubeRegular2)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.M2Bridge (cube_isClass pdist_lt_three_s')
open AdalyFormal.M1 (om_anti)
open AdalyFormal.W6
open AdalyFormal.NonflatJet
open AdalyFormal.BondComposite
open AdalyFormal.TowerLoc
open AdalyFormal.StatementLaneR8
open SmallnessBridge.Assemble (loopFactorBound)

section geom
variable {L : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower L}

/-- a ball of radius `≤ 5 B_j` around a site of `B_j`, with the `36 B_j`-ball inside `Ω_j`, is in one index-`j` class cube. -/
theorem cone_deep (hS : Admissible ell M R k S) (hell : 1 ≤ ell) (hR : 36 ≤ R) {j : ℕ} (hjk : j ≤ k)
    (hB : 0 < bigSide M ell j) {y0 : PeriodicLatticeSite L} (hy0 : y0 ∈ towerBj S j)
    (hdeep : ∀ w, pdist y0 w < 36 * bigSide M ell j → w ∈ S.Om j) {r : ℕ} (hr : r ≤ 5 * bigSide M ell j) :
    ∃ sites : Set (PeriodicLatticeSite L), IsClassCube ell M 12 k S sites j ∧ Ball y0 r ⊆ sites := by
  obtain ⟨z, hgrid, hbox⟩ := box_ball hB (fun σ => hS.2.2.1 j hjk σ) y0 hr
  have hxb : y0 ∈ siteBox z (12 * bigSide M ell j) := hbox (by show pdist y0 y0 ≤ r; rw [pdist_self]; exact Nat.zero_le _)
  have hsub : siteBox z (12 * bigSide M ell j) ⊆ S.Om j := by
    intro w hw
    apply hdeep
    have := pdist_lt_three_s' hxb hw
    omega
  have hRl : 3 * 12 ≤ R * ell := le_trans (by omega) (Nat.le_mul_of_pos_right R hell)
  exact ⟨_, cube_isClass hS hjk hgrid hsub hxb hy0 hRl, hbox⟩

/-- a point of `Ω_{i+1}^c` within the ball of radius `5 B_i` around a site of `Ω_{i+1}`: the ball is in one index-`i` class cube. -/
theorem cone_near (hS : Admissible ell M R k S) (hell : 1 ≤ ell) (hR : 36 ≤ R) {i : ℕ} (hik : i + 1 ≤ k)
    (hB : 0 < bigSide M ell i) {y0 : PeriodicLatticeSite L} (hy0 : y0 ∈ S.Om (i + 1))
    {w0 : PeriodicLatticeSite L} (hw0 : w0 ∉ S.Om (i + 1)) (hd : pdist y0 w0 ≤ 5 * bigSide M ell i) :
    ∃ sites : Set (PeriodicLatticeSite L), IsClassCube ell M 12 k S sites i ∧ Ball y0 (5 * bigSide M ell i) ⊆ sites := by
  obtain ⟨z, hgrid, hbox⟩ := box_ball hB (fun σ => hS.2.2.1 i (by omega) σ) y0 (le_refl _)
  have hxb : y0 ∈ siteBox z (12 * bigSide M ell i) := hbox (by show pdist y0 y0 ≤ _; rw [pdist_self]; exact Nat.zero_le _)
  have hsub : siteBox z (12 * bigSide M ell i) ⊆ S.Om i := by
    intro q hq
    by_contra hq'
    have h5 := hS.2.2.2.2.1 i (by omega) q hq' y0 hy0
    have h3 := pdist_lt_three_s' hxb hq
    rw [pdist_comm] at h5
    have : 36 * bigSide M ell i ≤ R * bigSide M ell i := Nat.mul_le_mul_right _ hR
    omega
  have hw0b : w0 ∈ siteBox z (12 * bigSide M ell i) := hbox hd
  have hRl : 3 * 12 ≤ R * ell := le_trans (by omega) (Nat.le_mul_of_pos_right R hell)
  exact ⟨_, cube_isClass hS (by omega) hgrid hsub hw0b ⟨hsub hw0b, hw0⟩ hRl, hbox⟩

/-- the anchor of a row: a site of `B_j` within `ℓ^j` of the row base -/
theorem row_anchor {Lu : PeriodicLatticeExtent} {ell k : ℕ} {S : Tower (scaleUp ell k Lu)} (p : BIdx (geomOf ell k S)) :
    ∃ a, a ∈ towerBj S (p.1 : ℕ) ∧ pdist p.2.1.1 a ≤ ell ^ (p.1 : ℕ) := by
  have hb : p.2.1.1 ∈ (geomOf ell k S).Lam (p.1 : ℕ) ∨
      coarseShift p.2.1.1 ((geomOf ell k S).ell ^ (p.1 : ℕ)) p.2.1.2 ∈ (geomOf ell k S).Lam (p.1 : ℕ) := p.2.2.1
  rcases hb with h | h
  · exact ⟨p.2.1.1, ⟨h.2.1, h.2.2⟩, by rw [pdist_self]; exact Nat.zero_le _⟩
  · exact ⟨coarseShift p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2, ⟨h.2.1, h.2.2⟩, pdist_coarseShift_le p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2⟩

/-- deep in `Ω_j` (the `36 B_j`-ball of the anchor is inside `Ω_j`) -/
def Deep (ell M : ℕ) (S : Tower L) (y0 : PeriodicLatticeSite L) (j : ℕ) : Prop :=
  ∀ w, pdist y0 w < 36 * bigSide M ell j → w ∈ S.Om j

/-- within `5 B_{j-1}` of `Ω_j^c` (only meaningful for `1 ≤ j`) -/
def NearBdry (ell M : ℕ) (S : Tower L) (y0 : PeriodicLatticeSite L) (j : ℕ) : Prop :=
  1 ≤ j ∧ ∃ w, w ∉ S.Om j ∧ pdist y0 w ≤ 5 * bigSide M ell (j - 1)

/-- **the uncovered band**: the anchor `y0 ∈ B_j` is neither deep (so some point of `Ω_j^c` lies within `36 B_j`) nor within
`5 B_{j-1}` of `Ω_j^c` (for `j = 0` the second clause is void). -/
def ConeBand (ell M : ℕ) (S : Tower L) (y0 : PeriodicLatticeSite L) (j : ℕ) : Prop :=
  ¬ Deep ell M S y0 j ∧ ¬ NearBdry ell M S y0 j

/-- **`ConeAt` outside the band** (needs `37 ℓ² ≤ 5 M`, `36 ≤ R`). -/
theorem coneAt_of_not_band (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hR : 36 ≤ R) (hM : 37 * ell ^ 2 ≤ 5 * M)
    {z y0 : PeriodicLatticeSite L} {j : ℕ} (hjk : j ≤ k) (hy0 : y0 ∈ towerBj S j) (hzy : pdist z y0 ≤ ell ^ j)
    (hnb : ¬ ConeBand ell M S y0 j) : ConeAt ell M 12 k S z j := by
  have hell0 : 0 < ell := by omega
  have hej : 0 < ell ^ j := pow_pos hell0 j
  have hpow : ell ^ (j + 1) = ell * ell ^ j := by rw [pow_succ']
  have hle : ell ^ j ≤ ell ^ (j + 1) := Nat.pow_le_pow_right hell0 (by omega)
  by_cases hd : Deep ell M S y0 j
  · -- deep: index j
    have hB : 0 < bigSide M ell j := by
      unfold bigSide
      have : 0 < M := by nlinarith
      exact Nat.mul_pos this hej
    have h37 : 37 * ell ^ (j + 1) ≤ 5 * bigSide M ell j := by
      unfold bigSide
      have h1 : 37 * ell ≤ 5 * M := by nlinarith
      have := Nat.mul_le_mul_right (ell ^ j) h1
      rw [hpow]; nlinarith
    obtain ⟨sites, hq, hsub⟩ := cone_deep hS (by omega) hR hjk hB hy0 hd (le_refl _)
    refine ⟨sites, j, hq, by omega, fun w hw => hsub ?_⟩
    have h1 : pdist z w ≤ 36 * ell ^ (j + 1) := hw
    have h2 := pdist_triangle y0 z w
    rw [pdist_comm y0 z] at h2
    show pdist y0 w ≤ 5 * bigSide M ell j
    omega
  · -- near the boundary of Ω_j: index j - 1
    have hnear : NearBdry ell M S y0 j := by
      by_contra hn
      exact hnb ⟨hd, hn⟩
    obtain ⟨hj1, w0, hw0, hdw⟩ := hnear
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hi : i + 1 - 1 = i := by omega
    rw [hi] at hdw
    have hei : 0 < ell ^ i := pow_pos hell0 i
    have hB : 0 < bigSide M ell i := by
      unfold bigSide
      have : 0 < M := by nlinarith
      exact Nat.mul_pos this hei
    have hp2 : ell ^ (i + 1 + 1) = ell * ell * ell ^ i := by rw [pow_succ', pow_succ']; ring
    have hp1 : ell ^ (i + 1) = ell * ell ^ i := by rw [pow_succ']
    have h37 : 37 * ell ^ (i + 1 + 1) ≤ 5 * bigSide M ell i := by
      unfold bigSide
      have h1 : 37 * (ell * ell) ≤ 5 * M := by nlinarith
      have := Nat.mul_le_mul_right (ell ^ i) h1
      rw [hp2]; nlinarith
    obtain ⟨sites, hq, hsub⟩ := cone_near hS (by omega) hR hjk hB hy0.1 hw0 hdw
    refine ⟨sites, i, hq, by omega, fun w hw => hsub ?_⟩
    have h1 : pdist z w ≤ 36 * ell ^ (i + 1 + 1) := hw
    have h2 := pdist_triangle y0 z w
    rw [pdist_comm y0 z] at h2
    show pdist y0 w ≤ 5 * bigSide M ell i
    have hz' : pdist z y0 ≤ ell ^ (i + 1) := hzy
    have hle' : ell ^ (i + 1) ≤ ell ^ (i + 1 + 1) := Nat.pow_le_pow_right hell0 (by omega)
    omega

/-- `ConeAt` forces the `36 ℓ^{j+1}`-ball into `Ω_0`: class cubes lie in `B_i ∪ B_{i+1} ⊆ Ω_0`. -/
theorem coneAt_ball_subset_Om0 (hS : Admissible ell M R k S) {z : PeriodicLatticeSite L} {j : ℕ} {f : ℕ}
    (h : ConeAt ell M f k S z j) : Ball z (36 * ell ^ (j + 1)) ⊆ S.Om 0 := by
  obtain ⟨sites, i, hq, -, hsub⟩ := h
  intro w hw
  have hws := hsub hw
  obtain ⟨-, -, hbj, -⟩ := hq.1
  have hOm : ∀ m, S.Om m ⊆ S.Om 0 := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact fun x hx => hx
    · exact (om_anti hS hm).trans (hS.1 0)
  rcases hbj hws with h1 | h1
  · exact hOm i h1.1
  · exact hOm (i + 1) h1.1

end geom

section final
variable {ell M R f k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

/-- **`ConeInCube` outside the band**: if no row anchor lies in the band, every row cone is in a class cube. -/
theorem coneInCube_of_not_band (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hR : 36 ≤ R) (hM : 37 * ell ^ 2 ≤ 5 * M)
    (hnb : ∀ p : BIdx (geomOf ell k S), ∀ a, a ∈ towerBj S (p.1 : ℕ) → pdist p.2.1.1 a ≤ ell ^ (p.1 : ℕ) →
      ¬ ConeBand ell M S a (p.1 : ℕ)) : ConeInCube ell M 12 k S := by
  intro p
  obtain ⟨a, ha, hpa⟩ := row_anchor p
  exact coneAt_of_not_band hS hell hR hM (Nat.lt_succ_iff.mp p.1.isLt) ha hpa (hnb p a ha hpa)

/-- **`Q_U*` is injective at the printed per-cube class** (no global gauge, no global regularity, no energy norm); the geometry
`ConeInCube` is an explicit hypothesis. -/
theorem qs_injective_class (hS : Admissible ell M R k S) (hell2 : 2 ≤ ell) (hM : 0 < M) (hR : 8 * ell ≤ R) (hroom : 17 * ell ≤ R * M)
    (hT3 : ∀ μ, 3 ≤ Lu μ + 1) {α₀ η : ℝ} (hα0 : 0 ≤ α₀) (hη : 0 < η)
    (ha1 : (f : ℝ) * M * α₀ ≤ 1) (hsm4 : 4000000 * (ell : ℝ) ^ 4 * ((4 * Real.pi + 4) * ((f : ℝ) * M * α₀)) ≤ 1)
    (U : LinkCfg (scaleUp ell k Lu)) (hP : PerCubeRegular2 ell M f k S α₀ η U) (hcone : ConeInCube ell M f k S)
    (hsm : ∀ j' l, l < k → rhoOf ell (clsEps ell ((f : ℝ) * M * α₀) j' l) < Real.pi / 2)
    (hr : ∀ j' l, l < k → Real.pi / 2 * ((loopFactorBound ell : ℝ) * clsEps ell ((f : ℝ) * M * α₀) j' l) < r0)
    (Sstar : ℝ) (hSstar : ∀ j' : ℕ, j' ≤ k → ∑ l ∈ range j', thetaOf ell (clsEps ell ((f : ℝ) * M * α₀) j' l) ≤ Sstar)
    (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (hsmall : 2 * CsrcS ell Sstar * (1 + CsrcA ell Sstar) < 1) :
    Function.Injective (gparams ell k Lu (by omega : 0 < ell) S U a Lam).data.Qs := by
  obtain ⟨γ, hch⟩ := chartHyp_of_class hell2 hT3 hα0 hη ha1 hsm4 U hP hcone
  have ha0 : 0 ≤ (f : ℝ) * M * α₀ := by positivity
  exact qs_injective_charts hell2 hS hM hR hroom U γ (clsEps ell ((f : ℝ) * M * α₀)) hch
    (fun j' l _ => clsEps_nonneg ell ha0 j' l) hsm hr Sstar hSstar a Lam hsmall

end final

end AdalyFormal.M2W6

#print axioms AdalyFormal.M2W6.cone_deep
#print axioms AdalyFormal.M2W6.cone_near
#print axioms AdalyFormal.M2W6.row_anchor
#print axioms AdalyFormal.M2W6.coneAt_of_not_band
#print axioms AdalyFormal.M2W6.coneAt_ball_subset_Om0
#print axioms AdalyFormal.M2W6.coneInCube_of_not_band
#print axioms AdalyFormal.M2W6.qs_injective_class
