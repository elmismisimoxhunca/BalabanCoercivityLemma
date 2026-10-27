import NP6

/-!
# NP7 -- one level, one ball: decay ⇒ small defect ⇒ local W3 (m1_patch_nonflat, 2026-10-14)

W2K `optDecay_of_harm` and W2H `W3LocAt_of` quantify over ALL levels and ALL `Rg`; a non-flat configuration is small only at
the level of its patch.  Here the same arguments at ONE `(i, Rg, w, s)`:
* `optDecay_lev` : the decay inequality for `HK G U (Ball w (s + d ell^i))` gives `defK ≤ ε · wnormSq` for `A` supported on
  bonds touching `Ball w s`;
* **`w3loc_lev`** : with `cW · wnormSq ≤ G0form` for that `A`, `(cW − ε) · wnormSq ≤ locG0(K = Ball w (s + d ell^i))(A)`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M1NonFlat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.M1Patch (patchTower)
open AdalyFormal.M1IMS (G0form)
open AdalyFormal.M1W2 (HK defK defK_eq gradOn inner_le_gradOn wnorm_ge_patch locG0 G0_sub_defK)

variable {L : PeriodicLatticeExtent}

theorem optDecay_lev (ell : ℕ) (hell : 0 < ell) (U : Cfg L) (i : ℕ) (Rg : Set (PeriodicLatticeSite L)) (ε : ℝ)
    (hε : 0 ≤ ε) (d : ℕ) (w : PeriodicLatticeSite L) (s : ℕ)
    (hharm : ∀ h ∈ HK (geomOf ell (i + 1) (patchTower i Rg)) U (Ball w (s + d * ell ^ i)),
      gradOn U (Ball w s) h ≤ ε * (((ell : ℝ) ^ (i + 1))⁻¹) ^ 2 * ‖h‖ ^ 2)
    (A : BondFnL2 L)
    (hA : ∀ b : Bond L, (WithLp.ofLp A) b ≠ 0 → b.1 ∈ Ball w s ∨ periodicLatticeShift b.1 b.2 ∈ Ball w s) :
    defK (geomOf ell (i + 1) (patchTower i Rg)) U (Ball w (s + d * ell ^ i)) A
      ≤ ε * AdalyFormal.M1.wnormSq (patchTower i Rg) ell (i + 1) A := by
  rw [defK_eq]
  set G := geomOf ell (i + 1) (patchTower i Rg)
  set K := Ball w (s + d * ell ^ i)
  set p := (HK G U K).starProjection (gradAdj U A) with hp
  have hmem : p ∈ HK G U K := Submodule.starProjection_apply_mem _ _
  have hgrad := hharm p hmem
  have hpp : ‖p‖ ^ 2 = ⟪gradAdj U A, p⟫ := by
    have horth : gradAdj U A - p ∈ (HK G U K)ᗮ := Submodule.sub_starProjection_mem_orthogonal _
    have h0 : ⟪gradAdj U A - p, p⟫ = 0 := by
      rw [real_inner_comm]; exact (Submodule.mem_orthogonal (HK G U K) _).mp horth p hmem
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at h0
    linarith
  have hin := inner_le_gradOn U (Ball w s) A p hA
  set c := (((ell : ℝ) ^ (i + 1))⁻¹) ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hw := wnorm_ge_patch ell i hell Rg A
  rw [← hc] at hw
  have hs : Real.sqrt (gradOn U (Ball w s) p) ≤ Real.sqrt (ε * c) * ‖p‖ := by
    rw [← Real.sqrt_sq (norm_nonneg p), ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h1 : ‖p‖ ^ 2 ≤ ‖A‖ * (Real.sqrt (ε * c) * ‖p‖) := by
    rw [hpp]; exact hin.trans (mul_le_mul_of_nonneg_left hs (norm_nonneg _))
  have h2 : ‖p‖ ≤ ‖A‖ * Real.sqrt (ε * c) := by
    rcases (norm_nonneg p).eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · have : ‖p‖ * ‖p‖ ≤ (‖A‖ * Real.sqrt (ε * c)) * ‖p‖ := by nlinarith
      exact le_of_mul_le_mul_right this hpos
  have h3 : ‖p‖ ^ 2 ≤ ‖A‖ ^ 2 * (ε * c) := by
    have := pow_le_pow_left₀ (norm_nonneg p) h2 2
    rw [mul_pow, Real.sq_sqrt (by positivity)] at this
    exact this
  calc ‖p‖ ^ 2 ≤ ‖A‖ ^ 2 * (ε * c) := h3
    _ = ε * (c * ‖A‖ ^ 2) := by ring
    _ ≤ ε * AdalyFormal.M1.wnormSq (patchTower i Rg) ell (i + 1) A := mul_le_mul_of_nonneg_left hw hε

/-- **local W3 at one level and one ball**. -/
theorem w3loc_lev (ell : ℕ) (hell : 0 < ell) (U : Cfg L) (i : ℕ) (Rg : Set (PeriodicLatticeSite L)) (a cW ε : ℝ)
    (hε : 0 ≤ ε) (d : ℕ) (w : PeriodicLatticeSite L) (s : ℕ)
    (hharm : ∀ h ∈ HK (geomOf ell (i + 1) (patchTower i Rg)) U (Ball w (s + d * ell ^ i)),
      gradOn U (Ball w s) h ≤ ε * (((ell : ℝ) ^ (i + 1))⁻¹) ^ 2 * ‖h‖ ^ 2)
    (A : BondFnL2 L)
    (hA : ∀ b : Bond L, (WithLp.ofLp A) b ≠ 0 → b.1 ∈ Ball w s ∨ periodicLatticeShift b.1 b.2 ∈ Ball w s)
    (hG0 : cW * AdalyFormal.M1.wnormSq (patchTower i Rg) ell (i + 1) A ≤ G0form (patchTower i Rg) ell (i + 1) U a A) :
    (cW - ε) * AdalyFormal.M1.wnormSq (patchTower i Rg) ell (i + 1) A
      ≤ locG0 (patchTower i Rg) ell (i + 1) U a (Ball w (s + d * ell ^ i)) A := by
  have h2 := optDecay_lev ell hell U i Rg ε hε d w s hharm A hA
  rw [← G0_sub_defK]
  nlinarith

end AdalyFormal.M1NonFlat

#print axioms AdalyFormal.M1NonFlat.optDecay_lev
#print axioms AdalyFormal.M1NonFlat.w3loc_lev
