import W2B
import MI34
import PW5

/-!
# W2C1 -- local reading facts used by the W2 bridge (M1 lane W2, 2026-10-13)

Every item is an exact locality statement about an r8 operator (no estimate):
* `gradAdj_congr` : `D_U* A` reads `U` only on bonds where `A ≠ 0`;
* `lapFull_congr_at` : `(D_U* D_U g)(x)` reads `U` only on the six bonds `(x, μ)`, `(x − e_μ, μ)`;
* `curl_zero_of` : the covariant curl at `p` vanishes if `A` vanishes on the four boundary bonds of `p`;
* `curl_congr_U` : the covariant curl at `p` reads `U` only on `(p₁, μ)`, `(p₁, ν)`;
* `Qcomposite_congr_in` : `Q'_j` at `y` reads its input only in `Ball y (rhoT ell j)` (any background);
* `strat_eq_of_agree` : two towers whose `Ω_m` agree at `x` for every `m` and vanish above `k₂ ≤ k₁` have the same stratum at `x`;
* `omGe_patch_iff` : `OmGe` of the patch tower is membership in its `Ω_m` (`m ≥ 1`), for `Rg` a union of `ell^{i+1}`-blocks.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M1W2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower BlockClosed)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap gradValueCovariant curlValueCovariant)
open AdalyFormal.Balaban.CovariantHjMinimizer (gradCovariantAdjointValue periodicLatticeShiftBack)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf)
open AdalyFormal.Balaban.QjComposite (Qcomposite)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt mem_Ball_self Ball_sub rhoT rhoT_succ stepAverage_congr)

variable {L : PeriodicLatticeExtent}

/-! ## 1. `D*` and `D*D` -/

theorem gradAdj_congr (U₁ U₂ : Cfg L) (A : BondFnL2 L)
    (h : ∀ b : Bond L, (WithLp.ofLp A) b ≠ 0 → U₁ b = U₂ b) : gradAdj U₁ A = gradAdj U₂ A := by
  refine PiLp.ext (fun x => ?_)
  show (WithLp.ofLp (gradAdj U₁ A)) x = (WithLp.ofLp (gradAdj U₂ A)) x
  rw [gradAdj_apply, gradAdj_apply]
  unfold gradCovariantAdjointValue
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  by_cases h0 : (WithLp.ofLp A) (periodicLatticeShiftBack x μ, μ) = 0
  · rw [h0, map_zero, map_zero]
  · rw [h _ h0]

theorem lapFull_congr_at (U₁ U₂ : Cfg L) (g : SiteL2 L) (x : PeriodicLatticeSite L)
    (h1 : ∀ μ : Fin 3, U₁ (x, μ) = U₂ (x, μ))
    (h2 : ∀ μ : Fin 3, U₁ (periodicLatticeShiftBack x μ, μ) = U₂ (periodicLatticeShiftBack x μ, μ)) :
    (lapFull U₁ g) x = (lapFull U₂ g) x := by
  unfold lapFull
  show (WithLp.ofLp (gradAdj U₁ (gradL2 U₁ g))) x = (WithLp.ofLp (gradAdj U₂ (gradL2 U₂ g))) x
  rw [gradAdj_apply, gradL2_apply, gradAdj_apply, gradL2_apply]
  unfold gradCovariantAdjointValue gradValueCovariant
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [h1 μ, h2 μ]

/-! ## 2. the covariant curl -/

theorem curl_zero_of (U : Cfg L) (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L)
    (h : ∀ e ∈ periodicPlaquetteBoundaryEdges p, A e = 0) : curlValueCovariant U A p = 0 := by
  have e1 := h _ ((AdalyFormal.StatementLaneR6.edge_mem p _).mpr (Or.inl rfl))
  have e2 := h _ ((AdalyFormal.StatementLaneR6.edge_mem p _).mpr (Or.inr (Or.inl rfl)))
  have e3 := h _ ((AdalyFormal.StatementLaneR6.edge_mem p _).mpr (Or.inr (Or.inr (Or.inl rfl))))
  have e4 := h _ ((AdalyFormal.StatementLaneR6.edge_mem p _).mpr (Or.inr (Or.inr (Or.inr rfl))))
  unfold curlValueCovariant
  rw [e1, e2, e3, e4]
  simp

theorem curl_congr_U (U₁ U₂ : Cfg L) (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L)
    (h : ∀ e ∈ periodicPlaquetteBoundaryEdges p, U₁ e = U₂ e) :
    curlValueCovariant U₁ A p = curlValueCovariant U₂ A p :=
  AdalyFormal.StatementLaneR6.curlValue_congr h A

/-! ## 3. input locality of the site composite `Q'_j` -/

theorem Qcomposite_congr_in (bg : ℕ → Cfg L) (ell : ℕ) (hell : 0 < ell) (j : ℕ) :
    ∀ (y : PeriodicLatticeSite L) (lam lam' : PeriodicLatticeSite L → SuTwo),
      (∀ x ∈ Ball y (rhoT ell j), lam x = lam' x) → Qcomposite bg ell j lam y = Qcomposite bg ell j lam' y := by
  induction j with
  | zero => intro y lam lam' h; exact h y (mem_Ball_self _ _)
  | succ j ih =>
      intro y lam lam' h
      show AdalyFormal.Balaban.QjComposite.stepAverage (ell ^ j) (bg j) ell (Qcomposite bg ell j lam) y
        = AdalyFormal.Balaban.QjComposite.stepAverage (ell ^ j) (bg j) ell (Qcomposite bg ell j lam') y
      refine stepAverage_congr _ ell (pow_pos hell j) y (fun _ _ _ => rfl) ?_
      intro x hx
      refine ih x lam lam' (fun z hz => h z (Ball_sub hx ?_ hz))
      rw [rhoT_succ]
      have : 3 * (ell ^ j * ell) ≤ 4 * (ell ^ j * ell) := by omega
      omega

theorem Qcomposite_zero_of (bg : ℕ → Cfg L) (ell : ℕ) (hell : 0 < ell) (j : ℕ) (y : PeriodicLatticeSite L)
    (lam : PeriodicLatticeSite L → SuTwo) (h : ∀ x ∈ Ball y (rhoT ell j), lam x = 0) :
    Qcomposite bg ell j lam y = 0 := by
  rw [Qcomposite_congr_in bg ell hell j y lam 0 h]
  have := (AdalyFormal.Balaban.QjComposite.QcompositeLM bg ell j).map_zero
  have h2 : Qcomposite bg ell j 0 = 0 := this
  rw [h2]; rfl

/-! ## 4. strata of two towers agreeing at a site -/

open Classical in
theorem findGreatest_congr_le (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q] (n₁ n₂ : ℕ) (h12 : n₂ ≤ n₁)
    (hPQ : ∀ m, P m ↔ Q m) (hQ : ∀ m, n₂ < m → ¬ Q m) : Nat.findGreatest P n₁ = Nat.findGreatest Q n₂ := by
  induction n₁ with
  | zero =>
      have : n₂ = 0 := by omega
      subst this
      simp
  | succ n ih =>
      rcases Nat.eq_or_lt_of_le h12 with e | e
      · subst e
        have hPQ' : P = Q := funext (fun m => propext (hPQ m))
        subst hPQ'
        congr
      · rw [Nat.findGreatest_succ]
        have hn : ¬ P (n + 1) := fun hp => hQ (n + 1) e ((hPQ _).mp hp)
        rw [if_neg hn]
        exact ih (by omega)

theorem strat_eq_of_agree (S₁ S₂ : Tower L) (k₁ k₂ : ℕ) (h12 : k₂ ≤ k₁) (x : PeriodicLatticeSite L)
    (hag : ∀ m, x ∈ S₁.Om m ↔ x ∈ S₂.Om m) (hvan : ∀ m, k₂ < m → x ∉ S₂.Om m) :
    AdalyFormal.M1.strat S₁ k₁ x = AdalyFormal.M1.strat S₂ k₂ x := by
  classical
  unfold AdalyFormal.M1.strat
  exact findGreatest_congr_le _ _ k₁ k₂ h12 hag hvan

/-! ## 5. `OmGe` of the patch tower -/

section patch
variable {ell i : ℕ} (hell : 0 < ell) {Rg : Set (PeriodicLatticeSite L)} (hRg : BlockClosed (ell ^ (i + 1)) Rg)
include hell hRg

open AdalyFormal.M1Patch in
theorem omGe_patch_iff (m : ℕ) (hm : 1 ≤ m) (x : PeriodicLatticeSite L) :
    OmGe (geomOf ell (i + 1) (patchTower i Rg)) m x ↔ x ∈ (patchTower i Rg).Om m := by
  rcases Nat.lt_or_ge (i + 1) m with hgt | hle
  · rw [om_gt i Rg hgt]
    exact ⟨fun h => not_OmGe_of_lt (G := geomOf ell (i + 1) (patchTower i Rg)) (show i + 1 < m from hgt) x h,
      fun h => h.elim⟩
  · rcases Nat.eq_or_lt_of_le hle with e | hlt
    · subst e
      rw [om_succ]
      exact ⟨fun h => by_contra (fun hn => not_omGe_of_not_mem hell hRg x hn h), fun h => omGe_of_mem hell hRg x h⟩
    · rw [om_le i Rg (by omega : m ≤ i)]
      simp only [Set.mem_univ, iff_true]
      by_cases hx : x ∈ Rg
      · have h := omGe_of_mem hell hRg x hx
        obtain ⟨i', h1, h2, y, hy, hxy⟩ := h
        exact ⟨i', by omega, h2, y, hy, hxy⟩
      · refine ⟨i, by omega, by show i ≤ i + 1; omega, corner (ell ^ i) x, ?_, ?_⟩
        · rw [mem_lam_j]
          refine ⟨corner_dvd _ x, fun hc => hx (hRg _ hc x (fun μ => ?_))⟩
          exact (same_big_block hell (corner_dvd _ x) (mem_block_corner (pow_pos hell _) x) μ).symm
        · exact mem_blockOf.mp (mem_block_corner (pow_pos hell _) x)

end patch

end AdalyFormal.M1W2

#print axioms AdalyFormal.M1W2.gradAdj_congr
#print axioms AdalyFormal.M1W2.lapFull_congr_at
#print axioms AdalyFormal.M1W2.curl_zero_of
#print axioms AdalyFormal.M1W2.curl_congr_U
#print axioms AdalyFormal.M1W2.Qcomposite_congr_in
#print axioms AdalyFormal.M1W2.Qcomposite_zero_of
#print axioms AdalyFormal.M1W2.findGreatest_congr_le
#print axioms AdalyFormal.M1W2.strat_eq_of_agree
#print axioms AdalyFormal.M1W2.omGe_patch_iff
