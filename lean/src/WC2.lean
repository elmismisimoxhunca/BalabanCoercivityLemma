import RC2

/-!
# WC2 -- UNCONDITIONAL far-locality of a row of the local composite (M2 W6 lane)

`QlinCompL ell bg j v b = 0` whenever `v` vanishes at every bond based in `Ball b₋ (rhoT ell j)`, for ANY background `bg`
(no regularity): the steps of the r8 local jet are local at every aligned row (`r8Steps_local`), no differentiability needed.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.M2W6

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp Tower pdist)
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.ClassJets (BallA)
open AdalyFormal.ReadsetComplete (r8Steps_local StepLocalAt)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)

variable {L : PeriodicLatticeExtent}

theorem compL_far_zero (ell : ℕ) (hell : 0 < ell) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (J : ℕ)
    (hd : ∀ l, l < J → ∀ ρ : Fin 3, ell ^ l ∣ L ρ + 1) :
    ∀ j, j ≤ J → ∀ (b : PeriodicLatticeEdge L), b.1 ∈ CoarseLattice L (ell ^ j) → ∀ v : XS L,
      (∀ e : PeriodicLatticeEdge L, pdist b.1 e.1 ≤ rhoT ell j → v e = 0) → QlinCompL ell bg j v b = 0 := by
  intro j
  induction j with
  | zero =>
      intro _ b _ v hv
      show v b = 0
      exact hv b (by rw [pdist_self]; exact Nat.zero_le _)
  | succ j ih =>
      intro hj b hb v hv
      have hbs : b.1 ∈ CoarseLattice L (ell ^ j) := by
        rw [mem_CoarseLattice] at hb ⊢
        intro ν
        exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.pow_dvd_pow ell (by omega)) (Nat.dvd_of_mod_eq_zero (hb ν)))
      have hloc := (r8Steps_local ell hell bg j (hd j (by omega)) b hbs).1
      rw [QlinCompL_succ]
      show QlinStepL (ell ^ j) ell (bg j) (QlinCompL ell bg j v) b = 0
      have hQ : (fun l => QlinStepL (ell ^ l) ell (bg l)) j (QlinCompL ell bg j v) b
          = (fun l => QlinStepL (ell ^ l) ell (bg l)) j
            (maskX (BallA b.1 (4 * (ell ^ j * ell)) (ell ^ j)) (QlinCompL ell bg j v)) b := hloc _
      have hz : maskX (BallA b.1 (4 * (ell ^ j * ell)) (ell ^ j)) (QlinCompL ell bg j v) = 0 := by
        funext e
        rw [maskX_apply]
        split_ifs with he
        · have hih := ih (by omega) e he.2 v (fun e' he' => hv e' ?_)
          · exact hih
          · have h1 := pdist_triangle b.1 e.1 e'.1
            have h2 := he.1
            rw [rhoT_succ]
            omega
        · rfl
      simp only at hQ
      rw [hQ, hz, map_zero]
      rfl

end AdalyFormal.M2W6

#print axioms AdalyFormal.M2W6.compL_far_zero
