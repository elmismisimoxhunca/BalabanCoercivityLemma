import CB5
/-!
# CB6 -- LOCAL form: the bounds hold wherever the dependency cone sits in the controlled region

`R` is any set of fine plaquette words (e.g. those of a class cube, where the printed class controls
the curvature); `goodP ell R l t` / `goodB ell R l c` say that every fine plaquette word read by the
computation of the level-`l` plaquette `t` / level-`l` defect at bond `c` lies in `R` (defined by the
same recursion as the blocking itself; no geometry is assumed).  `Rl` is a set of fine links;
`goodL ell Rl l c` says the straight transport of `c` reads only links in `Rl`.

* `pw_strT_le_loc`, `defect_tower_loc`, `link_tower_loc`, `curv_tower_loc`: the CB5 bounds with all
  hypotheses restricted to the cone.  The defect bound needs NO link hypothesis at all (it is gauge
  invariant: only plaquettes enter); the link bound needs fine links only along straight paths
  (in whatever gauge the links are bounded, e.g. the class cube's).
* `goodP_univ`, `goodB_univ`, `goodL_univ`: with `R = Rl = everything` every cone is good, so CB5's
  global statements are the special case (non-vacuity of the local predicates).

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.UbarTowerCov (coarseBondVar)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2 ubarTowerSU2)
open AdalyFormal.Balaban.ClassPropagationUbar (blkConstOf)

variable {L : PeriodicLatticeExtent}

abbrev PlaqT (L : PeriodicLatticeExtent) := PeriodicLatticeSite L × Fin 3 × Fin 3

/-- Plaquette cone. -/
def goodP (ell : ℕ) (R : PlaqT L → Prop) : ℕ → PlaqT L → Prop
  | 0, t => R t
  | l + 1, t => ∀ t' ∈ ladPlaqs (ell ^ l) t.2.2 ell t.1 (List.replicate ell t.2.1), goodP ell R l t'

/-- Defect cone. -/
def goodB (ell : ℕ) (R : PlaqT L → Prop) : ℕ → PeriodicLatticeEdge L → Prop
  | 0, _ => True
  | l + 1, c =>
      (∀ x ∈ stepBlockOf c.1 (ell ^ l) ell, ∀ b ∈ loopBonds (ell ^ l) ell c x, goodB ell R l b)
      ∧ (∀ b ∈ pathBonds (ell ^ l) c.1 (List.replicate ell c.2), goodB ell R l b)
      ∧ (∀ x ∈ stepBlockOf c.1 (ell ^ l) ell,
          ∀ t ∈ ladPlaqs (ell ^ l) c.2 ell c.1 (coarseGammaPath (ell ^ l) c.1 x), goodP ell R l t)

/-- Straight-link cone. -/
def goodL (ell : ℕ) (Rl : PeriodicLatticeEdge L → Prop) : ℕ → PeriodicLatticeEdge L → Prop
  | 0, b => Rl b
  | l + 1, c => ∀ b ∈ pathBonds (ell ^ l) c.1 (List.replicate ell c.2), goodL ell Rl l b

theorem pw_strT_le_loc (ell : ℕ) (U : PeriodicLinkConfiguration SU2 L) (R : PlaqT L → Prop)
    (q0 : ℝ) (h0 : ∀ t, R t → dv (pw 1 U t.1 t.2.1 t.2.2) ≤ q0) :
    ∀ (l : ℕ) (t : PlaqT L), goodP ell R l t →
      dv (pw (ell ^ l) (strT ell U l) t.1 t.2.1 t.2.2) ≤ ((ell : ℝ) ^ 2) ^ l * q0 := by
  intro l
  induction l with
  | zero =>
      intro t ht
      show dv (pw 1 U t.1 t.2.1 t.2.2) ≤ ((ell : ℝ) ^ 2) ^ 0 * q0
      rw [pow_zero, one_mul]; exact h0 t ht
  | succ k ih =>
      intro t ht
      have := pw_strT_succ_le ell U k t.1 t.2.1 t.2.2 (((ell : ℝ) ^ 2) ^ k * q0)
        (fun t' h' => ih t' (ht t' h'))
      calc _ ≤ (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ k * q0) := this
        _ = ((ell : ℝ) ^ 2) ^ (k + 1) * q0 := by ring

/-- **Local level-uniform defect tower.** -/
theorem defect_tower_loc (ell : ℕ) (hell : 0 < ell) (hr : blkConstOf ell < (ell : ℝ) ^ 2)
    (U : PeriodicLinkConfiguration SU2 L) (R : PlaqT L → Prop) (q0 : ℝ) (hq0 : 0 ≤ q0)
    (h0 : ∀ t, R t → dv (pw 1 U t.1 t.2.1 t.2.2) ≤ q0) :
    ∀ (l : ℕ) (c : PeriodicLatticeEdge L), goodB ell R l c →
      dv (ubarTowerSU2 ell U l c * (strT ell U l c)⁻¹) ≤ KC ell * ((ell : ℝ) ^ 2) ^ l * q0 := by
  have hK := KC_nonneg ell hell hr
  have hKe := KC_eq ell hr
  intro l
  induction l with
  | zero =>
      intro c _
      show dv (U c * (U c)⁻¹) ≤ _
      rw [mul_inv_cancel, dv_one, pow_zero, mul_one]; exact mul_nonneg hK hq0
  | succ k ih =>
      intro c hc
      obtain ⟨hc1, hc2, hc3⟩ := hc
      have hs : 0 < ell ^ k := pow_pos hell k
      set X : ℝ := ((ell : ℝ) ^ 2) ^ k * q0
      have hX : 0 ≤ X := by positivity
      have hq := pw_strT_le_loc ell U R q0 h0 k
      have hstep := defect_step (ell ^ k) ell hs hell (ubarTowerSU2 ell U k) (strT ell U k) c
        (KC ell * X) X (by positivity) hX
        (fun x hx b hb => (ih b (hc1 x hx b hb)).trans (le_of_eq (by simp only [X]; ring)))
        (fun b hb => (ih b (hc2 b hb)).trans (le_of_eq (by simp only [X]; ring)))
        (fun x hx t ht => hq t (hc3 x hx t ht))
      have hsh : ubarTowerSU2 ell U (k + 1) c * (strT ell U (k + 1) c)⁻¹
          = ubarSU2 (ell ^ k) ell (ubarTowerSU2 ell U k) c
            * (coarseBondVar (ell ^ k) ell (strT ell U k) c)⁻¹ := rfl
      rw [hsh]
      refine le_trans hstep (le_of_eq ?_)
      have hb : blkConstOf ell = (ell : ℝ) + Real.pi / 2 * (8 * (ell : ℝ) - 6) := rfl
      have ha : aC ell = Real.pi / 2 * (3 * ((ell : ℝ) - 1) * (ell : ℝ)) := rfl
      have hpow : ((ell : ℝ) ^ 2) ^ (k + 1) * q0 = (ell : ℝ) ^ 2 * X := by
        simp only [X]; ring
      rw [mul_assoc (KC ell), hpow]
      rw [hb, ha] at hKe
      linear_combination (-X) * hKe

theorem strT_link_le_loc (ell : ℕ) (U : PeriodicLinkConfiguration SU2 L)
    (Rl : PeriodicLatticeEdge L → Prop) (e : ℝ) (h0 : ∀ b, Rl b → dv (U b) ≤ e) :
    ∀ (l : ℕ) (c : PeriodicLatticeEdge L), goodL ell Rl l c →
      dv (strT ell U l c) ≤ (ell : ℝ) ^ l * e := by
  intro l
  induction l with
  | zero =>
      intro c hc
      show dv (U c) ≤ (ell : ℝ) ^ 0 * e
      rw [pow_zero, one_mul]; exact h0 c hc
  | succ k ih =>
      intro c hc
      have h := path_cmp (ell ^ k) (strT ell U k) (fun _ => (1 : SU2)) ((ell : ℝ) ^ k * e)
        (List.replicate ell c.2) c.1 (fun b hb => by
          rw [inv_one, mul_one]; exact ih b (hc b hb))
      rw [hol_one, inv_one, mul_one, List.length_replicate] at h
      show dv (coarsePathHolonomy (ell ^ k) (strT ell U k) c.1 (List.replicate ell c.2)) ≤ _
      calc _ ≤ (ell : ℝ) * ((ell : ℝ) ^ k * e) := h
        _ = (ell : ℝ) ^ (k + 1) * e := by ring

/-- **Local link tower** (links in any gauge in which the straight-cone links are bounded). -/
theorem link_tower_loc (ell : ℕ) (hell : 0 < ell) (hr : blkConstOf ell < (ell : ℝ) ^ 2)
    (U : PeriodicLinkConfiguration SU2 L) (R : PlaqT L → Prop) (Rl : PeriodicLatticeEdge L → Prop)
    (q0 e : ℝ) (hq0 : 0 ≤ q0) (h0 : ∀ t, R t → dv (pw 1 U t.1 t.2.1 t.2.2) ≤ q0)
    (he : ∀ b, Rl b → dv (U b) ≤ e) (l : ℕ) (c : PeriodicLatticeEdge L)
    (hcB : goodB ell R l c) (hcL : goodL ell Rl l c) :
    dv (ubarTowerSU2 ell U l c) ≤ (ell : ℝ) ^ l * e + KC ell * ((ell : ℝ) ^ 2) ^ l * q0 := by
  have h1 := defect_tower_loc ell hell hr U R q0 hq0 h0 l c hcB
  have h2 := strT_link_le_loc ell U Rl e he l c hcL
  have hid : ubarTowerSU2 ell U l c
      = (ubarTowerSU2 ell U l c * (strT ell U l c)⁻¹) * strT ell U l c := by group
  rw [hid]
  have := dv_mul (ubarTowerSU2 ell U l c * (strT ell U l c)⁻¹) (strT ell U l c)
  linarith

/-- **Local level-uniform curvature blocking of the genuine tower.** -/
theorem curv_tower_loc (ell : ℕ) (hell : 0 < ell) (hr : blkConstOf ell < (ell : ℝ) ^ 2)
    (U : PeriodicLinkConfiguration SU2 L) (R : PlaqT L → Prop) (q0 : ℝ) (hq0 : 0 ≤ q0)
    (h0 : ∀ t, R t → dv (pw 1 U t.1 t.2.1 t.2.2) ≤ q0) (l : ℕ) (y : PeriodicLatticeSite L)
    (ν μ : Fin 3) (hP : goodP ell R l (y, ν, μ))
    (h1 : goodB ell R l (y, ν)) (h2 : goodB ell R l (coarseShift y (ell ^ l) ν, μ))
    (h3 : goodB ell R l (coarseShift y (ell ^ l) μ, ν)) (h4 : goodB ell R l (y, μ)) :
    dv (pw (ell ^ l) (ubarTowerSU2 ell U l) y ν μ)
      ≤ (4 * KC ell + 1) * ((ell : ℝ) ^ 2) ^ l * q0 := by
  have hD := defect_tower_loc ell hell hr U R q0 hq0 h0 l
  have hT := pw_strT_le_loc ell U R q0 h0 l (y, ν, μ) hP
  have hc := four_cmp
    (ubarTowerSU2 ell U l (y, ν) * (strT ell U l (y, ν))⁻¹)
    (ubarTowerSU2 ell U l (coarseShift y (ell ^ l) ν, μ)
      * (strT ell U l (coarseShift y (ell ^ l) ν, μ))⁻¹)
    (ubarTowerSU2 ell U l (coarseShift y (ell ^ l) μ, ν)
      * (strT ell U l (coarseShift y (ell ^ l) μ, ν))⁻¹)
    (ubarTowerSU2 ell U l (y, μ) * (strT ell U l (y, μ))⁻¹)
    (strT ell U l (y, ν)) (strT ell U l (coarseShift y (ell ^ l) ν, μ))
    (strT ell U l (coarseShift y (ell ^ l) μ, ν)) (strT ell U l (y, μ))
  simp only [inv_mul_cancel_right] at hc
  have e1 := hD _ h1
  have e2 := hD _ h2
  have e3 := hD _ h3
  have e4 := hD _ h4
  unfold pw at hT ⊢
  linarith

theorem goodP_univ (ell : ℕ) : ∀ (l : ℕ) (t : PlaqT L), goodP ell (fun _ => True) l t := by
  intro l
  induction l with
  | zero => intro t; trivial
  | succ k ih => intro t t' _; exact ih t'

theorem goodB_univ (ell : ℕ) : ∀ (l : ℕ) (c : PeriodicLatticeEdge L),
    goodB ell (fun _ => True) l c := by
  intro l
  induction l with
  | zero => intro c; trivial
  | succ k ih =>
      intro c
      exact ⟨fun x _ b _ => ih b, fun b _ => ih b, fun x _ t _ => goodP_univ ell k t⟩

theorem goodL_univ (ell : ℕ) : ∀ (l : ℕ) (c : PeriodicLatticeEdge L),
    goodL ell (fun _ => True) l c := by
  intro l
  induction l with
  | zero => intro c; trivial
  | succ k ih => intro c b _; exact ih b

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.pw_strT_le_loc
#print axioms AdalyFormal.CurvBlock.defect_tower_loc
#print axioms AdalyFormal.CurvBlock.link_tower_loc
#print axioms AdalyFormal.CurvBlock.curv_tower_loc
#print axioms AdalyFormal.CurvBlock.goodB_univ
