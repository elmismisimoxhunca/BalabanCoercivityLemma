import CB2
/-!
# CB3 -- the straight tower and its exact curvature blocking

`strT ell U` is the blocking tower WITHOUT the exponential (block-averaged loop) factor:
`strT 0 = U`, `strT (l+1) c = coarseBondVar (ell^l) ell (strT l) c` (the product of the `ell` level-`l`
links along `c`; the tree's `ubarTowerSU2` is `exp(H) * coarseBondVar` of the previous level).

* `pw_strT_succ`: a stride-`ell^(l+1)` plaquette word of `strT (l+1)` IS the `ell × ell` strided
  ladder of `strT l` (exact identity).
* `pw_strT_le`: hence its defect is `≤ ell² ·` (sup of the enclosed level-`l` plaquette defects), and
  iterating, `≤ ell^(2l) · q0` with `q0` the fine (stride-1) plaquette defect bound.  Coefficient
  exactly `ell²` per level, no remainder (nonabelian Stokes via `ladS_le`).
* `strT_link_le`: `dv (strT l c) ≤ ell^l · e` when every fine link has `dv ≤ e`.

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS cPlusS_eq coarseBondVar)

variable {L : PeriodicLatticeExtent}

/-- The straight tower. -/
def strT (ell : ℕ) (U : PeriodicLinkConfiguration SU2 L) : ℕ → PeriodicLinkConfiguration SU2 L
  | 0 => U
  | l + 1 => fun c => coarseBondVar (ell ^ l) ell (strT ell U l) c

theorem pw_strT_succ (ell : ℕ) (U : PeriodicLinkConfiguration SU2 L) (l : ℕ)
    (y : PeriodicLatticeSite L) (ν μ : Fin 3) :
    pw (ell ^ (l + 1)) (strT ell U (l + 1)) y ν μ
      = ladS (ell ^ l) (strT ell U l) y (List.replicate ell ν) μ ell := by
  have he : coarsePathEndpoint (ell ^ l) y (List.replicate ell ν)
      = coarseShift y (ell ^ l * ell) ν := cPlusS_eq (ell ^ l) ell (y, ν)
  unfold pw ladS
  rw [he, pow_succ]
  rfl

/-- One level of exact curvature blocking for the straight tower (local hypotheses). -/
theorem pw_strT_succ_le (ell : ℕ) (U : PeriodicLinkConfiguration SU2 L) (l : ℕ)
    (y : PeriodicLatticeSite L) (ν μ : Fin 3) (q : ℝ)
    (h : ∀ t ∈ ladPlaqs (ell ^ l) μ ell y (List.replicate ell ν),
      dv (pw (ell ^ l) (strT ell U l) t.1 t.2.1 t.2.2) ≤ q) :
    dv (pw (ell ^ (l + 1)) (strT ell U (l + 1)) y ν μ) ≤ (ell : ℝ) ^ 2 * q := by
  rw [pw_strT_succ]
  have := ladS_le (ell ^ l) (strT ell U l) μ ell q (List.replicate ell ν) y h
  rw [List.length_replicate] at this
  calc _ ≤ (ell : ℝ) * ((ell : ℝ) * q) := this
    _ = (ell : ℝ) ^ 2 * q := by ring

/-- **Level-uniform curvature blocking of the straight tower (global form).** -/
theorem pw_strT_le (ell : ℕ) (U : PeriodicLinkConfiguration SU2 L) (q0 : ℝ)
    (h0 : ∀ y ν μ, dv (pw 1 U y ν μ) ≤ q0) :
    ∀ (l : ℕ) (y : PeriodicLatticeSite L) (ν μ : Fin 3),
      dv (pw (ell ^ l) (strT ell U l) y ν μ) ≤ ((ell : ℝ) ^ 2) ^ l * q0 := by
  intro l
  induction l with
  | zero =>
      intro y ν μ
      show dv (pw 1 U y ν μ) ≤ ((ell : ℝ) ^ 2) ^ 0 * q0
      rw [pow_zero, one_mul]; exact h0 y ν μ
  | succ k ih =>
      intro y ν μ
      have := pw_strT_succ_le ell U k y ν μ (((ell : ℝ) ^ 2) ^ k * q0)
        (fun t _ => ih t.1 t.2.1 t.2.2)
      calc _ ≤ (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ k * q0) := this
        _ = ((ell : ℝ) ^ 2) ^ (k + 1) * q0 := by ring

theorem hol_one (s : ℕ) (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    coarsePathHolonomy s (fun _ => (1 : SU2)) y p = 1 := by
  induction p generalizing y with
  | nil => rfl
  | cons μ rest ih =>
      show (1 : SU2) * coarsePathHolonomy s (fun _ => (1 : SU2)) (coarseShift y s μ) rest = 1
      rw [ih, one_mul]

/-- **Straight-tower link bound.** -/
theorem strT_link_le (ell : ℕ) (U : PeriodicLinkConfiguration SU2 L) (e : ℝ)
    (h0 : ∀ b, dv (U b) ≤ e) :
    ∀ (l : ℕ) (c : PeriodicLatticeEdge L), dv (strT ell U l c) ≤ (ell : ℝ) ^ l * e := by
  intro l
  induction l with
  | zero =>
      intro c
      show dv (U c) ≤ (ell : ℝ) ^ 0 * e
      rw [pow_zero, one_mul]; exact h0 c
  | succ k ih =>
      intro c
      have h := path_cmp (ell ^ k) (strT ell U k) (fun _ => (1 : SU2)) ((ell : ℝ) ^ k * e)
        (List.replicate ell c.2) c.1 (fun b _ => by simpa using ih b)
      rw [hol_one, inv_one, mul_one, List.length_replicate] at h
      show dv (coarsePathHolonomy (ell ^ k) (strT ell U k) c.1 (List.replicate ell c.2)) ≤ _
      calc _ ≤ (ell : ℝ) * ((ell : ℝ) ^ k * e) := h
        _ = (ell : ℝ) ^ (k + 1) * e := by ring

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.pw_strT_succ
#print axioms AdalyFormal.CurvBlock.pw_strT_le
#print axioms AdalyFormal.CurvBlock.strT_link_le
