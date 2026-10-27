import NB13
/-!
# RKL1 -- the LINEAR (Lie-algebra) truncated blocking `blkM` (NB2) at ANY bond: linearity, exact transport of
gradients, and the exact decomposition  `blkM f = avgM f + grad (G f) + Es f`.

`blkM s ell f c = Σ_{x ∈ B_s(c₋)} ell⁻³ • loopM f c x + bondM f c` with the tree's TRUNCATED block `stepBlockOf`.
* `blkM_grad`: `blkM s ell (grad s Λ) = grad (s·ell) Λ` (every bond; truncation irrelevant: loops of gradients vanish).
* `blkM_decomp`: `blkM s ell f c = avgM s ell f c + grad (s·ell) (Gs s ell f) c + Es s ell f c` where
  `avgM` is a convex combination of straight lines (weights `1 − |B|/ell³` and `ell⁻³`), `Gs` the block-averaged
  staircase from a site, `Es` the truncation MISMATCH between the blocks of `c₋` and `c₊`.
Kernel-checked; standard axioms only (see the #print axioms lines).
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.RegBgKU
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (M2)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath coarsePathEndpoint)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf coarsePathEndpoint_append)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS cPlusS_eq coarsePathEndpoint_coarseShift)
open AdalyFormal.CurvBlock (pathM bondM loopM blkM off gamma_end endpoint_rep)

variable {L : PeriodicLatticeExtent}

/-- link fields (Lie-algebra valued). -/
abbrev Fld (L : PeriodicLatticeExtent) : Type := PeriodicLatticeEdge L → M2

theorem pathM_add (s : ℕ) (f g : Fld L) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L), pathM s (f + g) y p = pathM s f y p + pathM s g y p := by
  intro p; induction p with
  | nil => intro y; simp [pathM]
  | cons μ r ih => intro y; simp only [pathM, ih, Pi.add_apply]; abel

theorem pathM_neg (s : ℕ) (f : Fld L) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L), pathM s (-f) y p = - pathM s f y p := by
  intro p; induction p with
  | nil => intro y; simp [pathM]
  | cons μ r ih => intro y; simp only [pathM, ih, Pi.neg_apply]; abel

theorem pathM_zero (s : ℕ) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L), pathM s (0 : Fld L) y p = 0 := by
  intro p; induction p with
  | nil => intro y; simp [pathM]
  | cons μ r ih => intro y; simp only [pathM, ih, Pi.zero_apply]; abel

theorem blkM_add (s ell : ℕ) (f g : Fld L) : blkM s ell (f + g) = blkM s ell f + blkM s ell g := by
  funext c
  simp only [blkM, loopM, bondM, pathM_add, Pi.add_apply, smul_add, Finset.sum_add_distrib, smul_sub,
    Finset.sum_sub_distrib]
  abel

theorem blkM_neg (s ell : ℕ) (f : Fld L) : blkM s ell (-f) = - blkM s ell f := by
  funext c
  simp only [blkM, loopM, bondM, pathM_neg, Pi.neg_apply, smul_neg, Finset.sum_neg_distrib, smul_sub,
    Finset.sum_sub_distrib, smul_add, Finset.sum_add_distrib]
  abel

theorem blkM_sub (s ell : ℕ) (f g : Fld L) : blkM s ell (f - g) = blkM s ell f - blkM s ell g := by
  rw [sub_eq_add_neg, blkM_add, blkM_neg, ← sub_eq_add_neg]

theorem blkM_zero (s ell : ℕ) : blkM s ell (0 : Fld L) = 0 := by
  funext c; simp [blkM, loopM, bondM, pathM_zero]

/-- the stride-`s` gradient of a site function: `(dΛ)(b) = Λ(b₋) − Λ(b₊)`. -/
def grad (s : ℕ) (Λ : PeriodicLatticeSite L → M2) : Fld L := fun b => Λ b.1 - Λ (coarseShift b.1 s b.2)

theorem pathM_grad (s : ℕ) (Λ : PeriodicLatticeSite L → M2) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L),
      pathM s (grad s Λ) y p = Λ y - Λ (coarsePathEndpoint s y p) := by
  intro p; induction p with
  | nil => intro y; simp [pathM, coarsePathEndpoint]
  | cons μ r ih =>
      intro y
      simp only [pathM, ih, grad]
      show _ = Λ y - Λ (coarsePathEndpoint s (coarseShift y s μ) r)
      abel

/-- **Gradients are transported exactly, at every bond (truncated blocks included).** -/
theorem blkM_grad (s ell : ℕ) (Λ : PeriodicLatticeSite L → M2) :
    blkM s ell (grad s Λ) = grad (s * ell) Λ := by
  funext c
  have hloop : ∀ x ∈ stepBlockOf c.1 s ell, loopM s ell (grad s Λ) c x = 0 := by
    intro x hx
    have hx' := mem_stepBlockOf.mp hx
    have hoff : ∀ σ, s ∣ off c.1 x σ := by
      intro σ
      have h := hx' σ
      unfold off
      rw [Fin.sub_val_of_le h.1]
      exact h.2.2
    have hg := gamma_end s c.1 x hoff
    unfold loopM bondM
    rw [pathM_grad, pathM_grad, pathM_grad, pathM_grad, hg, endpoint_rep, endpoint_rep, cPlusS_eq,
      coarsePathEndpoint_coarseShift, hg]
    abel
  unfold blkM
  rw [Finset.sum_eq_zero (fun x hx => by rw [hloop x hx, smul_zero]), zero_add]
  unfold bondM
  rw [pathM_grad, endpoint_rep]
  rfl

/-- straight-line average: weights `1 − |B|/ell³` on the bond itself and `ell⁻³` on each block line. -/
def avgM (s ell : ℕ) (f : Fld L) : Fld L := fun c =>
  (1 - ((stepBlockOf c.1 s ell).card : ℝ) / (ell : ℝ) ^ 3) • bondM s ell f c
    + ∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℝ) ^ 3)⁻¹ • pathM s f x (List.replicate ell c.2)

/-- block-averaged staircase from a site. -/
def Gs (s ell : ℕ) (f : Fld L) : PeriodicLatticeSite L → M2 := fun z =>
  ∑ x ∈ stepBlockOf z s ell, ((ell : ℝ) ^ 3)⁻¹ • pathM s f z (coarseGammaPath s z x)

/-- truncation mismatch between the block of `c₊` and the (translated) block of `c₋`. -/
def Es (s ell : ℕ) (f : Fld L) : Fld L := fun c =>
  Gs s ell f (cPlusS s ell c)
    - ∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℝ) ^ 3)⁻¹ • pathM s f (cPlusS s ell c) (coarseGammaPath s c.1 x)

/-- **Exact decomposition of the truncated linear blocking.** -/
theorem blkM_decomp (s ell : ℕ) (f : Fld L) (c : PeriodicLatticeEdge L) :
    blkM s ell f c = avgM s ell f c + grad (s * ell) (Gs s ell f) c + Es s ell f c := by
  have hcp : cPlusS s ell c = coarseShift c.1 (s * ell) c.2 := cPlusS_eq s ell c
  unfold blkM avgM grad Es Gs loopM
  rw [← hcp]
  simp only [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, sub_smul,
    one_smul, div_eq_mul_inv, mul_smul]
  simp only [Nat.cast_smul_eq_nsmul]
  abel

#print axioms blkM_add
#print axioms blkM_sub
#print axioms blkM_grad
#print axioms blkM_decomp

#print axioms blkM_neg
#print axioms blkM_zero
#print axioms pathM_grad
#print axioms pathM_add
#print axioms pathM_neg
#print axioms pathM_zero
end AdalyFormal.RegBgKU
