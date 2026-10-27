import TL2a

/-!
# TL3a -- abstract descent calculus for a finite Galois cover (lane m2_thin_20261015)
`Cov D Xt X`: a surjection `π : Xt → X` with a simply transitive-on-fibres family of deck permutations indexed by a finite type `D`.
`ell` = pullback, `sig` = fibre sum (the adjoint of `ell`).  `E1` / `E2` are the two intertwinings; `Desc = E1 ∧ E2` is closed under
composition, sums, adjoints and inverses; `E2` follows from `E1` plus deck-equivariance.
-/
set_option autoImplicit false
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace

structure Cov (D Xt X : Type) [Fintype D] [Fintype Xt] [Fintype X] where
  π : Xt → X
  τ : D → Equiv.Perm Xt
  surj : Function.Surjective π
  π_τ : ∀ d x, π (τ d x) = π x
  free : ∀ x y, π x = π y → ∃! d, τ d x = y

section cov
variable {D Xt X : Type} [Fintype D] [Fintype Xt] [Fintype X] [DecidableEq X] [DecidableEq Xt]
variable (c : Cov D Xt X)

theorem Cov.filter_eq_image (x0 : Xt) :
    Finset.univ.filter (fun xt => c.π xt = c.π x0) = Finset.univ.image (fun d => c.τ d x0) := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hy
    obtain ⟨d, hd, -⟩ := c.free x0 y hy.symm
    exact ⟨d, hd⟩
  · rintro ⟨d, rfl⟩
    exact c.π_τ d x0

theorem Cov.τ_inj (x0 : Xt) : Function.Injective (fun d => c.τ d x0) := by
  intro d d' h
  obtain ⟨e, -, he⟩ := c.free x0 (c.τ d x0) (c.π_τ d x0).symm
  have h1 := he d rfl
  have h2 := he d' h.symm
  rw [h1, h2]

theorem Cov.fibre_card (x : X) : (Finset.univ.filter (fun xt => c.π xt = x)).card = Fintype.card D := by
  obtain ⟨x0, rfl⟩ := c.surj x
  rw [c.filter_eq_image x0, Finset.card_image_of_injective _ (c.τ_inj x0)]
  simp

theorem Cov.fibreCount : FibreCount c.π (Fintype.card D) := c.fibre_card

end cov

section hilb
variable {D Xt X : Type} [Fintype D] [Fintype Xt] [Fintype X] [DecidableEq X] [DecidableEq Xt]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (c : Cov D Xt X)

/-- pullback along the covering projection -/
noncomputable abbrev Cov.ell : PiLp 2 (fun _ : X => E) →L[ℝ] PiLp 2 (fun _ : Xt => E) := liftF c.π

/-- fibre sum -/
noncomputable def Cov.sig : PiLp 2 (fun _ : Xt => E) →L[ℝ] PiLp 2 (fun _ : X => E) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 (fun x => ∑ xt ∈ Finset.univ.filter (fun xt => c.π xt = x), (WithLp.ofLp f) xt)
      map_add' := fun f g => by ext x; simp [Finset.sum_add_distrib]
      map_smul' := fun a f => by ext x; simp [Finset.smul_sum] }

theorem Cov.sig_apply (f : PiLp 2 (fun _ : Xt => E)) (x : X) :
    (c.sig f) x = ∑ xt ∈ Finset.univ.filter (fun xt => c.π xt = x), f xt := rfl

theorem Cov.inner_ell_left (f : PiLp 2 (fun _ : X => E)) (g : PiLp 2 (fun _ : Xt => E)) :
    ⟪c.ell f, g⟫ = ⟪f, c.sig g⟫ := by
  simp only [PiLp.inner_apply, Cov.sig_apply, liftF_apply]
  rw [← Finset.sum_fiberwise (Finset.univ) c.π (fun xt => ⟪f (c.π xt), g xt⟫)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [inner_sum]
  exact Finset.sum_congr rfl (fun xt hxt => by rw [(Finset.mem_filter.mp hxt).2])

theorem Cov.sig_ell (f : PiLp 2 (fun _ : X => E)) : c.sig (c.ell f) = (Fintype.card D : ℝ) • f := by
  ext x
  rw [Cov.sig_apply]
  simp only [liftF_apply]
  rw [Finset.sum_congr rfl (fun xt hxt => by rw [(Finset.mem_filter.mp hxt).2])]
  rw [Finset.sum_const, c.fibre_card x]
  exact (Nat.cast_smul_eq_nsmul ℝ _ _).symm

theorem Cov.ell_inj [Nonempty D] : Function.Injective (c.ell : PiLp 2 (fun _ : X => E) →L[ℝ] _) := by
  intro f g h
  have h1 := congrArg c.sig h
  rw [c.sig_ell, c.sig_ell] at h1
  have hN : (Fintype.card D : ℝ) ≠ 0 := by
    have : 0 < Fintype.card D := Fintype.card_pos
    positivity
  exact smul_right_injective _ hN h1

/-- the deck pullback -/
noncomputable abbrev Cov.pull (d : D) : PiLp 2 (fun _ : Xt => E) →L[ℝ] PiLp 2 (fun _ : Xt => E) := liftF (c.τ d)

theorem Cov.pull_ell (d : D) (f : PiLp 2 (fun _ : X => E)) : c.pull d (c.ell f) = c.ell f := by
  ext x
  simp only [liftF_apply]
  rw [c.π_τ]

theorem Cov.sum_pull (f : PiLp 2 (fun _ : Xt => E)) : ∑ d, c.pull d f = c.ell (c.sig f) := by
  ext x
  simp only [PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply, liftF_apply, Cov.sig_apply]
  rw [c.filter_eq_image x, Finset.sum_image (fun d _ d' _ h => c.τ_inj x h)]

end hilb


section perm
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {Z : Type} [Fintype Z]

theorem inner_liftF_perm (g : Equiv.Perm Z) (u v : PiLp 2 (fun _ : Z => E)) :
    ⟪liftF (⇑g.symm) u, v⟫ = ⟪u, liftF (⇑g) v⟫ := by
  simp only [PiLp.inner_apply, liftF_apply]
  exact (Equiv.sum_comp g (fun z => ⟪u (g.symm z), v z⟫)).symm.trans (by
    refine Finset.sum_congr rfl (fun z _ => ?_)
    simp)

theorem liftF_perm_cancel (g : Equiv.Perm Z) (u : PiLp 2 (fun _ : Z => E)) :
    liftF (⇑g) (liftF (⇑g.symm) u) = u := by
  ext z
  simp [liftF_apply]


theorem adjoint_liftF_perm (g : Equiv.Perm Z) :
    ContinuousLinearMap.adjoint (liftF (E := E) (⇑g)) = liftF (⇑g.symm) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  exact inner_liftF_perm (E := E) g u v


theorem liftF_perm_cancel' (g : Equiv.Perm Z) (u : PiLp 2 (fun _ : Z => E)) :
    liftF (⇑g.symm) (liftF (⇑g) u) = u := by
  ext z
  simp [liftF_apply]

end perm

section pullU
variable {D Xt X : Type} [Fintype D] [Fintype Xt] [Fintype X] [DecidableEq X] [DecidableEq Xt]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (c : Cov D Xt X)

theorem Cov.pull_orth (d : D) :
    (c.pull d : PiLp 2 (fun _ : Xt => E) →L[ℝ] _).comp (ContinuousLinearMap.adjoint (c.pull d)) = ContinuousLinearMap.id ℝ _ ∧
    (ContinuousLinearMap.adjoint (c.pull d)).comp (c.pull d : PiLp 2 (fun _ : Xt => E) →L[ℝ] _) = ContinuousLinearMap.id ℝ _ := by
  have e : ContinuousLinearMap.adjoint (c.pull d : PiLp 2 (fun _ : Xt => E) →L[ℝ] _) = liftF (⇑(c.τ d).symm) :=
    adjoint_liftF_perm (c.τ d)
  rw [e]
  constructor
  · ext1 f; exact liftF_perm_cancel (c.τ d) f
  · ext1 f; exact liftF_perm_cancel' (c.τ d) f

end pullU

end AdalyFormal.Thin
