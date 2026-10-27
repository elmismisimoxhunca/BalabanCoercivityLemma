import GFC9

/-!
# GFC10 -- the torus operators `L1` (curl), `L2` (line-block average at coarse sites), `Dstar`, `lap`, the subspace
`ΔW`, its projection, translations and equivariance.  Standard axioms only.
-/
set_option autoImplicit false
open scoped BigOperators ComplexInnerProductSpace
open AdalyFormal.Target.ClayStatement

namespace AdalyFormal.FlatCoercivity

variable {L : PeriodicLatticeExtent} {n : ℕ}

/-- complex site fields -/
abbrev TS (L : PeriodicLatticeExtent) := EuclideanSpace ℂ (Site L)
/-- complex plaquette-type fields (indexed by `x, μ, ν`) -/
abbrev TP (L : PeriodicLatticeExtent) := EuclideanSpace ℂ (Site L × Fin 3 × Fin 3)

/-- linear maps between `EuclideanSpace`s from coordinate formulas -/
noncomputable def mkE {ι κ : Type*} [Fintype ι] [Fintype κ] (f : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ :=
  (WithLp.linearEquiv 2 ℂ (κ → ℂ)).symm.toLinearMap ∘ₗ f ∘ₗ (WithLp.linearEquiv 2 ℂ (ι → ℂ)).toLinearMap

theorem mkE_apply {ι κ : Type*} [Fintype ι] [Fintype κ] (f : (ι → ℂ) →ₗ[ℂ] (κ → ℂ))
    (A : EuclideanSpace ℂ ι) (k : κ) : mkE f A k = f A.ofLp k := rfl

/-- the curl map -/
noncomputable def L1 (L : PeriodicLatticeExtent) : TB L →ₗ[ℂ] TP L :=
  mkE (LinearMap.pi (fun q : Site L × Fin 3 × Fin 3 =>
    ((1 / Real.sqrt 2 : ℝ) : ℂ) • (LinearMap.proj (R := ℂ) (φ := fun _ : Site L × Fin 3 => ℂ) (q.1 + eU L q.2.1, q.2.2)
      - LinearMap.proj (q.1, q.2.2) - LinearMap.proj (q.1 + eU L q.2.2, q.2.1) + LinearMap.proj (q.1, q.2.1))))

theorem L1_apply (A : TB L) (x : Site L) (μ ν : Fin 3) :
    L1 L A (x, μ, ν) = ((1 / Real.sqrt 2 : ℝ) : ℂ) *
      (A (x + eU L μ, ν) - A (x, ν) - A (x + eU L ν, μ) + A (x, μ)) := rfl


/-- divergence -/
noncomputable def Dst (L : PeriodicLatticeExtent) : TB L →ₗ[ℂ] TS L :=
  mkE (LinearMap.pi (fun x : Site L =>
    ∑ μ : Fin 3, (LinearMap.proj (R := ℂ) (φ := fun _ : Site L × Fin 3 => ℂ) (x - eU L μ, μ)
      - LinearMap.proj (x, μ))))

theorem Dst_apply (A : TB L) (x : Site L) : Dst L A x = ∑ μ : Fin 3, (A (x - eU L μ, μ) - A (x, μ)) := by
  simp [Dst, mkE_apply]

/-- the site Laplacian -/
noncomputable def lapC (L : PeriodicLatticeExtent) : TS L →ₗ[ℂ] TS L :=
  mkE (LinearMap.pi (fun x : Site L =>
    ∑ μ : Fin 3, (2 • LinearMap.proj (R := ℂ) (φ := fun _ : Site L => ℂ) x
      - LinearMap.proj (x + eU L μ) - LinearMap.proj (x - eU L μ))))

theorem lapC_apply (φ : TS L) (x : Site L) :
    lapC L φ x = ∑ μ : Fin 3, (2 * φ x - φ (x + eU L μ) - φ (x - eU L μ)) := by
  simp [lapC, mkE_apply]

/-- coarse sites -/
def Coarse (n : ℕ) (x : Site L) : Prop := ∀ μ, n ∣ (x μ : ℕ)

instance (n : ℕ) (x : Site L) : Decidable (Coarse n x) := by unfold Coarse; infer_instance

/-- the line-block sum at coarse sites (unnormalised `Q`) -/
noncomputable def L2 (hdvd : ∀ μ, n ∣ L μ + 1) : TB L →ₗ[ℂ] TB L :=
  mkE (LinearMap.pi (fun q : Site L × Fin 3 =>
    if Coarse n q.1 then ∑ t : Cell n, ∑ i ∈ Finset.range n,
      LinearMap.proj (R := ℂ) (φ := fun _ : Site L × Fin 3 => ℂ) (q.1 + ιc hdvd t + i • eU L q.2, q.2) else 0))

theorem L2_apply (hdvd : ∀ μ, n ∣ L μ + 1) (A : TB L) (x : Site L) (μ : Fin 3) :
    L2 hdvd A (x, μ) = if Coarse n x then ∑ t : Cell n, ∑ i ∈ Finset.range n, A (x + ιc hdvd t + i • eU L μ, μ) else 0 := by
  unfold L2
  rw [mkE_apply]
  by_cases h : Coarse n x <;> simp [h]

/-- translation by `n g` of any field over `Site L × β` -/
noncomputable def permE {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ.symm

theorem permE_apply {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (f : EuclideanSpace ℂ ι) (j : ι) :
    permE σ f j = f (σ j) := by
  simp [permE]

/-- translation of `Site L × β`-indexed fields by `n • g` -/
noncomputable def shiftE (n : ℕ) (g : Site L) (β : Type*) [Fintype β] :
    EuclideanSpace ℂ (Site L × β) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Site L × β) :=
  permE (Equiv.prodCongr (Equiv.addRight (n • g)) (Equiv.refl β))

theorem shiftE_apply (n : ℕ) (g : Site L) (β : Type*) [Fintype β] (f : EuclideanSpace ℂ (Site L × β)) (x : Site L) (b : β) :
    shiftE n g β f (x, b) = f (x + n • g, b) := by
  simp [shiftE, permE_apply]

/-- translation of site fields -/
noncomputable def shiftS (n : ℕ) (g : Site L) : TS L ≃ₗᵢ[ℂ] TS L :=
  permE (Equiv.addRight (n • g))

theorem shiftS_apply (n : ℕ) (g : Site L) (f : TS L) (x : Site L) : shiftS n g f x = f (x + n • g) := by
  simp [shiftS, permE_apply]

theorem L1_equiv (g : Site L) (A : TB L) :
    L1 L (shiftE n g (Fin 3) A) = shiftE n g (Fin 3 × Fin 3) (L1 L A) := by
  ext ⟨x, μ, ν⟩
  simp only [L1_apply, shiftE_apply]
  simp only [add_right_comm _ (eU L _) (n • g)]


theorem Dst_equiv (g : Site L) (A : TB L) :
    Dst L (shiftE n g (Fin 3) A) = shiftS n g (Dst L A) := by
  ext x
  rw [Dst_apply, shiftS_apply, Dst_apply]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  simp only [shiftE_apply, sub_add_eq_add_sub]

theorem lapC_equiv (g : Site L) (φ : TS L) :
    lapC L (shiftS n g φ) = shiftS n g (lapC L φ) := by
  ext x
  simp only [lapC_apply, shiftS_apply]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  simp only [sub_add_eq_add_sub, add_right_comm x (eU L μ) (n • g)]

theorem coarse_add (hdvd : ∀ μ, n ∣ L μ + 1) (x g : Site L) : Coarse n (x + n • g) ↔ Coarse n x := by
  have key : ∀ μ, ((x + n • g) μ : ℕ) % n = (x μ : ℕ) % n := by
    intro μ
    have h1 : ((x + n • g) μ : ℕ) = ((x μ : ℕ) + ((n • g μ : Fin (L μ + 1)) : ℕ)) % (L μ + 1) := by
      simp [Fin.val_add]
    rw [h1, Nat.mod_mod_of_dvd _ (hdvd μ), Nat.add_mod, fin_val_nsmul, Nat.mod_mod_of_dvd _ (hdvd μ)]
    simp [Nat.mul_mod_right]
  constructor
  · intro h μ
    have := h μ
    rw [Nat.dvd_iff_mod_eq_zero] at this ⊢
    rw [← key μ]; exact this
  · intro h μ
    have := h μ
    rw [Nat.dvd_iff_mod_eq_zero] at this ⊢
    rw [key μ]; exact this

theorem L2_equiv (hdvd : ∀ μ, n ∣ L μ + 1) (g : Site L) (A : TB L) :
    L2 hdvd (shiftE n g (Fin 3) A) = shiftE n g (Fin 3) (L2 hdvd A) := by
  ext ⟨x, μ⟩
  rw [L2_apply, shiftE_apply, L2_apply]
  by_cases h : Coarse n x
  · have h' : Coarse n (x + n • g) := (coarse_add hdvd x g).mpr h
    simp only [h, h', if_true, shiftE_apply, add_right_comm _ _ (n • g)]
  · have h' : ¬ Coarse n (x + n • g) := fun hh => h ((coarse_add hdvd x g).mp hh)
    simp [h, h']


/-- block-mean-zero site fields -/
def Wc (hdvd : ∀ μ, n ∣ L μ + 1) : Submodule ℂ (TS L) where
  carrier := {φ | ∀ c : Site L, Coarse n c → ∑ t : Cell n, φ (c + ιc hdvd t) = 0}
  zero_mem' := by intro c _; simp
  add_mem' := by
    intro a b ha hb c hc
    simp only [PiLp.add_apply, Finset.sum_add_distrib]
    rw [ha c hc, hb c hc, add_zero]
  smul_mem' := by
    intro r a ha c hc
    simp only [PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    rw [ha c hc, mul_zero]

/-- the image `Δ W` -/
noncomputable def DW (hdvd : ∀ μ, n ∣ L μ + 1) : Submodule ℂ (TS L) := (Wc hdvd).map (lapC L)

theorem shiftS_Wc (hdvd : ∀ μ, n ∣ L μ + 1) (g : Site L) {φ : TS L} (hφ : φ ∈ Wc (n := n) hdvd) :
    shiftS n g φ ∈ Wc (n := n) hdvd := by
  intro c hc
  have h := hφ (c + n • g) ((coarse_add hdvd c g).mpr hc)
  simp only [shiftS_apply]
  rw [← h]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [add_right_comm]

theorem DW_map_shiftS (hdvd : ∀ μ, n ∣ L μ + 1) (g : Site L) :
    (DW (n := n) hdvd).map (shiftS n g).toLinearEquiv.toLinearMap = DW (n := n) hdvd := by
  have hinv : ∀ φ : TS L, shiftS n (-g) (shiftS n g φ) = φ := by
    intro φ; ext x; simp [shiftS_apply]
  have hinv' : ∀ φ : TS L, shiftS n g (shiftS n (-g) φ) = φ := by
    intro φ; ext x; simp [shiftS_apply]
  apply le_antisymm
  · rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨shiftS n g w, shiftS_Wc hdvd g hw, ?_⟩
    exact (lapC_equiv g w)
  · intro y hy
    obtain ⟨w, hw, rfl⟩ := hy
    refine ⟨lapC L (shiftS n (-g) w), ⟨shiftS n (-g) w, shiftS_Wc hdvd (-g) hw, rfl⟩, ?_⟩
    show shiftS n g (lapC L (shiftS n (-g) w)) = lapC L w
    rw [← lapC_equiv, hinv']

/-- the orthogonal projector onto `Δ W` -/
noncomputable def Pw (hdvd : ∀ μ, n ∣ L μ + 1) : TS L →L[ℂ] TS L := (DW (n := n) hdvd).starProjection

theorem shiftS_symm (g : Site L) (w : TS L) : (shiftS n g).symm w = shiftS n (-g) w := by
  apply (shiftS n g).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext x
  simp [shiftS_apply]

theorem shiftS_mem_DW (hdvd : ∀ μ, n ∣ L μ + 1) (g : Site L) {y : TS L} (hy : y ∈ DW (n := n) hdvd) :
    shiftS n g y ∈ DW (n := n) hdvd := by
  have h : shiftS n g y ∈ (DW (n := n) hdvd).map (shiftS n g).toLinearEquiv.toLinearMap :=
    Submodule.mem_map_of_mem hy
  rwa [DW_map_shiftS] at h

theorem Pw_equiv (hdvd : ∀ μ, n ∣ L μ + 1) (g : Site L) (f : TS L) :
    Pw hdvd (shiftS n g f) = shiftS n g (Pw hdvd f) := by
  unfold Pw
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact shiftS_mem_DW hdvd g (Submodule.starProjection_apply_mem _ _)
  · intro w hw
    have h1 : shiftS n g f - shiftS n g ((DW (n := n) hdvd).starProjection f) = shiftS n g (f - (DW (n := n) hdvd).starProjection f) := by
      rw [map_sub]
    have key : ⟪shiftS n g (f - (DW (n := n) hdvd).starProjection f), w⟫
        = ⟪f - (DW (n := n) hdvd).starProjection f, (shiftS n g).symm w⟫ := by
      rw [← LinearIsometryEquiv.inner_map_map (shiftS n g) (f - (DW (n := n) hdvd).starProjection f) ((shiftS n g).symm w),
        LinearIsometryEquiv.apply_symm_apply]
    rw [h1, key, shiftS_symm]
    exact Submodule.starProjection_inner_eq_zero f _ (shiftS_mem_DW hdvd (-g) hw)

/-- the projected divergence -/
noncomputable def L3 (hdvd : ∀ μ, n ∣ L μ + 1) : TB L →ₗ[ℂ] TS L :=
  (Pw hdvd).toLinearMap ∘ₗ Dst L

theorem L3_equiv (hdvd : ∀ μ, n ∣ L μ + 1) (g : Site L) (A : TB L) :
    L3 hdvd (shiftE n g (Fin 3) A) = shiftS n g (L3 hdvd A) := by
  unfold L3
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  rw [Dst_equiv, Pw_equiv]

#print axioms L3_equiv
#print axioms L2_equiv
#print axioms L1_equiv

end AdalyFormal.FlatCoercivity
