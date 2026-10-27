
namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## J. The flat localized carrier of the dilated tower is positive definite

At the trivial background `⟪x, B x⟫ = ‖χ curl x‖² + ‖T x‖² + Σ a ℓʲ ‖Q x‖²` (`B` the localized
carrier).  If it vanishes, `x` is curl-free on the plaquettes of `Ω₀`, vanishes on every bond not
touching `Ω₁` (level-0 rows of `Q`), and has vanishing level-1 rows.  Integrating `x` along the
longitudinal lines from the left boundary gives a site field `ξ` with `x = D ξ` on the bonds
before the right edge; the level-1 rows telescope along the longitudinal chain of blocks from the
left collar (where `ξ = 0`) to the right collar (where `ξ` is a transverse constant), so the
constant is `0`, `ξ ∈ N(Q')` and `x = D ξ` everywhere; then `T (D ξ) = 0` forces `D ξ = 0`
(the frozen `final_step` argument, copied). -/
section FlatKernel

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dil_fine_size)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_one curlValueCovariant
  gradValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf stepAverage)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open Fin.NatCast

/-! ### Frozen `NsPtD2.final_step` (outside the `DrEquiv` closure), copied verbatim. -/

theorem siteMask_eq_self_of_supp' {L : PeriodicLatticeExtent} (S : Set (PeriodicLatticeSite L))
    (ξ : SiteL2 L) (h : ∀ x, x ∉ S → ξ x = 0) : siteMask S ξ = ξ := by
  classical
  ext x
  rw [siteMask_apply]
  by_cases hx : x ∈ S
  · rw [if_pos hx]
  · rw [if_neg hx, h x hx]

theorem lapDir_eq_mask_lap' {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (ξ : SiteL2 L)
    (h : ∀ x, x ∉ G.Om0 → ξ x = 0) : lapDir G U ξ = siteMask G.Om0 (lapFull U ξ) := by
  unfold lapDir
  simp only [ContinuousLinearMap.comp_apply]
  rw [siteMask_eq_self_of_supp' _ _ h]

theorem final_step' {L : PeriodicLatticeExtent} (G : TowerGeom L) (ξ : SiteL2 L)
    (hξ : ξ ∈ NQp G (flatCfg : Cfg L))
    (hT : Tfull G (flatCfg : Cfg L) (gradL2 (flatCfg : Cfg L) ξ) = 0) :
    gradL2 (flatCfg : Cfg L) ξ = 0 := by
  have hsupp := hξ.1
  have hlap := lapDir_eq_mask_lap' G flatCfg ξ hsupp
  have hmem : lapDir G (flatCfg : Cfg L) ξ ∈ RImage G (flatCfg : Cfg L) :=
    Submodule.mem_map.mpr ⟨ξ, hξ, rfl⟩
  have hR : Rproj G (flatCfg : Cfg L) (lapFull (flatCfg : Cfg L) ξ) = 0 := by
    have : Tfull G (flatCfg : Cfg L) (gradL2 (flatCfg : Cfg L) ξ) =
        Rproj G (flatCfg : Cfg L) (lapFull (flatCfg : Cfg L) ξ) := rfl
    rw [← this]; exact hT
  have horth : lapFull (flatCfg : Cfg L) ξ ∈ (RImage G (flatCfg : Cfg L))ᗮ := by
    have := hR
    unfold Rproj at this
    exact (Submodule.starProjection_apply_eq_zero_iff _).mp this
  have h1 : ⟪lapDir G (flatCfg : Cfg L) ξ, lapFull (flatCfg : Cfg L) ξ⟫ = 0 :=
    (Submodule.mem_orthogonal _ _).mp horth _ hmem
  have h2 : ⟪lapDir G (flatCfg : Cfg L) ξ, lapFull (flatCfg : Cfg L) ξ⟫ =
      ‖lapDir G (flatCfg : Cfg L) ξ‖ ^ 2 := by
    have e : ⟪siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ), lapFull (flatCfg : Cfg L) ξ⟫
        = ⟪siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ),
            siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ)⟫ := by
      calc ⟪siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ), lapFull (flatCfg : Cfg L) ξ⟫
          = ⟪siteMask G.Om0 (siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ)),
              lapFull (flatCfg : Cfg L) ξ⟫ := by rw [siteMask_idem]
        _ = _ := siteMask_symm _ _ _
    rw [hlap, e, real_inner_self_eq_norm_sq]
  have h3 : lapDir G (flatCfg : Cfg L) ξ = 0 := by
    rw [h2] at h1
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)
  have h4 : ⟪ξ, lapFull (flatCfg : Cfg L) ξ⟫ = 0 := by
    have : ⟪ξ, lapFull (flatCfg : Cfg L) ξ⟫ = ⟪siteMask G.Om0 ξ, lapFull (flatCfg : Cfg L) ξ⟫ := by
      rw [siteMask_eq_self_of_supp' _ _ hsupp]
    rw [this, siteMask_symm, ← hlap, h3, inner_zero_right]
  have h5 : ⟪ξ, lapFull (flatCfg : Cfg L) ξ⟫ = ‖gradL2 (flatCfg : Cfg L) ξ‖ ^ 2 := by
    simp only [lapFull, ContinuousLinearMap.comp_apply, gradAdj, ContinuousLinearMap.adjoint_inner_right]
    rw [real_inner_self_eq_norm_sq]
  rw [h5] at h4
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h4)

/-! ### Coordinates of the dilated tower -/

variable {q R : ℕ}

theorem dsize0 (hq : 0 < q) : scaleUp 2 1 (dilLu q R) 0 + 1 = 12 * (R * q) + 16 * q := by
  have h := dil_fine_size hq R 0
  simpa using h

theorem dsizeT (hq : 0 < q) {μ : Fin 3} (hμ : μ ≠ 0) : scaleUp 2 1 (dilLu q R) μ + 1 = 8 * q := by
  rw [dil_fine_size hq R μ, if_neg hμ]

theorem x0_lt (hq : 0 < q) (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    (x 0).val < 12 * (R * q) + 16 * q := by
  have h1 := (x 0).isLt
  have h2 := dsize0 (R := R) hq
  omega

theorem xT_lt (hq : 0 < q) (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0) :
    (x μ).val < 8 * q := by
  have h1 := (x μ).isLt
  have h2 := dsizeT (R := R) hq hμ
  omega

theorem mem_Om0 (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    x ∈ (dilTower q R).Om 0 ↔ 4 * q ≤ (x 0).val ∧ (x 0).val < 12 * (R * q) + 12 * q := Iff.rfl

theorem mem_Om1 (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    x ∈ (dilTower q R).Om 1 ↔
      2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q := Iff.rfl

theorem not_mem_Om2 (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    x ∉ (dilTower q R).Om 2 := by
  simp [dilTower]

theorem shift_coord_ne {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) {μ ν : Fin 3}
    (h : ν ≠ μ) : (periodicLatticeShift x μ) ν = x ν := by
  unfold periodicLatticeShift
  rw [Function.update_of_ne h]

theorem shift_self_coord {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) (μ : Fin 3) :
    (periodicLatticeShift x μ) μ = x μ + 1 := by
  unfold periodicLatticeShift
  rw [Function.update_self]

theorem shift0_val_lt {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L)
    (h : (x 0).val + 1 < L 0 + 1) : ((periodicLatticeShift x 0) 0).val = (x 0).val + 1 := by
  rw [shift_self_coord, Fin.val_add_one, if_neg]
  intro hc
  rw [hc, Fin.val_last] at h
  omega

theorem shift0_val_last {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L)
    (h : (x 0).val + 1 = L 0 + 1) : ((periodicLatticeShift x 0) 0).val = 0 := by
  rw [shift_self_coord, Fin.val_add_one, if_pos]
  ext
  rw [Fin.val_last]
  omega

/-! ### The kernel argument -/

section Kernel
variable (hq : 0 < q) (hR : 1 ≤ R) (A : BondFnL2 (scaleUp 2 1 (dilLu q R)))
  (hsupp : ∀ b, b ∉ bondsOm0 (geomOf 2 1 (dilTower q R)) → A b = 0)
  (hQ : QfullOf (geomOf 2 1 (dilTower q R)) flatCfg A = 0)

theorem OmGe1_mem {x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))}
    (h : OmGe (geomOf 2 1 (dilTower q R)) 1 x) : x ∈ (dilTower q R).Om 1 := by
  obtain ⟨i, hi1, hik, y, hy, hxy⟩ := h
  have hi : i = 1 := by
    have : i ≤ 1 := hik
    omega
  subst hi
  obtain ⟨hdiv, hyOm, -⟩ := hy
  rw [mem_Om1] at hyOm ⊢
  have h0 := hxy 0
  have hd := hdiv 0
  have hell : (geomOf 2 1 (dilTower q R)).ell = 2 := rfl
  simp only [pow_one, hell] at hd h0
  have hb : 2 ∣ 10 * (R * q) + 12 * q := ⟨5 * (R * q) + 6 * q, by ring⟩
  omega

include hsupp hQ in
theorem A_zero_off {b : Bond (scaleUp 2 1 (dilLu q R))} (h1 : b.1 ∉ (dilTower q R).Om 1)
    (h2 : periodicLatticeShift b.1 b.2 ∉ (dilTower q R).Om 1) : A b = 0 := by
  by_cases hb : b ∈ bondsOm0 (geomOf 2 1 (dilTower q R))
  · have hL : b ∈ bondsLam (geomOf 2 1 (dilTower q R)) 0 := by
      refine ⟨?_, ?_⟩
      · rcases hb with hb | hb
        · exact Or.inl ⟨fun μ => by simp, hb, h1⟩
        · exact Or.inr ⟨fun μ => by simp, hb, h2⟩
      · rintro (h | h)
        · exact h1 (OmGe1_mem h)
        · exact h2 (OmGe1_mem h)
    have h := congrArg (fun v : FSp (geomOf 2 1 (dilTower q R)) => WithLp.ofLp v ⟨0, ⟨b, hL⟩⟩) hQ
    have h' : WithLp.ofLp (QfullOf (geomOf 2 1 (dilTower q R)) flatCfg A) ⟨0, ⟨b, hL⟩⟩ = A b := by
      rw [QfullOf_apply]
      show (((geomOf 2 1 (dilTower q R)).ell : ℝ) ^ 0)⁻¹ •
        (WithLp.ofLp (QlinB (geomOf 2 1 (dilTower q R)) flatCfg 0 A)) b = A b
      rw [QlinB_zero, pow_zero, inv_one, one_smul]
    simp only at h
    rw [h'] at h
    exact h
  · exact hsupp b hb

/-- the site with longitudinal coordinate replaced by `u`. -/
def sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) :
    PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) :=
  Function.update z 0 ((u : ℕ) : Fin (scaleUp 2 1 (dilLu q R) 0 + 1))

omit hq A in
theorem sitex_val (hq : 0 < q) (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {u : ℕ}
    (hu : u < 12 * (R * q) + 16 * q) : ((sitex z u) 0).val = u := by
  unfold sitex
  rw [Function.update_self, Fin.val_natCast, dsize0 hq]
  exact Nat.mod_eq_of_lt hu

omit A in
theorem sitex_coord (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) {ν : Fin 3}
    (hν : ν ≠ 0) : (sitex z u) ν = z ν := by
  unfold sitex
  rw [Function.update_of_ne hν]

omit A in
theorem sitex_self (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : sitex z (z 0).val = z := by
  unfold sitex
  rw [Fin.cast_val_eq_self, Function.update_eq_self]

omit A in
theorem sitex_sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u v : ℕ) :
    sitex (sitex z v) u = sitex z u := by
  unfold sitex
  rw [Function.update_idem]

omit A in
theorem shift_sitex0 (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) :
    periodicLatticeShift (sitex z u) 0 = sitex z (u + 1) := by
  unfold periodicLatticeShift sitex
  rw [Function.update_idem, Function.update_self, Nat.cast_succ]

omit A in
theorem shift_sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) {μ : Fin 3}
    (hμ : μ ≠ 0) : periodicLatticeShift (sitex z u) μ = sitex (periodicLatticeShift z μ) u := by
  unfold periodicLatticeShift sitex
  rw [Function.update_of_ne hμ, Function.update_comm (Ne.symm hμ)]

omit A in
theorem sitex_of_shift0 (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) :
    sitex (periodicLatticeShift z 0) u = sitex z u := by
  unfold periodicLatticeShift sitex
  rw [Function.update_idem]

/-- the longitudinal potential. -/
noncomputable def xi (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : SuTwo :=
  ∑ u ∈ Finset.range (z 0).val, A (sitex z u, 0)

include hq in
/-- longitudinal step. -/
theorem xi_shift0 (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (h : (z 0).val + 1 < 12 * (R * q) + 16 * q) :
    xi A (periodicLatticeShift z 0) = xi A z + A (z, 0) := by
  unfold xi
  have hz : ((periodicLatticeShift z 0) 0).val = (z 0).val + 1 :=
    shift0_val_lt z (by have h2 := dsize0 (R := R) hq; omega)
  rw [hz, Finset.sum_range_succ]
  simp only [sitex_of_shift0]
  rw [sitex_self]

include hq hR hsupp hQ in
/-- the plaquette identity in the `(0, μ)` plane, from curl-freeness or vanishing of all bonds. -/
theorem trans_step
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (w : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0)
    (hw : (w 0).val + 1 < 12 * (R * q) + 16 * q) :
    A (periodicLatticeShift w μ, 0) - A (w, 0) = A (periodicLatticeShift w 0, μ) - A (w, μ) := by
  classical
  have h0μ : (0 : Fin 3) < μ := by
    rcases Fin.pos_iff_ne_zero.mpr hμ with h
    exact h
  have hw0 : ((periodicLatticeShift w 0) 0).val = (w 0).val + 1 :=
    shift0_val_lt w (by have h2 := dsize0 (R := R) hq; omega)
  have hwμ : (periodicLatticeShift w μ) 0 = w 0 := shift_coord_ne w (Ne.symm hμ)
  have hw0μ : ((periodicLatticeShift (periodicLatticeShift w 0) μ) 0).val = (w 0).val + 1 := by
    rw [shift_coord_ne _ (Ne.symm hμ), hw0]
  have hwμ0 : ((periodicLatticeShift (periodicLatticeShift w μ) 0) 0).val = (w 0).val + 1 := by
    rw [shift0_val_lt _ (by have h2 := dsize0 (R := R) hq; rw [hwμ]; omega), hwμ]
  by_cases hin : 4 * q ≤ (w 0).val ∧ (w 0).val + 1 < 12 * (R * q) + 12 * q
  · let p : PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)) := (w, ⟨(0, μ), h0μ⟩)
    have hp : p ∈ plaqIn ((dilTower q R).Om 0) := by
      intro e he
      simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton, p] at he
      rcases he with rfl | rfl | rfl | rfl
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
    have hc := hcurl p hp
    simp only [curlValueCovariant, p, flatCfg, RMap_one, LinearMap.id_apply] at hc
    have e : A (periodicLatticeShift w μ, 0) - A (w, 0) - (A (periodicLatticeShift w 0, μ) - A (w, μ)) = 0 := by
      rw [← neg_eq_zero, ← hc]; abel
    exact sub_eq_zero.mp e
  · have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
    have hR1 : ∀ x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)),
        ((x 0).val = (w 0).val ∨ (x 0).val = (w 0).val + 1) → x ∉ (dilTower q R).Om 1 := by
      intro x hx hxm
      rw [mem_Om1] at hxm
      rcases hx with hx | hx <;> rw [hx] at hxm <;>
        (by_cases h4 : 4 * q ≤ (w 0).val
         · have h5 : ¬ ((w 0).val + 1 < 12 * (R * q) + 12 * q) := fun h => hin ⟨h4, h⟩
           omega
         · omega)
    have z1 := A_zero_off A hsupp hQ (b := (w, 0)) (hR1 w (Or.inl rfl)) (hR1 _ (Or.inr hw0))
    have z2 := A_zero_off A hsupp hQ (b := (periodicLatticeShift w 0, μ)) (hR1 _ (Or.inr hw0))
      (hR1 _ (Or.inr hw0μ))
    have z3 := A_zero_off A hsupp hQ (b := (periodicLatticeShift w μ, 0))
      (hR1 (periodicLatticeShift w μ) (Or.inl (by rw [hwμ]))) (hR1 _ (Or.inr hwμ0))
    have z4 := A_zero_off A hsupp hQ (b := (w, μ)) (hR1 w (Or.inl rfl))
      (hR1 (periodicLatticeShift w μ) (Or.inl (by rw [hwμ])))
    rw [z1, z2, z3, z4]

include hq hR hsupp hQ in
/-- transverse step. -/
theorem xi_shiftT
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0) :
    xi A (periodicLatticeShift z μ) = xi A z + (A (z, μ) - A (sitex z 0, μ)) := by
  unfold xi
  rw [shift_coord_ne z (Ne.symm hμ)]
  have hz := x0_lt hq z
  have e : ∀ u ∈ Finset.range (z 0).val, A (sitex (periodicLatticeShift z μ) u, 0)
      = A (sitex z u, 0) + (A (sitex z (u + 1), μ) - A (sitex z u, μ)) := by
    intro u hu
    rw [Finset.mem_range] at hu
    have hval : ((sitex z u) 0).val = u := sitex_val hq z (by omega)
    have ht := trans_step hq hR A hsupp hQ hcurl (sitex z u) hμ (by rw [hval]; omega)
    rw [shift_sitex z u hμ, shift_sitex0] at ht
    rw [← sub_eq_iff_eq_add', ht]
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_range_sub (fun u => A (sitex z u, μ)),
    sitex_self]

include hq hsupp hQ in
theorem xi_left (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (h : (z 0).val < 2 * (R * q) + 4 * q) : xi A z = 0 := by
  unfold xi
  refine Finset.sum_eq_zero (fun u hu => ?_)
  rw [Finset.mem_range] at hu
  have hz := x0_lt hq z
  have hv : ((sitex z u) 0).val = u := sitex_val hq z (by omega)
  refine A_zero_off A hsupp hQ ?_ ?_
  · rw [mem_Om1, hv]; omega
  · rw [mem_Om1, shift_sitex0, sitex_val hq z (by omega)]; omega

include hq hsupp hQ in
/-- beyond the right edge of `Ω₁` the potential equals its value at the right edge. -/
theorem xi_right (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (h : 10 * (R * q) + 12 * q ≤ (z 0).val) :
    xi A z = xi A (sitex z (10 * (R * q) + 12 * q)) := by
  have hz := x0_lt hq z
  have key : ∀ n, 10 * (R * q) + 12 * q + n < 12 * (R * q) + 16 * q →
      xi A (sitex z (10 * (R * q) + 12 * q + n)) = xi A (sitex z (10 * (R * q) + 12 * q)) := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      have hv : ((sitex z (10 * (R * q) + 12 * q + n)) 0).val = 10 * (R * q) + 12 * q + n :=
        sitex_val hq z (by omega)
      rw [← ih (by omega)]
      have e := xi_shift0 hq A (sitex z (10 * (R * q) + 12 * q + n)) (by rw [hv]; omega)
      rw [shift_sitex0] at e
      rw [show 10 * (R * q) + 12 * q + (n + 1) = 10 * (R * q) + 12 * q + n + 1 by ring, e]
      have h0 : A (sitex z (10 * (R * q) + 12 * q + n), 0) = 0 := by
        refine A_zero_off A hsupp hQ ?_ ?_
        · show sitex z _ ∉ _
          rw [mem_Om1, hv]; omega
        · show periodicLatticeShift (sitex z _) 0 ∉ _
          rw [mem_Om1, shift_sitex0, sitex_val hq z (by omega)]; omega
      rw [h0, add_zero]
  have hk := key ((z 0).val - (10 * (R * q) + 12 * q)) (by omega)
  rw [Nat.add_sub_cancel' h, sitex_self] at hk
  exact hk

/-- the right-edge value of the potential, a function of the transverse coordinates. -/
noncomputable def Iv (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : SuTwo :=
  xi A (sitex z (10 * (R * q) + 12 * q))

include hq hR hsupp hQ in
theorem Iv_shiftT
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0) :
    Iv A (periodicLatticeShift z μ) = Iv A z := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  unfold Iv
  rw [← shift_sitex z _ hμ, xi_shiftT hq hR A hsupp hQ hcurl _ hμ]
  have hv : ((sitex z (10 * (R * q) + 12 * q)) 0).val = 10 * (R * q) + 12 * q :=
    sitex_val hq z (by omega)
  have e1 : A (sitex z (10 * (R * q) + 12 * q), μ) = 0 := by
    refine A_zero_off A hsupp hQ ?_ ?_
    · show sitex z _ ∉ _
      rw [mem_Om1, hv]; omega
    · show periodicLatticeShift (sitex z _) μ ∉ _
      rw [mem_Om1, shift_coord_ne _ (Ne.symm hμ), hv]; omega
  have e2 : A (sitex (sitex z (10 * (R * q) + 12 * q)) 0, μ) = 0 := by
    rw [sitex_sitex]
    have hv0 : ((sitex z 0) 0).val = 0 := sitex_val hq z (by omega)
    refine A_zero_off A hsupp hQ ?_ ?_
    · show sitex z 0 ∉ _
      rw [mem_Om1, hv0]; omega
    · show periodicLatticeShift (sitex z 0) μ ∉ _
      rw [mem_Om1, shift_coord_ne _ (Ne.symm hμ), hv0]; omega
  rw [e1, e2, sub_zero, add_zero]

omit hq hR A in
theorem update_shift_succ {L : PeriodicLatticeExtent} (w : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) :
    Function.update w μ (w μ + ((n + 1 : ℕ) : Fin (L μ + 1))) =
      periodicLatticeShift (Function.update w μ (w μ + ((n : ℕ) : Fin (L μ + 1)))) μ := by
  unfold periodicLatticeShift
  rw [Function.update_idem, Function.update_self, Nat.cast_succ, add_assoc]

include hq hR hsupp hQ in
theorem Iv_update
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0)
    (v : Fin (scaleUp 2 1 (dilLu q R) μ + 1)) :
    Iv A (Function.update z μ v) = Iv A z := by
  have hn : ∀ n : ℕ, Iv A (Function.update z μ (z μ + ((n : ℕ) : Fin _))) = Iv A z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [update_shift_succ, Iv_shiftT hq hR A hsupp hQ hcurl _ hμ, ih]
  have h := hn (v - z μ).val
  rw [Fin.cast_val_eq_self, add_sub_cancel] at h
  exact h

omit hq hR A in
theorem Iv_update0 (A : BondFnL2 (scaleUp 2 1 (dilLu q R))) (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (v : Fin (scaleUp 2 1 (dilLu q R) 0 + 1)) : Iv A (Function.update z 0 v) = Iv A z := by
  unfold Iv sitex
  rw [Function.update_idem]

include hq hR hsupp hQ in
theorem Iv_const
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : Iv A z = Iv A (fun _ => 0) := by
  have e : (fun _ => (0 : Fin _) : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) =
      Function.update (Function.update (Function.update z 0 0) 1 0) 2 0 := by
    funext ν
    fin_cases ν <;> simp [Function.update] <;> rfl
  rw [e, Iv_update hq hR A hsupp hQ hcurl _ (by decide), Iv_update hq hR A hsupp hQ hcurl _ (by decide),
    Iv_update0]

omit hq hR A in
theorem coarseShift_sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (t : ℕ) :
    coarseShift (sitex z t) 2 0 = sitex z (t + 2) := by
  show periodicLatticeShift (periodicLatticeShift (sitex z t) 0) 0 = _
  rw [shift_sitex0, shift_sitex0]

include hq hR hQ in
/-- one level-1 row along direction `0`: the block sums of the potential agree. -/
theorem row_step (y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (hy1 : 2 ∣ (y 1).val) (hy2 : 2 ∣ (y 2).val) (hy0 : 2 ∣ (y 0).val)
    (hlo : 2 * (R * q) + 4 * q ≤ (y 0).val + 2) (hhi : (y 0).val + 2 ≤ 10 * (R * q) + 12 * q) :
    ∑ w ∈ stepBlockOf (coarseShift y 2 0) 1 2, xi A w = ∑ w ∈ stepBlockOf y 1 2, xi A w := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  have hy0' : ((periodicLatticeShift y 0) 0).val = (y 0).val + 1 := shift0_val_lt y (by omega)
  have hcs0 : ((coarseShift y 2 0) 0).val = (y 0).val + 2 := by
    show ((periodicLatticeShift (periodicLatticeShift y 0) 0) 0).val = _
    rw [shift0_val_lt _ (by rw [hy0']; omega), hy0']
  have hcsT : ∀ ν : Fin 3, ν ≠ 0 → (coarseShift y 2 0) ν = y ν := by
    intro ν hν
    show (periodicLatticeShift (periodicLatticeShift y 0) 0) ν = y ν
    rw [shift_coord_ne _ hν, shift_coord_ne _ hν]
  have hc : (y, (0 : Fin 3)) ∈ bondsLam (geomOf 2 1 (dilTower q R)) 1 := by
    refine ⟨?_, ?_⟩
    · by_cases hya : 2 * (R * q) + 4 * q ≤ (y 0).val
      · left
        show y ∈ (geomOf 2 1 (dilTower q R)).Lam 1
        refine ⟨fun μ => ?_, (mem_Om1 _).mpr ⟨hya, by omega⟩, not_mem_Om2 _⟩
        show 2 ^ 1 ∣ (y μ).val
        fin_cases μ
        · simpa using hy0
        · simpa using hy1
        · simpa using hy2
      · right
        have e1 : coarseShift (y, (0 : Fin 3)).1 ((geomOf 2 1 (dilTower q R)).ell ^ 1) (y, (0 : Fin 3)).2 =
            coarseShift y 2 0 := rfl
        rw [e1]
        show coarseShift y 2 0 ∈ (geomOf 2 1 (dilTower q R)).Lam 1
        refine ⟨fun μ => ?_, (mem_Om1 _).mpr ⟨by rw [hcs0]; omega, by rw [hcs0]; omega⟩, not_mem_Om2 _⟩
        show 2 ^ 1 ∣ ((coarseShift y 2 0) μ).val
        fin_cases μ
        · show 2 ^ 1 ∣ ((coarseShift y 2 0) 0).val
          rw [hcs0]; simpa using (Nat.dvd_add hy0 (dvd_refl 2))
        · show 2 ^ 1 ∣ ((coarseShift y 2 0) 1).val
          rw [hcsT 1 (by decide)]; simpa using hy1
        · show 2 ^ 1 ∣ ((coarseShift y 2 0) 2).val
          rw [hcsT 2 (by decide)]; simpa using hy2
    · rintro (h | h) <;>
        exact not_OmGe_of_lt (G := geomOf 2 1 (dilTower q R)) (lt_of_eq_of_lt (dil_G_k q R) (by norm_num)) _ h
  let p : BIdx (geomOf 2 1 (dilTower q R)) := ⟨1, ⟨(y, 0), hc⟩⟩
  have hrow : WithLp.ofLp (QfullOf (geomOf 2 1 (dilTower q R)) flatCfg A) p = 0 := by
    rw [hQ]; rfl
  have hQrow := AdalyFormal.W6.Qflat_row (ell := 2) (k := 1) (Lu := dilLu q R) (S := dilTower q R)
    (by norm_num) A p
  have hline : AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictSuTwo (2 ^ (p.1 : ℕ))
      (WithLp.ofLp A) (AdalyFormal.W6.rowCB (by norm_num) p) = 0 := by
    rw [← hQrow]; exact hrow
  have hline' : (1 / ((2 : ℕ) : ℝ) ^ 4) • ∑ x ∈ blockOf y 2, ∑ i ∈ Finset.range 2,
      A (pathSite x 0 i, 0) = 0 := hline
  have hsum : ∑ x ∈ blockOf y 2, ∑ i ∈ Finset.range 2, A (pathSite x 0 i, 0) = 0 := by
    rcases smul_eq_zero.mp hline' with h | h
    · norm_num at h
    · exact h
  have hpt : ∀ x ∈ blockOf y 2, ∑ i ∈ Finset.range 2, A (pathSite x 0 i, 0) =
      xi A (coarseShift x 2 0) - xi A x := by
    intro x hx
    have hxb := (mem_blockOf.mp hx) 0
    have hx0 : (x 0).val + 1 < 12 * (R * q) + 16 * q := by omega
    have hsx : ((periodicLatticeShift x 0) 0).val = (x 0).val + 1 := shift0_val_lt x (by omega)
    have e1 := xi_shift0 hq A x hx0
    have e2 := xi_shift0 hq A (periodicLatticeShift x 0) (by rw [hsx]; omega)
    show _ = xi A (periodicLatticeShift (periodicLatticeShift x 0) 0) - xi A x
    rw [e2, e1, Finset.sum_range_succ, Finset.sum_range_one]
    show A (x, 0) + A (periodicLatticeShift x 0, 0) = _
    abel
  have hfit : ∀ ν : Fin 3, (y ν).val + 1 * 2 ≤ scaleUp 2 1 (dilLu q R) ν + 1 := by
    intro ν
    by_cases hν : ν = 0
    · subst hν; omega
    · have := xT_lt hq y hν
      have h8 := dsizeT (R := R) hq hν
      have hev : 2 ∣ (y ν).val := by
        fin_cases ν
        · exact absurd rfl hν
        · exact hy1
        · exact hy2
      omega
  have hfit' : ∀ ν : Fin 3, ((coarseShift y 2 0) ν).val + 1 * 2 ≤ scaleUp 2 1 (dilLu q R) ν + 1 := by
    intro ν
    by_cases hν : ν = 0
    · subst hν; rw [hcs0]; omega
    · rw [hcsT ν hν]; exact hfit ν
  have hshift := AdalyFormal.CurvBlock.block_sum_shift 1 2 2 0 hfit hfit' (xi A)
  rw [← hshift]
  rw [AdalyFormal.Balaban.QjComposite.stepBlockOf_one] at *
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib] at hsum
  exact sub_eq_zero.mp hsum

include hq hR hsupp hQ in
/-- the block sums vanish along the whole longitudinal chain of blocks. -/
theorem chain_zero (y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (hy1 : 2 ∣ (y 1).val) (hy2 : 2 ∣ (y 2).val) :
    ∀ m : ℕ, 2 * m ≤ 8 * (R * q) + 8 * q + 2 →
      ∑ w ∈ stepBlockOf (sitex y (2 * (R * q) + 4 * q - 2 + 2 * m)) 1 2, xi A w = 0 := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  intro m
  induction m with
  | zero =>
    intro _
    refine Finset.sum_eq_zero (fun w hw => ?_)
    have hb := ((AdalyFormal.Balaban.QjComposite.mem_stepBlockOf).mp hw) 0
    have hv : ((sitex y (2 * (R * q) + 4 * q - 2 + 2 * 0)) 0).val = 2 * (R * q) + 4 * q - 2 + 2 * 0 :=
      sitex_val hq y (by omega)
    rw [hv] at hb
    exact xi_left hq A hsupp hQ w (by omega)
  | succ m ih =>
    intro hm
    have hv : ((sitex y (2 * (R * q) + 4 * q - 2 + 2 * m)) 0).val = 2 * (R * q) + 4 * q - 2 + 2 * m :=
      sitex_val hq y (by omega)
    have e : sitex y (2 * (R * q) + 4 * q - 2 + 2 * (m + 1)) =
        coarseShift (sitex y (2 * (R * q) + 4 * q - 2 + 2 * m)) 2 0 := by
      rw [coarseShift_sitex]
      congr 1
    rw [e, row_step hq hR A hQ _ (by rw [sitex_coord _ _ (by decide)]; exact hy1)
      (by rw [sitex_coord _ _ (by decide)]; exact hy2) (by rw [hv]; omega) (by rw [hv]; omega)
      (by rw [hv]; omega)]
    exact ih (by omega)

include hq hR hsupp hQ in
theorem Iv_zero
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0) :
    Iv A (fun _ => 0) = 0 := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  let y0 : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) := fun _ => 0
  have hb := chain_zero hq hR A hsupp hQ y0 (by simp [y0]) (by simp [y0])
    (4 * (R * q) + 4 * q + 1) (by omega)
  have hv : ((sitex y0 (2 * (R * q) + 4 * q - 2 + 2 * (4 * (R * q) + 4 * q + 1))) 0).val =
      10 * (R * q) + 12 * q := by
    rw [sitex_val hq y0 (by omega)]; omega
  have e : ∀ w ∈ stepBlockOf (sitex y0 (2 * (R * q) + 4 * q - 2 + 2 * (4 * (R * q) + 4 * q + 1))) 1 2,
      xi A w = Iv A (fun _ => 0) := by
    intro w hw
    have hwb := ((AdalyFormal.Balaban.QjComposite.mem_stepBlockOf).mp hw) 0
    rw [hv] at hwb
    rw [xi_right hq A hsupp hQ w (by omega)]
    exact Iv_const hq hR A hsupp hQ hcurl w
  have hfit : ∀ ν : Fin 3, ((sitex y0 (2 * (R * q) + 4 * q - 2 + 2 * (4 * (R * q) + 4 * q + 1))) ν).val
      + 1 * 2 ≤ scaleUp 2 1 (dilLu q R) ν + 1 := by
    intro ν
    by_cases hν : ν = 0
    · subst hν; rw [hv]; omega
    · rw [sitex_coord _ _ hν]
      have h8 := dsizeT (R := R) hq hν
      show ((0 : Fin _) : ℕ) + 1 * 2 ≤ _
      simp only [Fin.val_zero]
      omega
  rw [Finset.sum_congr rfl e, Finset.sum_const,
    AdalyFormal.Balaban.QjComposite.card_stepBlockOf _ 1 2 one_pos hfit] at hb
  have h8 : (8 : ℝ) • Iv A (fun _ => 0) = 0 := by
    rw [show (8 : ℝ) = ((2 ^ 3 : ℕ) : ℝ) by norm_num, Nat.cast_smul_eq_nsmul]
    exact hb
  rcases smul_eq_zero.mp h8 with h | h
  · norm_num at h
  · exact h

include hq hR hsupp hQ in
theorem xi_mem_NQp
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0) :
    (WithLp.toLp 2 (xi A) : SiteL2 (scaleUp 2 1 (dilLu q R))) ∈
      NQp (geomOf 2 1 (dilTower q R)) flatCfg := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  have hzero : ∀ x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)),
      ¬ ((dilTower q R).Om 1 x) → xi A x = 0 := by
    intro x hx
    have hx' : ¬ (2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q) := hx
    by_cases h : (x 0).val < 2 * (R * q) + 4 * q
    · exact xi_left hq A hsupp hQ x h
    · rw [xi_right hq A hsupp hQ x (by omega)]
      show Iv A x = 0
      rw [Iv_const hq hR A hsupp hQ hcurl x, Iv_zero hq hR A hsupp hQ hcurl]
  refine ⟨fun x hx => ?_, fun j hj y hy => ?_⟩
  · show xi A x = 0
    refine hzero x (fun h1 => hx ?_)
    have h1' : 2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q := h1
    show 4 * q ≤ (x 0).val ∧ (x 0).val < 12 * (R * q) + 12 * q
    omega
  · have hj1 : j = 0 ∨ j = 1 := by
      have : j ≤ 1 := hj
      omega
    rcases hj1 with rfl | rfl
    · rw [Qlev_apply, AdalyFormal.Balaban.QjComposite.Qcomposite_zero]
      show xi A y = 0
      exact hzero y hy.2.2
    · rw [Qlev_apply, Qcomposite_one', bgTower_zero']
      show stepAverage (2 ^ 0) (trivialU _) 2 (xi A) y = 0
      rw [AdalyFormal.Balaban.QjComposite.stepAverage_trivialU, pow_zero]
      obtain ⟨hdiv, hy1, -⟩ := hy
      have hy1' : 2 * (R * q) + 4 * q ≤ (y 0).val ∧ (y 0).val < 10 * (R * q) + 12 * q := hy1
      have hd0 : 2 ∣ (y 0).val := by simpa using hdiv 0
      have hd1 : 2 ∣ (y 1).val := by simpa using hdiv 1
      have hd2 : 2 ∣ (y 2).val := by simpa using hdiv 2
      obtain ⟨m, hm⟩ : ∃ m, (y 0).val = 2 * (R * q) + 4 * q - 2 + 2 * m := by
        obtain ⟨t, ht⟩ := hd0
        refine ⟨t - (R * q) - 2 * q + 1, ?_⟩
        omega
      have hc := chain_zero hq hR A hsupp hQ y hd1 hd2 m (by omega)
      rw [← hm, sitex_self] at hc
      rw [hc, smul_zero]

include hq hR hsupp hQ in
theorem A_eq_grad
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0) :
    A = gradL2 flatCfg (WithLp.toLp 2 (xi A)) := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  refine PiLp.ext (fun e => ?_)
  obtain ⟨z, μ⟩ := e
  show A (z, μ) = gradValueCovariant flatCfg (xi A) (z, μ)
  simp only [gradValueCovariant, flatCfg, RMap_one, LinearMap.id_apply]
  have hz := x0_lt hq z
  by_cases hμ : μ = 0
  · subst hμ
    by_cases hz1 : (z 0).val + 1 < 12 * (R * q) + 16 * q
    · rw [xi_shift0 hq A z hz1]; abel
    · have hzl : (z 0).val + 1 = scaleUp 2 1 (dilLu q R) 0 + 1 := by omega
      have h0 : ((periodicLatticeShift z 0) 0).val = 0 := shift0_val_last z hzl
      have e1 : xi A (periodicLatticeShift z 0) = 0 := xi_left hq A hsupp hQ _ (by rw [h0]; omega)
      have e2 : xi A z = 0 := by
        rw [xi_right hq A hsupp hQ z (by omega)]
        show Iv A z = 0
        rw [Iv_const hq hR A hsupp hQ hcurl z, Iv_zero hq hR A hsupp hQ hcurl]
      have e3 : A (z, 0) = 0 := by
        refine A_zero_off A hsupp hQ ?_ ?_
        · show z ∉ _
          rw [mem_Om1]; omega
        · show periodicLatticeShift z 0 ∉ _
          rw [mem_Om1, h0]; omega
      rw [e1, e2, e3, sub_zero]
  · rw [xi_shiftT hq hR A hsupp hQ hcurl z hμ]
    have hv0 : ((sitex z 0) 0).val = 0 := sitex_val hq z (by omega)
    have e3 : A (sitex z 0, μ) = 0 := by
      refine A_zero_off A hsupp hQ ?_ ?_
      · show sitex z 0 ∉ _
        rw [mem_Om1, hv0]; omega
      · show periodicLatticeShift (sitex z 0) μ ∉ _
        rw [mem_Om1, shift_coord_ne _ (Ne.symm hμ), hv0]; omega
    rw [e3]; abel

include hq hR hsupp hQ in
/-- **The flat kernel of the dilated tower is trivial.** -/
theorem dil_flat_kernel
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (hT : Tfull (geomOf 2 1 (dilTower q R)) flatCfg A = 0) : A = 0 := by
  have hg := A_eq_grad hq hR A hsupp hQ hcurl
  have hmem := xi_mem_NQp hq hR A hsupp hQ hcurl
  rw [hg] at hT ⊢
  exact final_step' _ _ hmem hT

end Kernel

end FlatKernel

end AdalyFormal.Round9.Guarded.AnalyticR2
