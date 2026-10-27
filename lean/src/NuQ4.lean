import NuQ3

/-!
# NuQ4 -- `Ginv` on Z-fields along the direction-0 staggered family: the single negative edge (lane ncwdh_ell2_20261018)

`omega1 J N0 xs t v`: the `(0,1)`-plaquette weight on the slice `v` (restricted to `Ω₀`): `cos 2t` on the single slice `v = xs`, `1` on the other slices of `Ω₀`, `0` outside.
`Ginv_zfield0`: `Ginv (zfield f) = zfield (zprof N0 (omega1 ..) f + Wt (a · fSum f))`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.CoverNested (cartan cartan_coe)
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.IngredientFamilyR2

section
variable [CfData]
variable {L : PeriodicLatticeExtent} {ell xs : ℕ} {t : ℝ}

open Classical in
/-- the `(0,1)`-plaquette weight along the direction-0 staggered family as a function of `x₀`. -/
noncomputable def omega1 (J : ℕ → Prop) (N0 xs : ℕ) (t : ℝ) (v : ℕ) : ℝ :=
  if J v ∧ J (nxt N0 v) then (if v = xs then Real.cos (2 * t) else 1) else 0

open Classical in
theorem hω_stag0 (hN : 2 ∣ L 1 + 1) (J : ℕ → Prop) (xs : ℕ) (t : ℝ) (x : PeriodicLatticeSite L) :
    (if (x, q01) ∈ plaqIn {z : PeriodicLatticeSite L | J (z 0).val} then
        holCos (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (x, q01) else 0) =
      omega1 J (L 0) xs t (x 0).val := by
  unfold omega1
  by_cases h : J (x 0).val ∧ J (nxt (L 0) (x 0).val)
  · rw [if_pos ((plaqIn_01_iff J x).mpr h), if_pos h, holCos_stag0 hN]
    by_cases hx : (x 0).val = xs
    · rw [if_pos hx, if_pos]
      exact ⟨rfl, hx⟩
    · rw [if_neg hx, if_neg]
      intro hh; exact hx hh.2
  · rw [if_neg (fun h' => h ((plaqIn_01_iff J x).mp h')), if_neg h]

theorem zprof_supp0 (J : ℕ → Prop) (N xs : ℕ) (t : ℝ) (f : ℕ → ℝ) (v : ℕ) (hv : v ≤ N) (hJ : ¬ J v) :
    zprof N (omega1 J N xs t) f v = 0 := by
  classical
  unfold zprof Wa
  have h1 : omega1 J N xs t v = 0 := by unfold omega1; rw [if_neg (fun h => hJ h.1)]
  have h2 : omega1 J N xs t (prv N v) = 0 := by
    unfold omega1
    rw [if_neg]
    intro h
    exact hJ (by rw [nxt_prv N v hv] at h; exact h.2)
  rw [h1, h2]; ring

/-- the `Ginv` profile on Z-fields. -/
noncomputable def ginvProf0 (ell : ℕ) (isRow : ℕ → ℕ → Prop) (J : ℕ → Prop) (N0 xs : ℕ) (t a : ℝ) (f : ℕ → ℝ) (v : ℕ) : ℝ :=
  zprof N0 (omega1 J N0 xs t) f v + CoverOmega.Wt ell isRow (fun j u => a * fSum ell j f u) v

open Classical in
/-- **`Ginv` on a Z-field of `E_0`** along the direction-0 staggered family. -/
theorem Ginv_zfield0 {G : TowerGeom L} {isRow : ℕ → ℕ → Prop} (S : Z0Setup L ell xs t G isRow) (J : ℕ → Prop)
    (hOm : G.Om0 = {z : PeriodicLatticeSite L | J (z 0).val})
    (hrowJ : ∀ j, j ≤ 2 → ∀ v, isRow j (ell ^ j * (v / ell ^ j)) → J v)
    (a : ℝ) (Jf : BondFnL2 L) (f : ℕ → ℝ)
    (hf : (zfield f : BondFnL2 L) ∈ bondSupp G) :
    (((baseData G (stag0Cfg (L := L) xs t) a (bondSectorOf G (stag0Cfg (L := L) xs t)) Jf).Ginv ⟨zfield f, hf⟩ : ↥(bondSupp G)) : BondFnL2 L) =
      zfield (ginvProf0 ell isRow J (L 0) xs t a f) := by
  have hU := stag0Cfg_cartan (L := L) xs t
  have hωe : ∀ x : PeriodicLatticeSite L, (if (x, q01) ∈ plaqIn G.Om0 then holCos (stag0Cfg (L := L) xs t) (x, q01) else 0) = omega1 J (L 0) xs t (x 0).val := by
    intro x; rw [hOm]; exact hω_stag0 S.z.hN J xs t x
  have hD := DpiFull_zfield G (stag0Cfg (L := L) xs t) hU a f (omega1 J (L 0) xs t) hωe
  have hM := MassFull_zfield0 S a f
  have hDm : zfield (zprof (L 0) (omega1 J (L 0) xs t) f) ∈ bondSupp G :=
    zfield_mem_bondSupp G J hOm _ (fun v hv hJ => zprof_supp0 J (L 0) xs t f v hv hJ)
  have hMm : zfield (CoverOmega.Wt ell isRow (fun j u => a * fSum ell j f u)) ∈ bondSupp G := by
    refine zfield_mem_bondSupp G J hOm _ (fun v _ hJ => ?_)
    unfold CoverOmega.Wt
    refine Finset.sum_eq_zero (fun j hj => ?_)
    have hj2 : j ≤ 2 := by have := Finset.mem_range.mp hj; omega
    rw [if_neg (fun h => hJ (hrowJ j hj2 v h))]; ring
  have hDx : ((((baseData G (stag0Cfg (L := L) xs t) a (bondSectorOf G (stag0Cfg (L := L) xs t)) Jf).Dpi ⟨zfield f, hf⟩ : ↥(bondSupp G)) : BondFnL2 L)) =
      zfield (zprof (L 0) (omega1 J (L 0) xs t) f) := by
    show ((pE G (DpiFull G (stag0Cfg (L := L) xs t) a (iE G ⟨zfield f, hf⟩)) : ↥(bondSupp G)) : BondFnL2 L) = _
    show ((pE G (DpiFull G (stag0Cfg (L := L) xs t) a (zfield f)) : ↥(bondSupp G)) : BondFnL2 L) = _
    rw [hD]; exact pE_of_mem G _ hDm
  have hTx : (baseData G (stag0Cfg (L := L) xs t) a (bondSectorOf G (stag0Cfg (L := L) xs t)) Jf).T ⟨zfield f, hf⟩ = 0 := by
    show Tfull G (stag0Cfg (L := L) xs t) (iE G ⟨zfield f, hf⟩) = 0
    exact Tfull_zfield G (stag0Cfg (L := L) xs t) hU f
  have hMx : ((((baseData G (stag0Cfg (L := L) xs t) a (bondSectorOf G (stag0Cfg (L := L) xs t)) Jf).Mass ⟨zfield f, hf⟩ : ↥(bondSupp G)) : BondFnL2 L)) =
      zfield (CoverOmega.Wt ell isRow (fun j u => a * fSum ell j f u)) := by
    show ((pE G (MassFull G a (bondSectorOf G (stag0Cfg (L := L) xs t)) (iE G ⟨zfield f, hf⟩)) : ↥(bondSupp G)) : BondFnL2 L) = _
    show ((pE G (MassFull G a (bondSectorOf G (stag0Cfg (L := L) xs t)) (zfield f)) : ↥(bondSupp G)) : BondFnL2 L) = _
    rw [hM]; exact pE_of_mem G _ hMm
  have hGx : (baseData G (stag0Cfg (L := L) xs t) a (bondSectorOf G (stag0Cfg (L := L) xs t)) Jf).Ginv ⟨zfield f, hf⟩ =
      (baseData G (stag0Cfg (L := L) xs t) a (bondSectorOf G (stag0Cfg (L := L) xs t)) Jf).Dpi ⟨zfield f, hf⟩ +
      (baseData G (stag0Cfg (L := L) xs t) a (bondSectorOf G (stag0Cfg (L := L) xs t)) Jf).Ts ((baseData G (stag0Cfg (L := L) xs t) a (bondSectorOf G (stag0Cfg (L := L) xs t)) Jf).T ⟨zfield f, hf⟩) +
      (baseData G (stag0Cfg (L := L) xs t) a (bondSectorOf G (stag0Cfg (L := L) xs t)) Jf).Mass ⟨zfield f, hf⟩ := by
    simp [BaseDataS.Ginv]
  rw [hGx, hTx, map_zero]
  simp only [Submodule.coe_add, ZeroMemClass.coe_zero, add_zero]
  rw [hDx, hMx]
  have hP : ginvProf0 ell isRow J (L 0) xs t a f = fun v => zprof (L 0) (omega1 J (L 0) xs t) f v + CoverOmega.Wt ell isRow (fun j u => a * fSum ell j f u) v := rfl
  rw [hP]
  exact (zfield_add' _ _).symm

end

end AdalyFormal.NcwdhTwo
