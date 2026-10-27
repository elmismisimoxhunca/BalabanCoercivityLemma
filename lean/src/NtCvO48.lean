import NtCvO47

/-!
# CvO48 -- `Ginv` on Z-fields of `E_0` (lane omega)

`Ginv = Dpi + Ts T + Mass` (BaseDataS.Ginv).  On `x = zfield f ∈ E_0`: `Dpi x = zfield (zprof ω f)`, `T x = 0`, `Mass x = zfield (Wt (a·fSum f))`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverNested (cartan cartan_coe)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.IngredientFamilyR2

variable {L : PeriodicLatticeExtent}

/-- `zfield g ∈ E_0` as soon as `g` vanishes on slices `v ≤ L 0` outside the support interval. -/
theorem zfield_mem_bondSupp (G : TowerGeom L) (J : ℕ → Prop) (hOm : G.Om0 = {z : PeriodicLatticeSite L | J (z 0).val})
    (g : ℕ → ℝ) (hg : ∀ v, v ≤ L 0 → ¬ J v → g v = 0) : (zfield g : BondFnL2 L) ∈ bondSupp G := by
  intro b hb
  show zfun g b = 0
  unfold zfun
  by_cases h1 : b.2 = 1
  · rw [if_pos h1]
    have hnot : ¬ J (b.1 0).val := by
      intro hJ
      apply hb
      left
      rw [hOm]; exact hJ
    rw [hg _ (by have := (b.1 0).isLt; omega) hnot, dgS_zero]
  · rw [if_neg h1]

theorem nxt_prv (N v : ℕ) (hv : v ≤ N) : nxt N (prv N v) = v := by
  unfold nxt prv
  by_cases h : v = 0
  · subst h; simp
  · rw [if_neg h]
    have : v - 1 ≠ N := by omega
    rw [if_neg this]; omega

/-- support of the `Delta` profile. -/
theorem zprof_supp (J : ℕ → Prop) (N c : ℕ) (t : ℝ) (f : ℕ → ℝ) (v : ℕ) (hv : v ≤ N) (hJ : ¬ J v) :
    zprof N (omegaW J N c t) f v = 0 := by
  classical
  unfold zprof Wa
  have h1 : omegaW J N c t v = 0 := by unfold omegaW; rw [if_neg (fun h => hJ h.1)]
  have h2 : omegaW J N c t (prv N v) = 0 := by
    unfold omegaW
    rw [if_neg]
    intro h
    exact hJ (by rw [nxt_prv N v hv] at h; exact h.2)
  rw [h1, h2]; ring

theorem zfield_add (f g : ℕ → ℝ) : (zfield (f + g) : BondFnL2 L) = zfield f + zfield g := by
  refine PiLp.ext (fun b => ?_)
  show zfun (f + g) b = zfun f b + zfun g b
  unfold zfun
  split_ifs
  · exact dgS_add _ _
  · simp

theorem zfield_add' (f g : ℕ → ℝ) : (zfield (fun v => f v + g v) : BondFnL2 L) = zfield f + zfield g := zfield_add f g

/-- the `Ginv` profile on Z-fields. -/
noncomputable def ginvProf (ell : ℕ) (isRow : ℕ → ℕ → Prop) (J : ℕ → Prop) (N0 c : ℕ) (t a : ℝ) (f : ℕ → ℝ) (v : ℕ) : ℝ :=
  zprof N0 (omegaW J N0 c t) f v + Wt ell isRow (fun j u => a * fSum ell j f u) v

open Classical in
/-- **`Ginv` on a Z-field of `E_0`**. -/
theorem Ginv_zfield {ell c : ℕ} (t : ℝ) (U : Cfg L) (hUc : U = stagCfg c t) {G : TowerGeom L} {isRow : ℕ → ℕ → Prop} (S : StagSetup L ell c G isRow) (J : ℕ → Prop)
    (hOm : G.Om0 = {z : PeriodicLatticeSite L | J (z 0).val})
    (hrowJ : ∀ j, j ≤ 2 → ∀ v, isRow j (ell ^ j * (v / ell ^ j)) → J v)
    (htπ : |t| < tcap ell) (a : ℝ) (Jf : BondFnL2 L) (f : ℕ → ℝ)
    (hf : (zfield f : BondFnL2 L) ∈ bondSupp G) :
    (((baseData G U a (bondSectorOf G U) Jf).Ginv ⟨zfield f, hf⟩ : ↥(bondSupp G)) : BondFnL2 L) =
      zfield (ginvProf ell isRow J (L 0) c t a f) := by
  subst hUc
  have hU := stagCfg_cartan (L := L) c t
  have hωe : ∀ x : PeriodicLatticeSite L, (if (x, q01) ∈ plaqIn G.Om0 then holCos (stagCfg c t) (x, q01) else 0) = omegaW J (L 0) c t (x 0).val := by
    intro x; rw [hOm]; exact hω_stag J c t x
  have hD := DpiFull_zfield G (stagCfg c t) hU a f (omegaW J (L 0) c t) hωe
  have hM := MassFull_zfield S t htπ a f
  have hDm : zfield (zprof (L 0) (omegaW J (L 0) c t) f) ∈ bondSupp G :=
    zfield_mem_bondSupp G J hOm _ (fun v hv hJ => zprof_supp J (L 0) c t f v hv hJ)
  have hMm : zfield (Wt ell isRow (fun j u => a * fSum ell j f u)) ∈ bondSupp G := by
    refine zfield_mem_bondSupp G J hOm _ (fun v _ hJ => ?_)
    unfold Wt
    refine Finset.sum_eq_zero (fun j hj => ?_)
    have hj2 : j ≤ 2 := by have := Finset.mem_range.mp hj; omega
    rw [if_neg (fun h => hJ (hrowJ j hj2 v h))]; ring
  have hDx : ((((baseData G (stagCfg c t) a (bondSectorOf G (stagCfg c t)) Jf).Dpi ⟨zfield f, hf⟩ : ↥(bondSupp G)) : BondFnL2 L)) =
      zfield (zprof (L 0) (omegaW J (L 0) c t) f) := by
    show ((pE G (DpiFull G (stagCfg c t) a (iE G ⟨zfield f, hf⟩)) : ↥(bondSupp G)) : BondFnL2 L) = _
    show ((pE G (DpiFull G (stagCfg c t) a (zfield f)) : ↥(bondSupp G)) : BondFnL2 L) = _
    rw [hD]; exact pE_of_mem G _ hDm
  have hTx : (baseData G (stagCfg c t) a (bondSectorOf G (stagCfg c t)) Jf).T ⟨zfield f, hf⟩ = 0 := by
    show Tfull G (stagCfg c t) (iE G ⟨zfield f, hf⟩) = 0
    exact Tfull_zfield G (stagCfg c t) hU f
  have hMx : ((((baseData G (stagCfg c t) a (bondSectorOf G (stagCfg c t)) Jf).Mass ⟨zfield f, hf⟩ : ↥(bondSupp G)) : BondFnL2 L)) =
      zfield (Wt ell isRow (fun j u => a * fSum ell j f u)) := by
    show ((pE G (MassFull G a (bondSectorOf G (stagCfg c t)) (iE G ⟨zfield f, hf⟩)) : ↥(bondSupp G)) : BondFnL2 L) = _
    show ((pE G (MassFull G a (bondSectorOf G (stagCfg c t)) (zfield f)) : ↥(bondSupp G)) : BondFnL2 L) = _
    rw [hM]; exact pE_of_mem G _ hMm
  have hGx : (baseData G (stagCfg c t) a (bondSectorOf G (stagCfg c t)) Jf).Ginv ⟨zfield f, hf⟩ =
      (baseData G (stagCfg c t) a (bondSectorOf G (stagCfg c t)) Jf).Dpi ⟨zfield f, hf⟩ +
      (baseData G (stagCfg c t) a (bondSectorOf G (stagCfg c t)) Jf).Ts ((baseData G (stagCfg c t) a (bondSectorOf G (stagCfg c t)) Jf).T ⟨zfield f, hf⟩) +
      (baseData G (stagCfg c t) a (bondSectorOf G (stagCfg c t)) Jf).Mass ⟨zfield f, hf⟩ := by
    simp [BaseDataS.Ginv]
  rw [hGx, hTx, map_zero]
  simp only [Submodule.coe_add, ZeroMemClass.coe_zero, add_zero]
  rw [hDx, hMx]
  have hP : ginvProf ell isRow J (L 0) c t a f = fun v => zprof (L 0) (omegaW J (L 0) c t) f v + Wt ell isRow (fun j u => a * fSum ell j f u) v := rfl
  rw [hP]
  exact (zfield_add' _ _).symm

#print axioms Ginv_zfield

end AdalyFormal.CoverOmega
