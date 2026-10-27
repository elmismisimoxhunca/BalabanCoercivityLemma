import NuG3

/-!
# NuG4 -- invariance of the Z-block under `G1inv`, `Qs`, `Q`; the Z-block bound (lane ncwdh_ell2_20261018)

`zblock_ineq`: for a chain vector `e` with `Q x_e = y0`,
`<y0, N⁻¹ y0> ≤ c0 T1 qF1_c(e) + <y0, D y0>`, given the units `G1inv`, `N` and `qF1_c ≥ 0` on the constraint space.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 SuTwo)

section
variable [CfData]
variable {ell M R : ℕ}

/-- `G1inv` on an arbitrary Z-field of `E₀`. -/
theorem G1inv_zfield_gen (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t a : ℝ)
    (ht : |t| < Real.pi / 2) (f : ℕ → ℝ)
    (hf : (zfield f : BondFnL2 (scaleUp ell 2 (neLu M R))) ∈ bondSupp (geomOf ell 2 (neS ell M R))) :
    (((Pt ell M R (by omega) (neC0 ell M R) t a).G1inv ⟨zfield f, hf⟩ :
        ↥(bondSupp (Pt ell M R (by omega) (neC0 ell M R) t a).G)) : BondFnL2 (scaleUp ell 2 (neLu M R))) =
      zfield (ginvProf0 ell (isRowN ell M R) (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) (scaleUp ell 2 (neLu M R) 0)
        (neC0 ell M R) t a f) := by
  have hg := nGeo_two hell2 hdvd hM hR
  have hell : 0 < ell := by omega
  have S := nested_z0Setup hell2 hE hdvd hM hR t ht
  set P := Pt ell M R hell (neC0 ell M R) t a with hP
  have hcart : CartanCfg P.U := stag0Cfg_cartan _ t
  have hC : ∀ A : BondFnL2 P.Lf, SigB (WithLp.ofLp A) → P.sector.C2full A = 0 := fun A hA =>
    C2fullOf_sig0 S.z P.G S.hG S.hk A hA
  set x : ↥(bondSupp P.G) := ⟨zfield f, hf⟩ with hx
  have hxs : SigB (WithLp.ofLp (x : BondFnL2 P.Lf)) := fun b => zfun_diag _ b
  have hD2 := Delta2_sig P hcart hC x hxs
  have hG1 : P.G1inv = P.data.Ginv - P.data.Delta2 P.data_laws :=
    P.data.G1inv_unique P.G1inv_spec (P.data.isG1inv_sub P.data_laws)
  have h1 : P.G1inv x = P.data.Ginv x := by
    rw [hG1]; simp [hD2]
  rw [h1]
  exact Ginv_zfield0 S (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R)
    (by ext y; simp only [IngrBParams.G, geomOf, Set.mem_setOf_eq]; exact neS_om0 y)
    (fun j hj v h => hrowJ_nested hg hj v h) a P.Jf f hf

theorem G1inv_mem_WZ (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t a : ℝ)
    (ht : |t| < Real.pi / 2) {x : ↥(bondSupp (geomOf ell 2 (neS ell M R)))} (hx : x ∈ WZ (geomOf ell 2 (neS ell M R))) :
    (Pt ell M R (by omega) (neC0 ell M R) t a).G1inv x ∈ WZ (geomOf ell 2 (neS ell M R)) := by
  obtain ⟨f, hf⟩ := hx
  have hmem := x.2
  rw [hf] at hmem
  have hxe : x = ⟨zfield f, hmem⟩ := Subtype.ext hf
  rw [hxe]
  exact ⟨_, G1inv_zfield_gen hell2 hE hdvd hM hR t a ht f hmem⟩

theorem Qs_mem_WZ (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t a : ℝ)
    (ht : |t| < Real.pi / 2) {z : FSp (geomOf ell 2 (neS ell M R))} (hz : z ∈ ZF (geomOf ell 2 (neS ell M R))) :
    (Pt ell M R (by omega) (neC0 ell M R) t a).data.Qs z ∈ WZ (geomOf ell 2 (neS ell M R)) := by
  have hg := nGeo_two hell2 hdvd hM hR
  have S := nested_z0Setup hell2 hE hdvd hM hR t ht
  obtain ⟨ρ, rfl⟩ := hz
  have hmem : (zfield (CoverOmega.Wt ell (isRowN ell M R) ρ) : BondFnL2 (scaleUp ell 2 (neLu M R))) ∈
      bondSupp (geomOf ell 2 (neS ell M R)) := by
    refine zfield_mem_bondSupp _ (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) ?_ _ ?_
    · ext x; simp only [geomOf, Set.mem_setOf_eq]; exact neS_om0 x
    · intro v _ hv
      exact Wt_outside hg hv ρ
  have : (Pt ell M R (by omega) (neC0 ell M R) t a).data.Qs (zrow (geomOf ell 2 (neS ell M R)) ρ) =
      ⟨zfield (CoverOmega.Wt ell (isRowN ell M R) ρ), hmem⟩ := by
    apply ext_inner_left ℝ
    intro w
    show (inner ℝ w ((ContinuousLinearMap.adjoint ((bondSectorOf (geomOf ell 2 (neS ell M R)) (stag0Cfg (neC0 ell M R) t)).Qfull.comp
      (iE (geomOf ell 2 (neS ell M R))))) (zrow (geomOf ell 2 (neS ell M R)) ρ)) : ℝ) = _
    rw [ContinuousLinearMap.adjoint_inner_right]
    show (inner ℝ ((QfullOf (geomOf ell 2 (neS ell M R)) (stag0Cfg (neC0 ell M R) t)) (iE (geomOf ell 2 (neS ell M R)) w))
      (zrow (geomOf ell 2 (neS ell M R)) ρ) : ℝ) = _
    rw [inner_Q_zrow0 S]
    rfl
  rw [this]
  exact ⟨_, rfl⟩

theorem Q_mem_ZF (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t a : ℝ)
    (ht : |t| < Real.pi / 2) {x : ↥(bondSupp (geomOf ell 2 (neS ell M R)))} (hx : x ∈ WZ (geomOf ell 2 (neS ell M R))) :
    (Pt ell M R (by omega) (neC0 ell M R) t a).data.Q x ∈ ZF (geomOf ell 2 (neS ell M R)) := by
  have hg := nGeo_two hell2 hdvd hM hR
  have S := nested_z0Setup hell2 hE hdvd hM hR t ht
  obtain ⟨f, hf⟩ := hx
  have : (Pt ell M R (by omega) (neC0 ell M R) t a).data.Q x =
      QfullOf (geomOf ell 2 (neS ell M R)) (stag0Cfg (L := scaleUp ell 2 (neLu M R)) (neC0 ell M R) t) (x : BondFnL2 (scaleUp ell 2 (neLu M R))) := rfl
  rw [this, hf, Qfull_zfield_eq_zrow0 S f]
  exact ⟨_, rfl⟩


/-- the mass part of the Z-energy is a function of `Q x_e`. -/
theorem Kz_eq (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t a : ℝ)
    (ht : |t| < Real.pi / 2) (e : Fin (nN ell M R) → ℝ) :
    (inner ℝ (zfield (fe (neP0 ell M R) e) : BondFnL2 (scaleUp ell 2 (neLu M R)))
        (zfield (CoverOmega.Wt ell (isRowN ell M R) (fun j u => a * fSum ell j (fe (neP0 ell M R) e) u))) : ℝ) =
      (inner ℝ ((Pt ell M R (by omega) (neC0 ell M R) t a).data.Q (xE (nGeo_two hell2 hdvd hM hR) hell2 hM hR e))
        (diagW (geomOf ell 2 (neS ell M R)) (massW (geomOf ell 2 (neS ell M R)) a)
          ((Pt ell M R (by omega) (neC0 ell M R) t a).data.Q (xE (nGeo_two hell2 hdvd hM hR) hell2 hM hR e))) : ℝ) := by
  have S := nested_z0Setup hell2 hE hdvd hM hR t ht
  rw [← MassFull_zfield0 S a (fe (neP0 ell M R) e)]
  show (inner ℝ (zfield (fe (neP0 ell M R) e) : BondFnL2 (scaleUp ell 2 (neLu M R)))
    ((ContinuousLinearMap.adjoint (QfullOf (geomOf ell 2 (neS ell M R)) (stag0Cfg (neC0 ell M R) t)))
      (diagW (geomOf ell 2 (neS ell M R)) (massW (geomOf ell 2 (neS ell M R)) a)
        (QfullOf (geomOf ell 2 (neS ell M R)) (stag0Cfg (neC0 ell M R) t) (zfield (fe (neP0 ell M R) e))))) : ℝ) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  rfl

/-- **the Z-block bound.** -/
theorem zblock_ineq (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t a : ℝ)
    (ht : |t| < Real.pi / 2)
    (hG1 : IsUnit (Pt ell M R (by omega) (neC0 ell M R) t a).G1inv)
    (hN : IsUnit (GenP.Nmat (Pt ell M R (by omega) (neC0 ell M R) t a)))
    (hpsd : ∀ e' : Fin (nN ell M R) → ℝ, e' ∈ Vsub (rowOfN ell M R) → 0 ≤ qF1 (neC0 ell M R - neP0 ell M R) (Real.cos (2 * t)) e')
    (e : Fin (nN ell M R) → ℝ) :
    (inner ℝ ((Pt ell M R (by omega) (neC0 ell M R) t a).data.Q (xE (nGeo_two hell2 hdvd hM hR) hell2 hM hR e))
        (Ring.inverse (GenP.Nmat (Pt ell M R (by omega) (neC0 ell M R) t a))
          ((Pt ell M R (by omega) (neC0 ell M R) t a).data.Q (xE (nGeo_two hell2 hdvd hM hR) hell2 hM hR e))) : ℝ) ≤
      c0 * ((((scaleUp ell 2 (neLu M R)) 1 + 1) * ((scaleUp ell 2 (neLu M R)) 2 + 1) : ℕ) : ℝ) *
        qF1 (neC0 ell M R - neP0 ell M R) (Real.cos (2 * t)) e +
      (inner ℝ ((Pt ell M R (by omega) (neC0 ell M R) t a).data.Q (xE (nGeo_two hell2 hdvd hM hR) hell2 hM hR e))
        (diagW (geomOf ell 2 (neS ell M R)) (massW (geomOf ell 2 (neS ell M R)) a)
          ((Pt ell M R (by omega) (neC0 ell M R) t a).data.Q (xE (nGeo_two hell2 hdvd hM hR) hell2 hM hR e))) : ℝ) := by
  have hg := nGeo_two hell2 hdvd hM hR
  set P := Pt ell M R (by omega) (neC0 ell M R) t a with hP
  have hxW : xE hg hell2 hM hR e ∈ WZ (geomOf ell 2 (neS ell M R)) := ⟨fe (neP0 ell M R) e, rfl⟩
  have hNeq : GenP.Nmat P = P.data.Q.comp ((Ring.inverse P.G1inv).comp P.data.Qs) := by
    unfold GenP.Nmat
    exact ContinuousLinearMap.ext (fun _ => rfl)
  have hmin := AdalyNcwdhTwo.Min.minPrinciple (A := P.G1inv) P.G1inv_spec.symm hG1 (Q := P.data.Q) (Qs := P.data.Qs)
    P.data.Q_adj (by rw [← hNeq]; exact hN) (WZ (geomOf ell 2 (neS ell M R))) (ZF (geomOf ell 2 (neS ell M R)))
    (fun x hx => G1inv_mem_WZ hell2 hE hdvd hM hR t a ht hx) (fun z hz => Qs_mem_WZ hell2 hE hdvd hM hR t a ht hz)
    (fun x hx => Q_mem_ZF hell2 hE hdvd hM hR t a ht hx) (y := P.data.Q (xE hg hell2 hM hR e))
    (Q_mem_ZF hell2 hE hdvd hM hR t a ht hxW) (x := xE hg hell2 hM hR e) hxW rfl (by
      intro d hd hQd
      obtain ⟨e', hV, rfl⟩ := wz_chain hell2 hE hdvd hM hR t a ht hd hQd
      rw [inner_G1inv_zfield0 hell2 hE hdvd hM hR t a ht e', Kz_eq hell2 hE hdvd hM hR t a ht e', hQd]
      have hc0 : 0 < c0 := c0_pos
      have hT : 0 < (((scaleUp ell 2 (neLu M R)) 1 + 1) * ((scaleUp ell 2 (neLu M R)) 2 + 1) : ℕ) := by positivity
      have := hpsd e' hV
      simp only [inner_zero_left, add_zero]
      positivity)
  rw [← hNeq] at hmin
  rw [inner_G1inv_zfield0 hell2 hE hdvd hM hR t a ht e, Kz_eq hell2 hE hdvd hM hR t a ht e] at hmin
  exact hmin

end

end AdalyFormal.NcwdhTwo
