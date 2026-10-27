import M12_NV

/-!
# M12_W -- non-vacuity of the `{12, 12*ell}` Mixed / Family headlines at the parameters the p.409 result consumes (lane mixed12_20261019)

`factors12_curved_nonvacuous` : for EVERY `ell ≥ 2`, `m ≥ 1`, `R ≥ 1` (so in particular `R ≥ 21 ell` and `R ≥ R₁` for any `R₁`), `a₀ > 0`:
`k = 2`, a torus `Lu` with `ell^m < Lu μ + 1` (larger than one block) and `bigSide M ell k < scaleUp ell k Lu μ + 1` (p.409's `hgt`), an admissible three-stratum tower `S`,
`Λ ≠ ∅`, a CURVED non-pure-gauge `U` (`plaq U z ≠ 1` at a site of `Ω₂`), `α₀ > 0` with `12 ell · ell^m · α₀ ≤ a₀`, `ClassCoupledΦ` AND `ClassCoupledQ` (family `famPhi {12, 12 ell}`),
a nonzero `B̃ ∈ Λ̃`, class cubes of factor `12` and of factor `12 ell` through points of `Ω₀`, and no class cube of either factor equal to the whole torus.
`factors12_curved_nonvacuous_Q` is the same theorem with an extra predicate `Q k Lu S` on the witness tower (hypothesis `hQ` at `towerW`); `factors12_curved_nonvacuous` is its `Q := True` instance.
`factors12_instance_inequality` : the Family headline `p428Target8_factors_12_12ell_family` applied at that witness (constants `m₁, R₁, a₀, γ₀` first; `m ≥ m₁`, `R ≥ max R₁ (21 ell)`).
`factors12_instance_inequality_mixed` : the same through the Mixed headline `p428Target8_factors_12_12ell`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 64000000

namespace M12NV

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.NonVacC

theorem factors12_curved_nonvacuous_Q {ell m R : ℕ}
    (Q : ∀ (k : ℕ) (Lu : PeriodicLatticeExtent), Tower (scaleUp ell k Lu) → Prop)
    (hQ : Q 2 (nvcLu (ell ^ m) (max R (12 * ell))) (towerW ell (ell ^ m) R (max R (12 * ell))))
    (hell : 2 ≤ ell) (hm : 1 ≤ m) (hR : 1 ≤ R)
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
      2 ≤ k ∧ TorusOK ell (ell ^ m) Lu ∧ (∀ μ : Fin 3, ell ^ m < Lu μ + 1) ∧
      (∀ μ : Fin 3, bigSide (ell ^ m) ell k < scaleUp ell k Lu μ + 1) ∧
      Admissible ell (ell ^ m) R k S ∧ LambdaOK2 ell (ell ^ m) R k S Lam ∧
      0 < α₀ ∧ (12 * (ell : ℝ)) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧
      (∀ f ∈ M12.Phi12 ell, (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) ∧
      MXP.AllC.ClassCoupledΦ ell (ell ^ m) (M12.Phi12 ell) k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      MXQ.AllC.ClassCoupledQ ell (ell ^ m) (MXQ.Total.famPhi (M12.Phi12 ell)) k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      (∃ p, p ∈ towerBj S 0) ∧ (∃ p, p ∈ towerBj S 1) ∧ (∃ p, p ∈ towerBj S 2) ∧
      (∃ p, p ∉ S.Om 0) ∧
      (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
      (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
      Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
      (∀ f ∈ M12.Phi12 ell, ∀ j : ℕ, j ≤ k → ∀ μ : Fin 3,
        6 * (f * bigSide (ell ^ m) ell j) ≤ scaleUp ell k Lu μ + 1) ∧
      (∀ f ∈ M12.Phi12 ell, ∀ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
        IsClassCube ell (ell ^ m) f k S sites j → ∃ x, x ∉ sites) ∧
      (12 : ℕ) ≠ 12 * ell ∧
      (∃ x ∈ S.Om 0, ∃ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
        IsClassCube ell (ell ^ m) 12 k S sites j ∧ x ∈ sites ∧
        (sites, j, 12) ∈ MXQ.Total.famPhi (M12.Phi12 ell) (scaleUp ell k Lu)) ∧
      (∃ x ∈ S.Om 0, ∃ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
        IsClassCube ell (ell ^ m) (12 * ell) k S sites j ∧ x ∈ sites ∧
        (sites, j, 12 * ell) ∈ MXQ.Total.famPhi (M12.Phi12 ell) (scaleUp ell k Lu)) ∧
      Q k Lu S := by
  have hM : 0 < ell ^ m := pow_pos (by omega) m
  have h12 : (12 : ℕ) ∈ M12.Phi12 ell := Or.inl rfl
  have h12l : 12 * ell ∈ M12.Phi12 ell := Or.inr rfl
  obtain ⟨k, Lu, S, Lam, U, α₀, Bt, hk, hT, hA, hL, hα, hαS, hCC, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hLu,
    hper, hnw, hpres, hQS⟩ :=
    nonvac_core_Phi (ell := ell) (M := ell ^ m) (R := R) (T := max R (12 * ell)) Q hQ (M12.Phi12 ell) ⟨12, h12⟩
      (by
        intro f hf
        rcases hf with rfl | rfl
        · have := le_max_right R (12 * ell); omega
        · exact ⟨by omega, le_max_right _ _⟩)
      hell (dvd_pow_self ell (by omega)) hM hR (le_max_left _ _) (by have := le_max_left R (12 * ell); omega) ha₀
  have hα12l : (12 * (ell : ℝ)) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ := by
    have := hαS (12 * ell) h12l
    push_cast at this ⊢
    exact this
  have hgt : ∀ μ : Fin 3, bigSide (ell ^ m) ell k < scaleUp ell k Lu μ + 1 := by
    intro μ
    have := hper 12 h12 k le_rfl μ
    have hb : 0 < bigSide (ell ^ m) ell k := Nat.mul_pos hM (pow_pos (by omega) k)
    omega
  refine ⟨k, Lu, S, Lam, U, α₀, Bt, hk, hT, hLu, hgt, hA, hL, hα, hα12l, hαS, hCC, MXQ.Total.classCoupledΦ_toQ hCC,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hper, hnw, by omega, ?_, ?_, hQS⟩
  · obtain ⟨x, hx, sites, j, hq, hxs⟩ := hpres 12 h12
    exact ⟨x, hx, sites, j, hq, hxs, h12⟩
  · obtain ⟨x, hx, sites, j, hq, hxs⟩ := hpres (12 * ell) h12l
    exact ⟨x, hx, sites, j, hq, hxs, h12l⟩

theorem factors12_curved_nonvacuous {ell m R : ℕ} (hell : 2 ≤ ell) (hm : 1 ≤ m) (hR : 1 ≤ R)
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
      2 ≤ k ∧ TorusOK ell (ell ^ m) Lu ∧ (∀ μ : Fin 3, ell ^ m < Lu μ + 1) ∧
      (∀ μ : Fin 3, bigSide (ell ^ m) ell k < scaleUp ell k Lu μ + 1) ∧
      Admissible ell (ell ^ m) R k S ∧ LambdaOK2 ell (ell ^ m) R k S Lam ∧
      0 < α₀ ∧ (12 * (ell : ℝ)) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧
      (∀ f ∈ M12.Phi12 ell, (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) ∧
      MXP.AllC.ClassCoupledΦ ell (ell ^ m) (M12.Phi12 ell) k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      MXQ.AllC.ClassCoupledQ ell (ell ^ m) (MXQ.Total.famPhi (M12.Phi12 ell)) k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      (∃ p, p ∈ towerBj S 0) ∧ (∃ p, p ∈ towerBj S 1) ∧ (∃ p, p ∈ towerBj S 2) ∧
      (∃ p, p ∉ S.Om 0) ∧
      (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
      (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
      Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
      (∀ f ∈ M12.Phi12 ell, ∀ j : ℕ, j ≤ k → ∀ μ : Fin 3,
        6 * (f * bigSide (ell ^ m) ell j) ≤ scaleUp ell k Lu μ + 1) ∧
      (∀ f ∈ M12.Phi12 ell, ∀ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
        IsClassCube ell (ell ^ m) f k S sites j → ∃ x, x ∉ sites) ∧
      (12 : ℕ) ≠ 12 * ell ∧
      (∃ x ∈ S.Om 0, ∃ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
        IsClassCube ell (ell ^ m) 12 k S sites j ∧ x ∈ sites ∧
        (sites, j, 12) ∈ MXQ.Total.famPhi (M12.Phi12 ell) (scaleUp ell k Lu)) ∧
      (∃ x ∈ S.Om 0, ∃ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
        IsClassCube ell (ell ^ m) (12 * ell) k S sites j ∧ x ∈ sites ∧
        (sites, j, 12 * ell) ∈ MXQ.Total.famPhi (M12.Phi12 ell) (scaleUp ell k Lu)) := by
  obtain ⟨k, Lu, S, Lam, U, α₀, Bt, hk, hT, hLu, hgt, hA, hL, hα, hα12l, hαS, hCC, hCQ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    hper, hnw, hne, hc12, hc12l, -⟩ :=
    factors12_curved_nonvacuous_Q (ell := ell) (m := m) (R := R) (fun _ _ _ => True) trivial hell hm hR ha₀
  exact ⟨k, Lu, S, Lam, U, α₀, Bt, hk, hT, hLu, hgt, hA, hL, hα, hα12l, hαS, hCC, hCQ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    hper, hnw, hne, hc12, hc12l⟩

/-- **the Family headline `p428Target8_factors_12_12ell_family` applied at the curved witness.** -/
theorem factors12_instance_inequality (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ (a₀ γ₀ : ℝ), 0 < a₀ ∧ 0 < γ₀ ∧
      ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, max R₁ (21 * ell) ≤ R →
      ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
      2 ≤ k ∧ TorusOK ell (ell ^ m) Lu ∧ (∀ μ : Fin 3, ell ^ m < Lu μ + 1) ∧
      (∀ μ : Fin 3, bigSide (ell ^ m) ell k < scaleUp ell k Lu μ + 1) ∧
      Admissible ell (ell ^ m) R k S ∧ LambdaOK2 ell (ell ^ m) R k S Lam ∧
      0 < α₀ ∧ (12 * (ell : ℝ)) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧
      MXP.AllC.ClassCoupledΦ ell (ell ^ m) (M12.Phi12 ell) k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      MXQ.AllC.ClassCoupledQ ell (ell ^ m) (MXQ.Total.famPhi (M12.Phi12 ell)) k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
      (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
      Lam.Nonempty ∧ OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
      (∃ x ∈ S.Om 0, ∃ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
        IsClassCube ell (ell ^ m) 12 k S sites j ∧ x ∈ sites) ∧
      (∃ x ∈ S.Om 0, ∃ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
        IsClassCube ell (ell ^ m) (12 * ell) k S sites j ∧ x ∈ sites) ∧
      GenP.WellDefG (gparams ell k Lu (by omega) S U a Lam) ∧
      γ₀ * bondEnergy Bt ≤
        GenP.genForm (gparams ell k Lu (by omega) S U a Lam)
          (WithLp.toLp 2 (GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt)) := by
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ₀, hU⟩ := M12.p428Target8_factors_12_12ell_family ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, γ₀, ha₀, hγ₀, fun m hm R hR => ?_⟩
  have hR1 : 1 ≤ R := by have := le_max_right R₁ (21 * ell); omega
  obtain ⟨k, Lu, S, Lam, U, α₀, Bt, hk, hT, hLu, hgt, hA, hL, hα, hα12l, -, hCC, hCQ, -, -, -, -, hcv, hnp, hLam, -, hOT, hOT2, hen, hBt,
    -, -, -, hc12, hc12l⟩ := factors12_curved_nonvacuous (ell := ell) (m := m) (R := R) hell (le_trans hm₁ hm) hR1 ha₀
  have hmain := hU (MXQ.Total.famPhi (M12.Phi12 ell)) (fun L s j f hx => hx) m hm R (le_trans (le_max_left _ _) hR) k (by omega) Lu α₀
    hα hα12l hT S hA Lam hL U hCQ
  refine ⟨k, Lu, S, Lam, U, α₀, Bt, hk, hT, hLu, hgt, hA, hL, hα, hα12l, hCC, hCQ, hcv, hnp, hLam, hOT, hOT2, hen, hBt, ?_, ?_,
    hmain.1, hmain.2 Bt hOT hOT2⟩
  · obtain ⟨x, hx, sites, j, hq, hxs, -⟩ := hc12
    exact ⟨x, hx, sites, j, hq, hxs⟩
  · obtain ⟨x, hx, sites, j, hq, hxs, -⟩ := hc12l
    exact ⟨x, hx, sites, j, hq, hxs⟩

/-- **the Mixed headline `p428Target8_factors_12_12ell` applied at the same curved witness.** -/
theorem factors12_instance_inequality_mixed (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ (a₀ γ₀ : ℝ), 0 < a₀ ∧ 0 < γ₀ ∧
      ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, max R₁ (21 * ell) ≤ R →
      ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
      2 ≤ k ∧ TorusOK ell (ell ^ m) Lu ∧ (∀ μ : Fin 3, ell ^ m < Lu μ + 1) ∧
      (∀ μ : Fin 3, bigSide (ell ^ m) ell k < scaleUp ell k Lu μ + 1) ∧
      Admissible ell (ell ^ m) R k S ∧ LambdaOK2 ell (ell ^ m) R k S Lam ∧
      0 < α₀ ∧ (12 * (ell : ℝ)) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧
      MXP.AllC.ClassCoupledΦ ell (ell ^ m) (M12.Phi12 ell) k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
      (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
      Lam.Nonempty ∧ OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
      GenP.WellDefG (gparams ell k Lu (by omega) S U a Lam) ∧
      γ₀ * bondEnergy Bt ≤
        GenP.genForm (gparams ell k Lu (by omega) S U a Lam)
          (WithLp.toLp 2 (GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt)) := by
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ₀, hU⟩ := M12.p428Target8_factors_12_12ell ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, γ₀, ha₀, hγ₀, fun m hm R hR => ?_⟩
  have hR1 : 1 ≤ R := by have := le_max_right R₁ (21 * ell); omega
  obtain ⟨k, Lu, S, Lam, U, α₀, Bt, hk, hT, hLu, hgt, hA, hL, hα, hα12l, -, hCC, hCQ, -, -, -, -, hcv, hnp, hLam, -, hOT, hOT2, hen, hBt,
    -, -, -, -, -⟩ := factors12_curved_nonvacuous (ell := ell) (m := m) (R := R) hell (le_trans hm₁ hm) hR1 ha₀
  have hmain := hU m hm R (le_trans (le_max_left _ _) hR) k (by omega) Lu α₀ hα hα12l hT S hA Lam hL U hCC
  exact ⟨k, Lu, S, Lam, U, α₀, Bt, hk, hT, hLu, hgt, hA, hL, hα, hα12l, hCC, hcv, hnp, hLam, hOT, hOT2, hen, hBt,
    hmain.1, hmain.2 Bt hOT hOT2⟩

end M12NV

#print axioms M12NV.nonvac_core_Phi
#print axioms M12NV.factors12_curved_nonvacuous_Q
#print axioms M12NV.factors12_curved_nonvacuous
#print axioms M12NV.factors12_instance_inequality
#print axioms M12NV.factors12_instance_inequality_mixed
