import DLR93

/-!
# DL94 -- the model parameters of the `G⁻¹` / Schur chains as continuous functions of `(θ, ρ)` at `ρ → 0`, any `ℓ ≥ 2`, `a, t > 0`

* `GLv.*` : the `G⁻¹`-level and Schur-level constants at the model parameters (`rfl` bridges to `EGM0`, `ENfree`, `EGM1`,
  `EN1free`, `cg1`, `bN1`).
* `t*` lemmas : along any filter with `θ → θ₀` and `ρ → 0`, every model parameter (`cS δDS δQS bS cGS δCS κS δKS νS δνS δBS
  qBS δS bNS ThetaM0 KhatM0`) converges to its value at `(θ₀, 0)`.
* values at the degenerate point: `δDS 0 = δQS a 0 = δCS 0 = 0`, `κS 0 = νS 0 = 0`, `ThetaM0 ℓ a t 0 = 0`, `cS a 0 > 0`,
  `cGS ℓ a 0 0 > 0`, `KhatM0 ℓ a t 0 > 0`, `bNS a 0 (δS ℓ 0) > 0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.DLayer

open Filter Topology
open AdalyFormal.AsmM0 (KhatM0 ThetaM0 Mc phiC Stil Wc Vc)
open AdalyFormal.BondComposite (rr)

namespace GLv
noncomputable def EG (ell : ℕ) (a ρ θ ν δν : ℝ) : ℝ :=
  FF.EG (cS a ρ) (δDS θ) (δQS a θ) 1 (qS a) (cGS ell a ρ θ) (δCS θ) (κS ρ) (δKS ρ θ) ν δν (δBS ell a ρ θ) 1
noncomputable def nW (ell : ℕ) (a ρ θ : ℝ) : ℝ := FF.nW (cS a ρ) (δDS θ) (δQS a θ) 1 (qS a) (cGS ell a ρ θ)
noncomputable def dW (ell : ℕ) (a ρ θ : ℝ) : ℝ := FF.dW (cS a ρ) (δDS θ) (δQS a θ) 1 (qS a) (cGS ell a ρ θ)
noncomputable def δCW (ell : ℕ) (a ρ θ : ℝ) : ℝ :=
  FF.δCW (cS a ρ) (δDS θ) (δQS a θ) 1 (qS a) (cGS ell a ρ θ) (δCS θ) (κS ρ) (δKS ρ θ)
noncomputable def dT (ell : ℕ) (a ρ θ : ℝ) : ℝ := FF.dT (cS a ρ) (δDS θ) (δQS a θ) 1 (qS a) (cGS ell a ρ θ)
noncomputable def EN (ell : ℕ) (a ρ θ ν δν cg : ℝ) : ℝ :=
  FF.EN (EG ell a ρ θ ν δν) (nW ell a ρ θ) (dW ell a ρ θ) (δCW ell a ρ θ) (dT ell a ρ θ) ν δν (δBS ell a ρ θ) 1 cg
    (qBS ell a ρ)
end GLv

theorem EGM0_GL (ell : ℕ) (a ρ θ : ℝ) (hc : CondM0 ell a ρ θ) :
    EGM0 ell a ρ θ hc = GLv.EG ell a ρ θ (νS ρ) (δνS ρ θ) := rfl

theorem ENfree_GL (ell : ℕ) (a t ρ θ : ℝ) (hc : CondM0 ell a ρ θ) (hK : 0 < KhatM0 ell a t ρ)
    (hEG : 4 * EGM0 ell a ρ θ hc ≤ 1 / KhatM0 ell a t ρ) :
    ENfree ell a t ρ θ hc hK hEG = GLv.EN ell a ρ θ (νS ρ) (δνS ρ θ) (1 / KhatM0 ell a t ρ) := rfl

theorem EGM1_GL (ell : ℕ) (a ρ θ : ℝ) (hc : CondM0 ell a ρ θ) (νψ δψ : ℝ) (hν : 0 ≤ νψ) (hδ : 0 ≤ δψ) :
    EGM1 ell a ρ θ hc νψ δψ hν hδ = GLv.EG ell a ρ θ (νS ρ + νψ) (δνS ρ θ + δψ) := rfl

theorem EN1free_GL (ell : ℕ) (a t ρ θ : ℝ) (hc : CondM0 ell a ρ θ) (νψ δψ : ℝ) (hν : 0 ≤ νψ) (hδ : 0 ≤ δψ)
    (hK : 0 < KhatM0 ell a t ρ) (hcg : 0 < cg1 ell a t ρ θ hc νψ)
    (hEG : 4 * EGM1 ell a ρ θ hc νψ δψ hν hδ ≤ cg1 ell a t ρ θ hc νψ) :
    EN1free ell a t ρ θ hc νψ δψ hν hδ hK hcg hEG
      = GLv.EN ell a ρ θ (νS ρ + νψ) (δνS ρ θ + δψ) (cg1 ell a t ρ θ hc νψ) := rfl

theorem cg1_GL (ell : ℕ) (a t ρ θ : ℝ) (hc : CondM0 ell a ρ θ) (νψ : ℝ) :
    cg1 ell a t ρ θ hc νψ = 1 / KhatM0 ell a t ρ - νψ * GLv.nW ell a ρ θ ^ 2 := rfl

theorem bN1_GL (ell : ℕ) (a t ρ θ : ℝ) (hc : CondM0 ell a ρ θ) (νψ : ℝ) :
    bN1 ell a t ρ θ hc νψ = bNS a ρ (δS ell ρ) * (1 + νψ * GLv.nW ell a ρ θ ^ 2 * KhatM0 ell a t ρ) := rfl

/-! ## values at the degenerate point -/

theorem δDS_zero : δDS 0 = 0 := by unfold δDS; simp
theorem δQS_zero (a : ℝ) : δQS a 0 = 0 := by unfold δQS; simp
theorem δCS_zero : δCS 0 = 0 := by unfold δCS; simp
theorem κS_zero : κS 0 = 0 := by unfold κS; simp
theorem νS_zero : νS 0 = 0 := by unfold νS; simp
theorem δKS_zero (θ : ℝ) : δKS 0 θ = 0 := by unfold δKS; rw [κS_zero, zero_mul]
theorem δνS_zero (θ : ℝ) : δνS 0 θ = 0 := by unfold δνS; rw [νS_zero, zero_mul]
theorem δBS_zero (ell : ℕ) (a ρ : ℝ) : δBS ell a ρ 0 = 0 := by unfold δBS; simp
theorem phiC_zero (ell : ℕ) : phiC ell 0 = 0 := by unfold phiC; simp
theorem δS_zero (ell : ℕ) : δS ell 0 = 0 := by unfold δS; simp [phiC_zero]

theorem Mc_pos (a : ℝ) : 0 < Mc a := lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem cS_zero_pos (a : ℝ) : 0 < cS a 0 := by
  unfold cS
  have e : (1 : ℝ) - 216 * 0 ^ 2 = 1 := by norm_num
  rw [e]; exact div_pos one_pos (Mc_pos a)

theorem qS_pos (a : ℝ) (ha : 0 < a) : 0 < qS a := Real.sqrt_pos.mpr ha

theorem rr_pos (ell : ℕ) (hell : 1 ≤ ell) : 0 < rr ell := by
  unfold rr; apply Real.sqrt_pos.mpr; have : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  exact div_pos one_pos (by linarith)

theorem Theta_zero (ell : ℕ) (a t : ℝ) : ThetaM0 ell a t 0 = 0 := by
  unfold ThetaM0 AdalyFormal.AsmM0.Stil AdalyFormal.AsmM0.Vc
  simp [phiC_zero]

theorem bS_den_ne (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    (1 - 162 * (0 : ℝ)) ^ 2 * (a * (1 - 1 / ((ell : ℝ) * ell))) ≠ 0 := by
  have hl : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have h1 : 0 < 1 - 1 / ((ell : ℝ) * ell) := by
    rw [sub_pos, div_lt_one (by positivity)]; nlinarith
  have e : (1 - 162 * (0 : ℝ)) ^ 2 = 1 := by norm_num
  rw [e, one_mul]; exact (mul_pos ha h1).ne'

theorem bS_zero_pos (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) : 0 < bS ell a 0 := by
  unfold bS
  have hd := bS_den_ne ell hell a ha
  have h0 : 0 ≤ (Real.sqrt 78732 + 27 * Real.sqrt 12 * 0) ^ 2 / ((1 - 162 * (0 : ℝ)) ^ 2 * (a * (1 - 1 / ((ell : ℝ) * ell)))) := by
    apply div_nonneg (sq_nonneg _)
    have hl : (2 : ℝ) ≤ ell := by exact_mod_cast hell
    have h1 : 0 < 1 - 1 / ((ell : ℝ) * ell) := by
      rw [sub_pos, div_lt_one (by positivity)]; nlinarith
    have e : (1 - 162 * (0 : ℝ)) ^ 2 = 1 := by norm_num
    rw [e, one_mul]; exact (mul_pos ha h1).le
  linarith

theorem epsXf_zero (c q : ℝ) : epsXf c 0 0 q = 0 := by unfold epsXf; simp

theorem cGS_zero_pos (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) : 0 < cGS ell a 0 0 := by
  unfold cGS
  rw [δDS_zero, δQS_zero, epsXf_zero]
  have := qS_pos a ha
  have := bS_zero_pos ell hell a ha
  simp; positivity

theorem KhatM0_zero_pos (ell : ℕ) (a t : ℝ) (ha : 0 < a) (ht : 0 < t) : 0 < KhatM0 ell a t 0 := by
  unfold KhatM0
  rw [Theta_zero]
  have hm : 0 < min a 1 := lt_min ha one_pos
  have := Mc_pos a
  apply lt_of_lt_of_le _ (le_max_right _ _)
  simp; positivity

theorem bNS_zero_pos (ell : ℕ) (a : ℝ) : 0 < bNS a 0 (δS ell 0) := bNS_pos a 0 (δS ell 0) (by rw [νS_zero])

/-! ## continuity in `(θ, ρ)` at `ρ = 0` -/

section par
variable {X : Type*} {L : Filter X} {θ ρ : X → ℝ} {θ₀ : ℝ}

theorem texp {f : X → ℝ} {y : ℝ} (h : Tendsto f L (𝓝 y)) : Tendsto (fun x => Real.exp (f x)) L (𝓝 (Real.exp y)) :=
  (Real.continuous_exp.tendsto y).comp h

theorem tcS (hρ : Tendsto ρ L (𝓝 0)) (a : ℝ) : Tendsto (fun x => cS a (ρ x)) L (𝓝 (cS a 0)) := by
  unfold cS
  exact (tendsto_const_nhds.sub (tendsto_const_nhds.mul (hρ.pow 2))).div_const _

theorem tδDS (hθ : Tendsto θ L (𝓝 θ₀)) : Tendsto (fun x => δDS (θ x)) L (𝓝 (δDS θ₀)) := by
  unfold δDS
  exact tendsto_const_nhds.mul (hθ.mul (texp hθ))

theorem tδQS (hθ : Tendsto θ L (𝓝 θ₀)) (a : ℝ) : Tendsto (fun x => δQS a (θ x)) L (𝓝 (δQS a θ₀)) := by
  unfold δQS
  exact tendsto_const_nhds.mul ((texp (tendsto_const_nhds.mul hθ)).sub tendsto_const_nhds)

theorem tbS (hρ : Tendsto ρ L (𝓝 0)) (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x => bS ell a (ρ x)) L (𝓝 (bS ell a 0)) := by
  unfold bS
  exact (tdiv ((tendsto_const_nhds.add (tendsto_const_nhds.mul hρ)).pow 2)
    (((tendsto_const_nhds.sub (tendsto_const_nhds.mul hρ)).pow 2).mul tendsto_const_nhds)
    (bS_den_ne ell hell a ha)).add tendsto_const_nhds

theorem tcGS (hθ : Tendsto θ L (𝓝 θ₀)) (hρ : Tendsto ρ L (𝓝 0)) (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x => cGS ell a (ρ x) (θ x)) L (𝓝 (cGS ell a 0 θ₀)) := by
  unfold cGS
  have hb := tbS hρ ell hell a ha
  have hne : 2 * (qS a * bS ell a 0) ^ 2 ≠ 0 := by
    have := qS_pos a ha; have := bS_zero_pos ell hell a ha; positivity
  have he := FFlim.tepsX (tcS hρ a) (cS_zero_pos a) (tδDS hθ) (tδQS hθ a) (tendsto_const_nhds (x := (1 : ℝ)))
    (tendsto_const_nhds (x := qS a))
  exact (tcdiv 1 (tendsto_const_nhds.mul ((tendsto_const_nhds.mul hb).pow 2)) hne).sub
    (tendsto_const_nhds.mul (he.pow 2))

theorem tδCS (hθ : Tendsto θ L (𝓝 θ₀)) : Tendsto (fun x => δCS (θ x)) L (𝓝 (δCS θ₀)) := by
  unfold δCS
  exact tendsto_const_nhds.mul (hθ.mul (texp hθ))

theorem tκS (hρ : Tendsto ρ L (𝓝 0)) : Tendsto (fun x => κS (ρ x)) L (𝓝 (κS 0)) := by
  unfold κS
  exact tendsto_const_nhds.mul (hρ.div_const _)

theorem tδKS (hθ : Tendsto θ L (𝓝 θ₀)) (hρ : Tendsto ρ L (𝓝 0)) :
    Tendsto (fun x => δKS (ρ x) (θ x)) L (𝓝 (δKS 0 θ₀)) := by
  unfold δKS
  exact (tκS hρ).mul ((texp (tendsto_const_nhds.mul hθ)).sub tendsto_const_nhds)

theorem tνS (hρ : Tendsto ρ L (𝓝 0)) : Tendsto (fun x => νS (ρ x)) L (𝓝 (νS 0)) := by
  unfold νS
  exact tendsto_const_nhds.mul ((hρ.div_const _).div_const _)

theorem tδνS (hθ : Tendsto θ L (𝓝 θ₀)) (hρ : Tendsto ρ L (𝓝 0)) :
    Tendsto (fun x => δνS (ρ x) (θ x)) L (𝓝 (δνS 0 θ₀)) := by
  unfold δνS
  exact (tνS hρ).mul ((texp (tendsto_const_nhds.mul hθ)).sub tendsto_const_nhds)

theorem tδBS (hθ : Tendsto θ L (𝓝 θ₀)) (hρ : Tendsto ρ L (𝓝 0)) (ell : ℕ) (a : ℝ) :
    Tendsto (fun x => δBS ell a (ρ x) (θ x)) L (𝓝 (δBS ell a 0 θ₀)) := by
  unfold δBS
  exact ((tendsto_const_nhds.mul (texp ((tendsto_const_nhds.mul hρ).div_const _))).mul
    ((texp (tendsto_const_nhds.mul hθ)).sub tendsto_const_nhds)).mul tendsto_const_nhds

theorem tqBS (hρ : Tendsto ρ L (𝓝 0)) (ell : ℕ) (a : ℝ) :
    Tendsto (fun x => qBS ell a (ρ x)) L (𝓝 (qBS ell a 0)) := by
  unfold qBS
  exact tendsto_const_nhds.mul (texp ((tendsto_const_nhds.mul hρ).div_const _))

theorem tphiC {f : X → ℝ} {y : ℝ} (h : Tendsto f L (𝓝 y)) (ell : ℕ) :
    Tendsto (fun x => phiC ell (f x)) L (𝓝 (phiC ell y)) := by
  unfold phiC
  exact (h.div_const _).mul (texp (h.div_const _))

theorem tδS (hρ : Tendsto ρ L (𝓝 0)) (ell : ℕ) : Tendsto (fun x => δS ell (ρ x)) L (𝓝 (δS ell 0)) := by
  unfold δS
  exact tendsto_const_nhds.mul (tphiC (tendsto_const_nhds.mul hρ) ell)

theorem tbNS (hρ : Tendsto ρ L (𝓝 0)) (ell : ℕ) (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x => bNS a (ρ x) (δS ell (ρ x))) L (𝓝 (bNS a 0 (δS ell 0))) := by
  have hδ := tδS hρ ell
  have hA0 : (1 - δS ell 0) * Real.sqrt a ≠ 0 := by
    rw [δS_zero]; have := Real.sqrt_pos.mpr ha; simp; positivity
  have hA : Tendsto (fun x => A0S a (δS ell (ρ x))) L (𝓝 (A0S a (δS ell 0))) := by
    unfold A0S; exact tcdiv 1 ((tendsto_const_nhds.sub hδ).mul tendsto_const_nhds) hA0
  have hc := tcS hρ a
  have hc0 := cS_zero_pos a
  have hcN : Tendsto (fun x => cNS a (ρ x) (δS ell (ρ x))) L (𝓝 (cNS a 0 (δS ell 0))) := by
    unfold cNS; exact (tendsto_const_nhds.add (tendsto_const_nhds.mul hρ)).mul hA
  have hdN : Tendsto (fun x => dNS a (ρ x) (δS ell (ρ x))) L (𝓝 (dNS a 0 (δS ell 0))) := by
    unfold dNS; exact (tendsto_const_nhds.add (tendsto_const_nhds.mul hρ)).mul hA
  have hgN : Tendsto (fun x => gNS a (δS ell (ρ x))) L (𝓝 (gNS a (δS ell 0))) := by
    unfold gNS; exact tendsto_const_nhds.mul hA
  unfold bNS
  exact ((((hcN.add ((tκS hρ).mul (tdiv hdN hc hc0.ne'))).pow 2).add
    ((tνS hρ).mul ((hgN.add (tdiv hdN hc.sqrt (Real.sqrt_pos.mpr hc0).ne')).pow 2))).add (hdN.pow 2)).add
    tendsto_const_nhds

theorem tTheta (hρ : Tendsto ρ L (𝓝 0)) (ell : ℕ) (hell : 1 ≤ ell) (a t : ℝ) :
    Tendsto (fun x => ThetaM0 ell a t (ρ x)) L (𝓝 (ThetaM0 ell a t 0)) := by
  have hd : (1 : ℝ) - 162 * 0 ≠ 0 := by norm_num
  have hW : Tendsto (fun x => Wc (Real.sqrt 3) (ρ x)) L (𝓝 (Wc (Real.sqrt 3) 0)) := by
    unfold Wc
    exact tdiv (tendsto_const_nhds.mul (tendsto_const_nhds.add hρ)) (tendsto_const_nhds.sub (tendsto_const_nhds.mul hρ)) hd
  have hV : Tendsto (fun x => Vc (Real.sqrt 3) (Real.sqrt (Mc a)) (ρ x)) L (𝓝 (Vc (Real.sqrt 3) (Real.sqrt (Mc a)) 0)) := by
    unfold Vc
    exact (hW.mul tendsto_const_nhds).mul ((tendsto_const_nhds.mul hρ).add
      (tdiv ((tendsto_const_nhds.mul hρ).mul (tendsto_const_nhds.add hρ))
        (tendsto_const_nhds.sub (tendsto_const_nhds.mul hρ)) hd))
  have hS : Tendsto (fun x => Stil (Real.sqrt 3) (Real.sqrt (Mc a)) (ρ x)) L
      (𝓝 (Stil (Real.sqrt 3) (Real.sqrt (Mc a)) 0)) := by
    unfold Stil
    exact (hW.mul (((tendsto_const_nhds.mul hρ).mul tendsto_const_nhds).add hV)).add (tendsto_const_nhds.mul hρ)
  unfold ThetaM0
  exact ((hS.pow 2).add (tendsto_const_nhds.mul ((tendsto_const_nhds.mul (hρ.div_const _)).div_const _))).add
    (tendsto_const_nhds.mul ((tendsto_const_nhds.mul (hρ.pow 2)).add
      (tendsto_const_nhds.mul ((tphiC (tendsto_const_nhds.mul hρ) ell).pow 2))))

theorem tKhat (hρ : Tendsto ρ L (𝓝 0)) (ell : ℕ) (hell : 1 ≤ ell) (a t : ℝ) (ha : 0 < a) :
    Tendsto (fun x => KhatM0 ell a t (ρ x)) L (𝓝 (KhatM0 ell a t 0)) := by
  have hT := tTheta hρ ell hell a t
  have h1 : min a 1 / 1000 - ThetaM0 ell a t 0 ≠ 0 := by
    rw [Theta_zero, sub_zero]; exact (div_pos (lt_min ha one_pos) (by norm_num)).ne'
  have h2 : (1 : ℝ) - 216 * 0 ^ 2 ≠ 0 := by norm_num
  unfold KhatM0
  exact (tdiv tendsto_const_nhds (tendsto_const_nhds.sub hT) h1).max
    (tdiv tendsto_const_nhds (tendsto_const_nhds.sub (tendsto_const_nhds.mul (hρ.pow 2))) h2)

end par

#print axioms cGS_zero_pos
#print axioms tcGS
#print axioms tbNS
#print axioms tKhat

end AdalyFormal.DLayer
