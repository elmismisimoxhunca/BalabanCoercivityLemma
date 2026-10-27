import DLR95

/-!
# DL96 -- continuity at `ρ → 0` of the regime / unit / conclusion constants, any `ℓ`, and the proof-free forms of the `ψ`-constants

* `tkapHat`, `te2rho`, `tdCM0`, `tcBM0`, `tEbar`, `tthetaK2`, `tK2free`, `tJS`, `tgam0Form` : limits along any filter.
* `CHf`, `CH1f`, `nuf`, `deltaf`, `cg1f`, `bN1f` : the constants `CHfree`, `CH1free`, `nuPsi`, `deltaPsi`, `cg1`, `bN1` written
  without proof arguments (`rfl` bridges), and their limits at a FIXED slope `θ₁` as `ρ → 0`, `νψ → 0`, `δψ → 0`, `β → 0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open Filter Topology
open AdalyFormal.AsmM0 (KhatM0 ThetaM0 Mc phiC)
open AdalyFormal.BondComposite (rr)
open AdalyFormal.RegBgKU (kapHat Kc)
open AdalyFormal.NonflatJet (rhoOf r0)
open EstimatesLayer.E1E3 (e2Majorant e1Majorant gInvMajorant)
open AdalyFormal.M0Finish (dCM0 cBM0 EbarM0 gam0Form)

section lim
variable {X : Type*} {L : Filter X} {ρ : X → ℝ}

theorem tkapHat (hρ : Tendsto ρ L (𝓝 0)) (ell : ℕ) : Tendsto (fun x => kapHat ell (ρ x)) L (𝓝 0) := by
  have h : Tendsto (fun x => kapHat ell (ρ x)) L (𝓝 (kapHat ell 0)) := by
    unfold kapHat
    exact (tendsto_const_nhds.mul hρ).add (tendsto_const_nhds.mul ((hρ.div_const _).add (hρ.pow 2)))
  have e : kapHat ell 0 = 0 := by unfold kapHat; simp
  rwa [e] at h

theorem te2rho {f : X → ℝ} (hf : Tendsto f L (𝓝 0)) (ell : ℕ) :
    Tendsto (fun x => e2Majorant (rhoOf ell (f x))) L (𝓝 0) := by
  have hr : Tendsto (fun x => rhoOf ell (f x)) L (𝓝 0) := by
    have h : Tendsto (fun x => rhoOf ell (f x)) L (𝓝 (rhoOf ell 0)) := by
      unfold rhoOf; exact tendsto_const_nhds.mul (tendsto_const_nhds.mul hf)
    have e : rhoOf ell 0 = 0 := by unfold rhoOf; simp
    rwa [e] at h
  have h : Tendsto (fun x => e2Majorant (rhoOf ell (f x))) L (𝓝 (e2Majorant 0)) := by
    unfold e2Majorant e1Majorant gInvMajorant
    exact ((((texp (tendsto_const_nhds.mul hr)).sub tendsto_const_nhds).mul
      ((tendsto_const_nhds.add hr).add tendsto_const_nhds)).add (hr.mul tendsto_const_nhds)).add
      ((texp (tendsto_const_nhds.mul hr)).sub tendsto_const_nhds)
  have e : e2Majorant 0 = 0 := by unfold e2Majorant e1Majorant gInvMajorant; simp
  rwa [e] at h

theorem tdCM0 (hρ : Tendsto ρ L (𝓝 0)) (ell : ℕ) : Tendsto (fun x => dCM0 ell (ρ x)) L (𝓝 0) := by
  have hk := tkapHat hρ ell
  have he := te2rho hk ell
  have h : Tendsto (fun x => dCM0 ell (ρ x)) L
      (𝓝 ((ell : ℝ) ^ 3 * Real.sqrt (384 * ((ell : ℝ) * 0) ^ 2 + 480 * 0 ^ 2))) := by
    unfold dCM0
    exact tendsto_const_nhds.mul (((tendsto_const_nhds.mul ((tendsto_const_nhds.mul hk).pow 2)).add
      (tendsto_const_nhds.mul (he.pow 2))).sqrt)
  simpa using h

theorem tcBM0 (hρ : Tendsto ρ L (𝓝 0)) (ell : ℕ) :
    Tendsto (fun x => cBM0 ell (ρ x)) L (𝓝 (1 + (ell : ℝ) ^ 3 * Real.sqrt (1 / (ell : ℝ) ^ 3))) := by
  have h : Tendsto (fun x => cBM0 ell (ρ x)) L
      (𝓝 ((1 + (ell : ℝ) ^ 3 * Real.sqrt (1 / (ell : ℝ) ^ 3)) / (1 - 0))) := by
    unfold cBM0
    exact tdiv tendsto_const_nhds (tendsto_const_nhds.sub (tdCM0 hρ ell)) (by norm_num)
  simpa using h

theorem tEbar (hρ : Tendsto ρ L (𝓝 0)) (ell : ℕ) (hell : 1 ≤ ell) (a t : ℝ) (ha : 0 < a) :
    Tendsto (fun x => EbarM0 ell a t (ρ x)) L (𝓝 0) := by
  have hK := tKhat hρ ell hell a t ha
  have h : Tendsto (fun x => EbarM0 ell a t (ρ x)) L
      (𝓝 ((4 * (272 * (0 / (3 * Real.pi)) / (4 * Real.sqrt 2)) + 128 * 0 ^ 2
        + 128 * phiC ell (3600 * (ell : ℝ) * 0) ^ 2) * KhatM0 ell a t 0)) := by
    unfold EbarM0
    exact (((tendsto_const_nhds.mul ((tendsto_const_nhds.mul (hρ.div_const _)).div_const _)).add
      (tendsto_const_nhds.mul (hρ.pow 2))).add
      (tendsto_const_nhds.mul ((tphiC (tendsto_const_nhds.mul hρ) ell).pow 2))).mul hK
  simpa [phiC_zero] using h

theorem tthetaK2 (hρ : Tendsto ρ L (𝓝 0)) (ell : ℕ) :
    Tendsto (fun x => thetaK2 ell (ρ x)) L (𝓝 (1 / (ell : ℝ))) := by
  have h : Tendsto (fun x => thetaK2 ell (ρ x)) L (𝓝 (1 / (ell : ℝ) + 1536 * (ell : ℝ) ^ 2 * 0)) := by
    unfold thetaK2
    exact tendsto_const_nhds.add (tendsto_const_nhds.mul (te2rho hρ ell))
  simpa using h

theorem tK2free (hρ : Tendsto ρ L (𝓝 0)) (ell : ℕ) (hell : 2 ≤ ell) :
    Tendsto (fun x => K2free ell (ρ x)) L (𝓝 (K2s ell * Real.exp (2 * (3600 * (ell : ℝ) * 0) / rr ell) * ell
      / (1 - 1 / (ell : ℝ)))) := by
  have hl : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hne : (1 : ℝ) - 1 / (ell : ℝ) ≠ 0 := by
    have : 1 / (ell : ℝ) < 1 := by rw [div_lt_one (by positivity)]; linarith
    linarith
  unfold K2free
  exact tdiv ((tendsto_const_nhds.mul (texp ((tendsto_const_nhds.mul (tendsto_const_nhds.mul hρ)).div_const _))).mul
    tendsto_const_nhds) (tendsto_const_nhds.sub (tthetaK2 hρ ell)) hne

theorem tJS {β : X → ℝ} (hβ : Tendsto β L (𝓝 0)) : Tendsto (fun x => JSfree (β x)) L (𝓝 0) := by
  have h : Tendsto (fun x => JSfree (β x)) L (𝓝 ((0 + 40 * 0 ^ 2 + 4144 * 0 ^ 3 + 8192 * 0 ^ 4) / Real.sqrt 2)) := by
    unfold JSfree
    exact ((((hβ.add (tendsto_const_nhds.mul (hβ.pow 2))).add (tendsto_const_nhds.mul (hβ.pow 3))).add
      (tendsto_const_nhds.mul (hβ.pow 4)))).div_const _
  simpa using h

theorem tgam0Form {γ a : ℝ} {ε' εJ Et dC cB : X → ℝ} {ε₀ εJ₀ Et₀ dC₀ cB₀ : ℝ} (h1 : Tendsto ε' L (𝓝 ε₀))
    (h2 : Tendsto εJ L (𝓝 εJ₀)) (h3 : Tendsto Et L (𝓝 Et₀)) (h4 : Tendsto dC L (𝓝 dC₀)) (h5 : Tendsto cB L (𝓝 cB₀))
    (hne : 4 + Et₀ ≠ 0) :
    Tendsto (fun x => gam0Form γ a (ε' x) (εJ x) (Et x) (dC x) (cB x)) L (𝓝 (gam0Form γ a ε₀ εJ₀ Et₀ dC₀ cB₀)) := by
  unfold gam0Form
  exact (tdiv ((tendsto_const_nhds.sub h1).mul (tendsto_const_nhds.sub
    (((h3.mul tendsto_const_nhds).add (tendsto_const_nhds.mul (h4.pow 2))).mul (h5.pow 2))))
    (tendsto_const_nhds.add h3) hne).sub (((h1.mul tendsto_const_nhds).add (tendsto_const_nhds.mul h2)).mul (h5.pow 2))

end lim

/-! ## the `ψ`-constants without proof arguments -/

noncomputable def Xθ (θ : ℝ) : ℝ := (1 / θ + 2) * Real.sqrt (1 / θ + 2)

noncomputable def CHf (ell : ℕ) (a t ρ θ : ℝ) : ℝ :=
  Real.sqrt 3 * Real.sqrt a * Xθ θ
    * ((2 * KhatM0 ell a t ρ) * (qBS ell a ρ + δBS ell a ρ θ)
      / (1 / bNS a ρ (δS ell ρ) - GLv.EN ell a ρ θ (νS ρ) (δνS ρ θ) (1 / KhatM0 ell a t ρ)))

noncomputable def nuf (ell : ℕ) (a t ρ β θ : ℝ) : ℝ := 2 * CHf ell a t ρ θ * JSfree β * K2free ell ρ

noncomputable def deltaf (ell : ℕ) (a t ρ β θ : ℝ) : ℝ :=
  nuf ell a t ρ β θ * 648 * ((Real.exp (5 * θ) - 1) * (Real.exp (5 * θ) + 1))

noncomputable def cg1f (ell : ℕ) (a t ρ θ νψ : ℝ) : ℝ := 1 / KhatM0 ell a t ρ - νψ * GLv.nW ell a ρ θ ^ 2

noncomputable def bN1f (ell : ℕ) (a t ρ θ νψ : ℝ) : ℝ :=
  bNS a ρ (δS ell ρ) * (1 + νψ * GLv.nW ell a ρ θ ^ 2 * KhatM0 ell a t ρ)

noncomputable def CH1f (ell : ℕ) (a t ρ θ νψ δψ : ℝ) : ℝ :=
  Real.sqrt 3 * Real.sqrt a * Xθ θ
    * ((2 / cg1f ell a t ρ θ νψ) * (qBS ell a ρ + δBS ell a ρ θ)
      / (1 / bN1f ell a t ρ θ νψ - GLv.EN ell a ρ θ (νS ρ + νψ) (δνS ρ θ + δψ) (cg1f ell a t ρ θ νψ)))

theorem CHfree_CHf (ell : ℕ) (a t ρ θ : ℝ) (hc : CondM0 ell a ρ θ) (hK : 0 < KhatM0 ell a t ρ)
    (hEG : 4 * EGM0 ell a ρ θ hc ≤ 1 / KhatM0 ell a t ρ) : CHfree ell a t ρ θ hc hK hEG = CHf ell a t ρ θ := rfl

theorem nuPsi_nuf (ell : ℕ) (a t ρ β θ : ℝ) (hc : CondM0 ell a ρ θ) (hK : 0 < KhatM0 ell a t ρ)
    (hEG : 4 * EGM0 ell a ρ θ hc ≤ 1 / KhatM0 ell a t ρ) : nuPsi ell a t ρ β θ hc hK hEG = nuf ell a t ρ β θ := rfl

theorem deltaPsi_deltaf (ell : ℕ) (a t ρ β θ : ℝ) (hc : CondM0 ell a ρ θ) (hK : 0 < KhatM0 ell a t ρ)
    (hEG : 4 * EGM0 ell a ρ θ hc ≤ 1 / KhatM0 ell a t ρ) :
    deltaPsi ell a t ρ β θ hc hK hEG = deltaf ell a t ρ β θ := rfl

theorem CH1free_CH1f (ell : ℕ) (a t ρ θ : ℝ) (hc : CondM0 ell a ρ θ) (νψ δψ : ℝ) (hν : 0 ≤ νψ) (hδ : 0 ≤ δψ)
    (hK : 0 < KhatM0 ell a t ρ) (hcg : 0 < cg1 ell a t ρ θ hc νψ)
    (hEG : 4 * EGM1 ell a ρ θ hc νψ δψ hν hδ ≤ cg1 ell a t ρ θ hc νψ) :
    CH1free ell a t ρ θ hc νψ δψ hν hδ hK hcg hEG = CH1f ell a t ρ θ νψ δψ := rfl

/-! ## limits at a fixed slope `θ₁` -/
section fixed
variable {X : Type*} {L : Filter X} {ρ ν δ β : X → ℝ}

theorem tCHf (hρ : Tendsto ρ L (𝓝 0)) (ell : ℕ) (hell : 2 ≤ ell) (a t θ₁ : ℝ) (ha : 0 < a) (ht : 0 < t)
    (hG : cGS ell a 0 θ₁ ≠ 0)
    (hD : 1 / bNS a 0 (δS ell 0) - GLv.EN ell a 0 θ₁ (νS 0) (δνS 0 θ₁) (1 / KhatM0 ell a t 0) ≠ 0) :
    Tendsto (fun x => CHf ell a t (ρ x) θ₁) L (𝓝 (CHf ell a t 0 θ₁)) := by
  have hθ : Tendsto (fun _ : X => θ₁) L (𝓝 θ₁) := tendsto_const_nhds
  have hK := tKhat hρ ell (by omega) a t ha
  have hK0 := KhatM0_zero_pos ell a t ha ht
  have hb0 := bNS_zero_pos ell a
  unfold CHf
  exact tendsto_const_nhds.mul (tdiv ((tendsto_const_nhds.mul hK).mul ((tqBS hρ ell a).add (tδBS hθ hρ ell a)))
    ((tcdiv 1 (tbNS hρ ell a ha) hb0.ne').sub (tGLv_EN hθ hρ ell hell a ha hG (tνS hρ) (tδνS hθ hρ)
      (tcdiv 1 hK hK0.ne') (by positivity))) hD)

theorem tnuf (hρ : Tendsto ρ L (𝓝 0)) (hβ : Tendsto β L (𝓝 0)) (ell : ℕ) (hell : 2 ≤ ell) (a t θ₁ : ℝ) (ha : 0 < a)
    (ht : 0 < t) (hG : cGS ell a 0 θ₁ ≠ 0)
    (hD : 1 / bNS a 0 (δS ell 0) - GLv.EN ell a 0 θ₁ (νS 0) (δνS 0 θ₁) (1 / KhatM0 ell a t 0) ≠ 0) :
    Tendsto (fun x => nuf ell a t (ρ x) (β x) θ₁) L (𝓝 0) := by
  have h : Tendsto (fun x => nuf ell a t (ρ x) (β x) θ₁) L
      (𝓝 (2 * CHf ell a t 0 θ₁ * 0 * (K2s ell * Real.exp (2 * (3600 * (ell : ℝ) * 0) / rr ell) * ell
        / (1 - 1 / (ell : ℝ))))) := by
    unfold nuf
    exact ((tendsto_const_nhds.mul (tCHf hρ ell hell a t θ₁ ha ht hG hD)).mul (tJS hβ)).mul (tK2free hρ ell hell)
  simpa using h

theorem tdeltaf (hρ : Tendsto ρ L (𝓝 0)) (hβ : Tendsto β L (𝓝 0)) (ell : ℕ) (hell : 2 ≤ ell) (a t θ₁ : ℝ)
    (ha : 0 < a) (ht : 0 < t) (hG : cGS ell a 0 θ₁ ≠ 0)
    (hD : 1 / bNS a 0 (δS ell 0) - GLv.EN ell a 0 θ₁ (νS 0) (δνS 0 θ₁) (1 / KhatM0 ell a t 0) ≠ 0) :
    Tendsto (fun x => deltaf ell a t (ρ x) (β x) θ₁) L (𝓝 0) := by
  have h : Tendsto (fun x => deltaf ell a t (ρ x) (β x) θ₁) L
      (𝓝 (0 * 648 * ((Real.exp (5 * θ₁) - 1) * (Real.exp (5 * θ₁) + 1)))) := by
    unfold deltaf
    exact ((tnuf hρ hβ ell hell a t θ₁ ha ht hG hD).mul tendsto_const_nhds).mul tendsto_const_nhds
  simpa using h

theorem tcg1f (hρ : Tendsto ρ L (𝓝 0)) (hν : Tendsto ν L (𝓝 0)) (ell : ℕ) (hell : 2 ≤ ell) (a t θ₁ : ℝ)
    (ha : 0 < a) (ht : 0 < t) (hG : cGS ell a 0 θ₁ ≠ 0) :
    Tendsto (fun x => cg1f ell a t (ρ x) θ₁ (ν x)) L (𝓝 (cg1f ell a t 0 θ₁ 0)) := by
  have hθ : Tendsto (fun _ : X => θ₁) L (𝓝 θ₁) := tendsto_const_nhds
  have hK := tKhat hρ ell (by omega) a t ha
  have hK0 := KhatM0_zero_pos ell a t ha ht
  unfold cg1f
  exact (tcdiv 1 hK hK0.ne').sub (hν.mul ((tGLv_nW hθ hρ ell hell a ha hG).pow 2))

theorem tbN1f (hρ : Tendsto ρ L (𝓝 0)) (hν : Tendsto ν L (𝓝 0)) (ell : ℕ) (hell : 2 ≤ ell) (a t θ₁ : ℝ)
    (ha : 0 < a) (hG : cGS ell a 0 θ₁ ≠ 0) :
    Tendsto (fun x => bN1f ell a t (ρ x) θ₁ (ν x)) L (𝓝 (bN1f ell a t 0 θ₁ 0)) := by
  have hθ : Tendsto (fun _ : X => θ₁) L (𝓝 θ₁) := tendsto_const_nhds
  have hK := tKhat hρ ell (by omega) a t ha
  unfold bN1f
  exact (tbNS hρ ell a ha).mul (tendsto_const_nhds.add ((hν.mul ((tGLv_nW hθ hρ ell hell a ha hG).pow 2)).mul hK))

theorem tCH1f (hρ : Tendsto ρ L (𝓝 0)) (hν : Tendsto ν L (𝓝 0)) (hδ : Tendsto δ L (𝓝 0)) (ell : ℕ) (hell : 2 ≤ ell)
    (a t θ₁ : ℝ) (ha : 0 < a) (ht : 0 < t) (hG : cGS ell a 0 θ₁ ≠ 0)
    (hD : 1 / bN1f ell a t 0 θ₁ 0 - GLv.EN ell a 0 θ₁ (νS 0 + 0) (δνS 0 θ₁ + 0) (cg1f ell a t 0 θ₁ 0) ≠ 0) :
    Tendsto (fun x => CH1f ell a t (ρ x) θ₁ (ν x) (δ x)) L (𝓝 (CH1f ell a t 0 θ₁ 0 0)) := by
  have hθ : Tendsto (fun _ : X => θ₁) L (𝓝 θ₁) := tendsto_const_nhds
  have hK0 := KhatM0_zero_pos ell a t ha ht
  have hcg0 : cg1f ell a t 0 θ₁ 0 ≠ 0 := by
    unfold cg1f; rw [zero_mul, sub_zero]; exact (one_div_pos.mpr hK0).ne'
  have hbN0 : bN1f ell a t 0 θ₁ 0 ≠ 0 := by
    unfold bN1f; rw [zero_mul, zero_mul, add_zero, mul_one]; exact (bNS_zero_pos ell a).ne'
  have hcg := tcg1f hρ hν ell hell a t θ₁ ha ht hG
  unfold CH1f
  exact tendsto_const_nhds.mul (tdiv ((tcdiv 2 hcg hcg0).mul ((tqBS hρ ell a).add (tδBS hθ hρ ell a)))
    ((tcdiv 1 (tbN1f hρ hν ell hell a t θ₁ ha hG) hbN0).sub
      (tGLv_EN hθ hρ ell hell a ha hG ((tνS hρ).add hν) ((tδνS hθ hρ).add hδ) hcg hcg0)) hD)

end fixed

#print axioms tdCM0
#print axioms tgam0Form
#print axioms tCHf
#print axioms tnuf
#print axioms tCH1f

end AdalyFormal.DLayer
