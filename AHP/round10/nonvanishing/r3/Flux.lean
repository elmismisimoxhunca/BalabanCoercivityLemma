import DrEquiv

/-! Finite transverse flux and normalized two-site blocking.
The field-to-array identification is kept separate from these finite identities. -/
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace AdalyFormal.Round10.Nonvanishing.Flux

open Finset

variable {T : Type*} [Fintype T]

/-- Tangential flux through a longitudinal layer. -/
def flux (b : ℕ → T → ℝ) (x : ℕ) : ℝ := ∑ t, b x t

/-- Oriented 0-mu plaquette stencil, with periodic tangential shift `s`. -/
def curl (s : T ≃ T) (a b : ℕ → T → ℝ) (x : ℕ) (t : T) : ℝ :=
  a x t + b (x+1) t - a x (s t) - b x t

/-- Transverse divergence cancels exactly, not asymptotically. -/
theorem sum_curl (s : T ≃ T) (a b : ℕ → T → ℝ) (x : ℕ) :
    ∑ t, curl s a b x t = flux b (x+1) - flux b x := by
  have hs : ∑ t, a x (s t) = ∑ t, a x t := Equiv.sum_comp s (a x)
  simp only [curl, Finset.sum_sub_distrib, Finset.sum_add_distrib, flux]
  rw [hs]
  ring

/-- Zero plaquette curl makes layer flux constant on a finite interval. -/
theorem flux_eq_of_curl_zero (s : T ≃ T) (a b : ℕ → T → ℝ) (l n : ℕ)
    (hc : ∀ x, l ≤ x → x < l+n → ∀ t, curl s a b x t = 0) :
    flux b (l+n) = flux b l := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (fun x hxl hxn => hc x hxl (by omega))
    have hz : ∑ t, curl s a b (l+n) t = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      exact hc (l+n) (by omega) (by omega) t
    rw [sum_curl] at hz
    have : flux b (l+n+1) = flux b (l+n) := sub_eq_zero.mp hz
    simpa [Nat.add_assoc] using this.trans hprev

/-- One zero-flux collar layer is enough. No pointwise gauge choice is required. -/
theorem flux_zero_of_curl_zero (s : T ≃ T) (a b : ℕ → T → ℝ) (l h : ℕ)
    (hl : flux b l = 0)
    (hc : ∀ x, l ≤ x → x < h → ∀ t, curl s a b x t = 0)
    (x : ℕ) (hxl : l ≤ x) (hxh : x ≤ h) : flux b x = 0 := by
  have he := flux_eq_of_curl_zero s a b l (x-l)
    (fun y hyl hyx => hc y hyl (by omega))
  rw [Nat.add_sub_of_le hxl] at he
  exact he.trans hl

/-- Sum of the normalized level-one tangential rows at one longitudinal block. -/
noncomputable def coarseFlux (b : ℕ → T → ℝ) (p : ℕ) : ℝ :=
  (1/8 : ℝ) * (flux b p + flux b (p+1))

/-- A nonzero coarse tangential flux forces a nonzero interior plaquette curl. -/
theorem exists_curl_of_coarseFlux (s : T ≃ T) (a b : ℕ → T → ℝ) (l p : ℕ)
    (hlp : l ≤ p) (hl : flux b l = 0) (hb : coarseFlux b p ≠ 0) :
    ∃ x, l ≤ x ∧ x < p+1 ∧ ∃ t, curl s a b x t ≠ 0 := by
  classical
  by_contra hn
  have hc : ∀ x, l ≤ x → x < p+1 → ∀ t, curl s a b x t = 0 := by
    intro x hxl hxp t
    by_contra ht
    exact hn ⟨x,hxl,hxp,t,ht⟩
  have h0 := flux_zero_of_curl_zero s a b l (p+1) hl hc p hlp (by omega)
  have h1 := flux_zero_of_curl_zero s a b l (p+1) hl hc (p+1) (by omega) le_rfl
  apply hb
  simp [coarseFlux,h0,h1]

/-- The same conclusion for any nonzero prescribed multiple of the physical flux. -/
theorem exists_curl_of_jet (s : T ≃ T) (a b : ℕ → T → ℝ) (l p : ℕ)
    (jet factor : ℝ) (hlp : l ≤ p) (hl : flux b l = 0)
    (hdict : jet = factor * coarseFlux b p) (hj : jet ≠ 0) :
    ∃ x, l ≤ x ∧ x < p+1 ∧ ∃ t, curl s a b x t ≠ 0 := by
  apply exists_curl_of_coarseFlux s a b l p hlp hl
  intro hz
  apply hj
  rw [hdict,hz,mul_zero]

section Tiling
variable {C O : Type*} [Fintype C] [Fintype O]

/-- The printed ell=2 row sum: eight sites and two path links, coefficient 1/16.
A transverse tiling accounts for the four transverse offsets. -/
noncomputable def blockRow (tile : C × O ≃ T) (s : T ≃ T)
    (b : ℕ → T → ℝ) (p : ℕ) (c : C) : ℝ :=
  (1/16 : ℝ) * ∑ o, (b p (tile (c,o)) + b p (s (tile (c,o))) +
    b (p+1) (tile (c,o)) + b (p+1) (s (tile (c,o))))

/-- The exact physical normalization is 1/8 times two layer fluxes.
The transverse cardinality is already in the sum; no Bloch normalization occurs. -/
theorem sum_blockRow (tile : C × O ≃ T) (s : T ≃ T)
    (b : ℕ → T → ℝ) (p : ℕ) :
    ∑ c, blockRow tile s b p c = coarseFlux b p := by
  have hsum (f : T → ℝ) : (∑ c, ∑ o, f (tile (c,o))) = ∑ t, f t := by
    calc
      _ = ∑ co : C × O, f (tile co) := (Fintype.sum_prod_type (fun co : C × O => f (tile co))).symm
      _ = _ := Equiv.sum_comp tile f
  have hs (x : ℕ) : (∑ t, b x (s t)) = ∑ t, b x t := Equiv.sum_comp s (b x)
  simp only [blockRow, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [hsum (b p),hsum (fun t => b p (s t)),hsum (b (p+1)),
    hsum (fun t => b (p+1) (s t)),hs,hs]
  simp only [coarseFlux,flux]
  ring

/-- Direct finite-array interface for the genuine level-one blocking formula. -/
theorem exists_curl_of_blockRows (tile : C × O ≃ T) (s : T ≃ T)
    (a b : ℕ → T → ℝ) (l p : ℕ) (hlp : l ≤ p) (hl : flux b l = 0)
    (hb : (∑ c, blockRow tile s b p c) ≠ 0) :
    ∃ x, l ≤ x ∧ x < p+1 ∧ ∃ t, curl s a b x t ≠ 0 := by
  apply exists_curl_of_coarseFlux s a b l p hlp hl
  simpa [sum_blockRow] using hb
end Tiling

#print axioms flux
#print axioms curl
#print axioms sum_curl
#print axioms flux_eq_of_curl_zero
#print axioms flux_zero_of_curl_zero
#print axioms coarseFlux
#print axioms exists_curl_of_coarseFlux
#print axioms exists_curl_of_jet
#print axioms blockRow
#print axioms sum_blockRow
#print axioms exists_curl_of_blockRows
end AdalyFormal.Round10.Nonvanishing.Flux
