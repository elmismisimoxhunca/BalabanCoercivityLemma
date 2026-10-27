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

namespace AdalyFormal.Round10.Nonvanishing.TorusFlux

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (curlValue)
open AdalyFormal.Round10.Nonvanishing.Flux

variable {L : PeriodicLatticeExtent}

abbrev Slice (L : PeriodicLatticeExtent) := Fin (L 1+1) × Fin (L 2+1)

/-- The actual physical transverse section, with the longitudinal index periodic. -/
def site (L : PeriodicLatticeExtent) (x : ℕ) (t : Slice L) : PeriodicLatticeSite L := by
  intro μ
  refine Fin.cases (Fin.ofNat (L 0+1) x) ?_ μ
  intro ν
  refine Fin.cases t.1 ?_ ν
  intro κ
  refine Fin.cases t.2 ?_ κ
  intro j
  exact Fin.elim0 j

@[simp] theorem site_zero (x : ℕ) (t : Slice L) : site L x t 0 = Fin.ofNat (L 0+1) x := rfl
@[simp] theorem site_one (x : ℕ) (t : Slice L) : site L x t 1 = t.1 := rfl
@[simp] theorem site_two (x : ℕ) (t : Slice L) : site L x t 2 = t.2 := rfl

/-- Unit translation on the actual first transverse circle. -/
def shift1 (L : PeriodicLatticeExtent) : Slice L ≃ Slice L where
  toFun t := (t.1+1,t.2)
  invFun t := (t.1-1,t.2)
  left_inv t := by ext <;> simp
  right_inv t := by ext <;> simp

/-- Unit translation on the actual second transverse circle. -/
def shift2 (L : PeriodicLatticeExtent) : Slice L ≃ Slice L where
  toFun t := (t.1,t.2+1)
  invFun t := (t.1,t.2-1)
  left_inv t := by ext <;> simp
  right_inv t := by ext <;> simp

@[simp] theorem shift_site_zero (x : ℕ) (t : Slice L) :
    periodicLatticeShift (site L x t) 0 = site L (x+1) t := by
  funext μ
  fin_cases μ <;> simp [periodicLatticeShift]
  apply Fin.ext
  change (x % (L 0+1) + 1 % (L 0+1)) % (L 0+1) = (x+1) % (L 0+1)
  exact (Nat.add_mod x 1 (L 0+1)).symm

@[simp] theorem shift_site_one (x : ℕ) (t : Slice L) :
    periodicLatticeShift (site L x t) 1 = site L x (shift1 L t) := by
  funext μ
  fin_cases μ <;> simp [periodicLatticeShift,shift1]

@[simp] theorem shift_site_two (x : ℕ) (t : Slice L) :
    periodicLatticeShift (site L x t) 2 = site L x (shift2 L t) := by
  funext μ
  fin_cases μ <;> simp [periodicLatticeShift,shift2]

/-- A physical scalar bond field restricted to the indicated layer and direction. -/
def component (A : Bond L → ℝ) (μ : Fin 3) (x : ℕ) (t : Slice L) : ℝ :=
  A (site L x t,μ)

def plaq01 (L : PeriodicLatticeExtent) (x : ℕ) (t : Slice L) : PeriodicLatticePlaquette L :=
  (site L x t,⟨(0,1),by decide⟩)

def plaq02 (L : PeriodicLatticeExtent) (x : ℕ) (t : Slice L) : PeriodicLatticePlaquette L :=
  (site L x t,⟨(0,2),by decide⟩)

/-- No replacement curl: this is the frozen physical oriented plaquette formula. -/
theorem curl01 (A : Bond L → ℝ) (x : ℕ) (t : Slice L) :
    curlValue A (plaq01 L x t) = curl (shift1 L) (component A 0) (component A 1) x t := by
  simp [curlValue,plaq01,curl,component]

theorem curl02 (A : Bond L → ℝ) (x : ℕ) (t : Slice L) :
    curlValue A (plaq02 L x t) = curl (shift2 L) (component A 0) (component A 2) x t := by
  simp [curlValue,plaq02,curl,component]

/-- Exact physical transverse divergence theorem in the 0-1 plane. -/
theorem sum_curl01 (A : Bond L → ℝ) (x : ℕ) :
    ∑ t : Slice L, curlValue A (plaq01 L x t) =
      flux (component A 1) (x+1) - flux (component A 1) x := by
  simp_rw [curl01]
  exact sum_curl _ _ _ _

theorem sum_curl02 (A : Bond L → ℝ) (x : ℕ) :
    ∑ t : Slice L, curlValue A (plaq02 L x t) =
      flux (component A 2) (x+1) - flux (component A 2) x := by
  simp_rw [curl02]
  exact sum_curl _ _ _ _

/-- Nonzero physical coarse tangential flux forces a physical nonzero plaquette curl. -/
theorem exists_curl01 (A : Bond L → ℝ) (l p : ℕ) (hlp : l ≤ p)
    (hl : flux (component A 1) l = 0)
    (hb : coarseFlux (component A 1) p ≠ 0) :
    ∃ x, l ≤ x ∧ x < p+1 ∧ ∃ t : Slice L, curlValue A (plaq01 L x t) ≠ 0 := by
  simpa only [curl01] using
    exists_curl_of_coarseFlux (shift1 L) (component A 0) (component A 1) l p hlp hl hb

theorem exists_curl02 (A : Bond L → ℝ) (l p : ℕ) (hlp : l ≤ p)
    (hl : flux (component A 2) l = 0)
    (hb : coarseFlux (component A 2) p ≠ 0) :
    ∃ x, l ≤ x ∧ x < p+1 ∧ ∃ t : Slice L, curlValue A (plaq02 L x t) ≠ 0 := by
  simpa only [curl02] using
    exists_curl_of_coarseFlux (shift2 L) (component A 0) (component A 2) l p hlp hl hb

/-- The collar hypothesis can be supplied by zero level-zero rows. -/
theorem flux_zero_of_layer_zero (A : Bond L → ℝ) (μ : Fin 3) (l : ℕ)
    (h : ∀ t : Slice L, A (site L l t,μ) = 0) : flux (component A μ) l = 0 := by
  apply Finset.sum_eq_zero
  intro t _
  exact h t

#print axioms Slice
#print axioms site
#print axioms site_zero
#print axioms site_one
#print axioms site_two
#print axioms shift1
#print axioms shift2
#print axioms shift_site_zero
#print axioms shift_site_one
#print axioms shift_site_two
#print axioms component
#print axioms plaq01
#print axioms plaq02
#print axioms curl01
#print axioms curl02
#print axioms sum_curl01
#print axioms sum_curl02
#print axioms exists_curl01
#print axioms exists_curl02
#print axioms flux_zero_of_layer_zero
end AdalyFormal.Round10.Nonvanishing.TorusFlux
