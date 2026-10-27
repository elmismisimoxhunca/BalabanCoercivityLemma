
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

namespace AdalyFormal.Round10.Nonvanishing.Coordinate
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
variable {L : PeriodicLatticeExtent}
section Cube
variable {E : Type*} [AddCommGroup E]
def cube (g : ℕ → ℕ → ℕ → E) (n a b c : ℕ) : E :=
  ∑ i ∈ range n, ∑ j ∈ range n, ∑ k ∈ range n, g (a + i) (b + j) (c + k)
end Cube

def mkS (L : PeriodicLatticeExtent) (a b c : ℕ) : PeriodicLatticeSite L :=
  fun μ => ⟨(![a, b, c] μ) % (L μ + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem mkS_val (a b c : ℕ) (μ : Fin 3) : ((mkS L a b c) μ).val = (![a, b, c] μ) % (L μ + 1) := rfl

theorem mkS_val0 (a b c : ℕ) : ((mkS L a b c) 0).val = a % (L 0 + 1) := rfl

theorem mkS_val1 (a b c : ℕ) : ((mkS L a b c) 1).val = b % (L 1 + 1) := rfl

theorem mkS_val2 (a b c : ℕ) : ((mkS L a b c) 2).val = c % (L 2 + 1) := rfl

theorem mkS_eta (x : PeriodicLatticeSite L) : mkS L (x 0).val (x 1).val (x 2).val = x := by
  funext μ
  apply Fin.ext
  rw [mkS_val]
  fin_cases μ
  · simp [Nat.mod_eq_of_lt (x 0).isLt]
  · simp [Nat.mod_eq_of_lt (x 1).isLt]
  · simp [Nat.mod_eq_of_lt (x 2).isLt]

theorem shift_val_self (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ((periodicLatticeShift x μ) μ).val = ((x μ).val + 1) % (L μ + 1) := by
  simp [periodicLatticeShift, Fin.val_add]

theorem shift_val_ne (x : PeriodicLatticeSite L) (μ ν : Fin 3) (h : ν ≠ μ) :
    ((periodicLatticeShift x μ) ν) = x ν := by
  simp [periodicLatticeShift, Function.update_of_ne h]

theorem shift_mkS1 (a b c : ℕ) : periodicLatticeShift (mkS L a b c) 1 = mkS L a (b + 1) c := by
  funext ν
  apply Fin.ext
  by_cases h : ν = 1
  · subst h
    rw [shift_val_self, mkS_val1, mkS_val1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  · rw [shift_val_ne _ _ _ h, mkS_val, mkS_val]
    fin_cases ν <;> simp_all

theorem mkS_mem_block (Y : PeriodicLatticeSite L) (n : ℕ) (hfit : ∀ μ, (Y μ).val + n ≤ L μ + 1)
    (i j k : ℕ) (hi : i < n) (hj : j < n) (hk : k < n) :
    mkS L ((Y 0).val + i) ((Y 1).val + j) ((Y 2).val + k) ∈ blockOf Y n := by
  rw [mem_blockOf]
  intro μ
  have h0 := hfit 0; have h1 := hfit 1; have h2 := hfit 2
  fin_cases μ
  · simp only [Fin.zero_eta, mkS_val0]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [Fin.mk_one, mkS_val1]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [Fin.reduceFinMk, mkS_val2]
    rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem sum_block_eq_cube {E : Type*} [AddCommGroup E] [Module ℝ E] (Y : PeriodicLatticeSite L) (n : ℕ)
    (hfit : ∀ μ, (Y μ).val + n ≤ L μ + 1) (F : PeriodicLatticeSite L → E) :
    ∑ x ∈ blockOf Y n, F x = cube (fun a b c => F (mkS L a b c)) n (Y 0).val (Y 1).val (Y 2).val := by
  classical
  unfold cube
  have e : ∑ i ∈ range n, ∑ j ∈ range n, ∑ k ∈ range n, F (mkS L ((Y 0).val + i) ((Y 1).val + j) ((Y 2).val + k))
      = ∑ p ∈ range n ×ˢ (range n ×ˢ range n), F (mkS L ((Y 0).val + p.1) ((Y 1).val + p.2.1) ((Y 2).val + p.2.2)) := by
    simp only [Finset.sum_product]
  rw [e]
  symm
  refine Finset.sum_nbij' (fun p => mkS L ((Y 0).val + p.1) ((Y 1).val + p.2.1) ((Y 2).val + p.2.2))
    (fun x => ((x 0).val - (Y 0).val, (x 1).val - (Y 1).val, (x 2).val - (Y 2).val)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    exact mkS_mem_block Y n hfit _ _ _ hp.1 hp.2.1 hp.2.2
  · intro x hx
    rw [mem_blockOf] at hx
    simp only [Finset.mem_product, Finset.mem_range]
    refine ⟨?_, ?_, ?_⟩
    · have := hx 0; omega
    · have := hx 1; omega
    · have := hx 2; omega
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    have h0 := hfit 0; have h1 := hfit 1; have h2 := hfit 2
    simp only [mkS_val0, mkS_val1, mkS_val2]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp
  · intro x hx
    rw [mem_blockOf] at hx
    have a0 := hx 0; have a1 := hx 1; have a2 := hx 2
    have e0 : (Y 0).val + ((x 0).val - (Y 0).val) = (x 0).val := by omega
    have e1 : (Y 1).val + ((x 1).val - (Y 1).val) = (x 1).val := by omega
    have e2 : (Y 2).val + ((x 2).val - (Y 2).val) = (x 2).val := by omega
    simp only [e0, e1, e2]
    exact mkS_eta x
  · intro p hp
    rfl

#print axioms cube
#print axioms mkS
#print axioms mkS_val
#print axioms mkS_val0
#print axioms mkS_val1
#print axioms mkS_val2
#print axioms mkS_eta
#print axioms shift_val_self
#print axioms shift_val_ne
#print axioms shift_mkS1
#print axioms mkS_mem_block
#print axioms sum_block_eq_cube
end AdalyFormal.Round10.Nonvanishing.Coordinate

namespace AdalyFormal.Round10.Nonvanishing.PhysicalBlocking

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.QOne (qOnePathSum longBondValue_ell2)
open AdalyFormal.Round10.Nonvanishing.Coordinate (mkS mkS_val0 mkS_val1 mkS_val2 sum_block_eq_cube cube shift_mkS1)
open AdalyFormal.Round10.Nonvanishing.Flux
open AdalyFormal.Round10.Nonvanishing.TorusFlux

variable {L : PeriodicLatticeExtent} {ny nz : ℕ}

/-- Four transverse fine offsets per physical coarse cell. -/
def tiling (hy : ny*2 = L 1+1) (hz : nz*2 = L 2+1) :
    (Fin ny × Fin nz) × (Fin 2 × Fin 2) ≃ Slice L :=
  (Equiv.prodProdProdComm (Fin ny) (Fin nz) (Fin 2) (Fin 2)).trans
    ((finProdFinEquiv.trans (finCongr hy)).prodCongr
      (finProdFinEquiv.trans (finCongr hz)))

theorem site_tiling (hy : ny*2 = L 1+1) (hz : nz*2 = L 2+1)
    (x : ℕ) (c : Fin ny × Fin nz) (o : Fin 2 × Fin 2) :
    site L x (tiling hy hz (c,o)) = mkS L x (2*c.1.val+o.1.val) (2*c.2.val+o.2.val) := by
  funext μ
  apply Fin.ext
  fin_cases μ
  · simp [mkS]
  · have hlt : 2*c.1.val+o.1.val < L 1+1 := by omega
    change o.1.val + 2*c.1.val = (2*c.1.val+o.1.val) % (L 1+1)
    rw [Nat.mod_eq_of_lt hlt]
    omega
  · have hlt : 2*c.2.val+o.2.val < L 2+1 := by omega
    change o.2.val + 2*c.2.val = (2*c.2.val+o.2.val) % (L 2+1)
    rw [Nat.mod_eq_of_lt hlt]
    omega

/-- Actual even-site coarse bond, not a substituted one-cell torus. -/
def row (hy : ny*2 = L 1+1) (hz : nz*2 = L 2+1)
    (p : ℕ) (hp : p+2 ≤ L 0+1) (heven : p%2 = 0) (c : Fin ny × Fin nz) : CoarseBond L 2 :=
  (⟨mkS L p (2*c.1.val) (2*c.2.val),by
    rw [mem_CoarseLattice]
    intro μ
    have hpy : 2*c.1.val < L 1+1 := by omega
    have hpz : 2*c.2.val < L 2+1 := by omega
    fin_cases μ
    · simpa [mkS_val0,Nat.mod_eq_of_lt (show p < L 0+1 by omega)] using heven
    · simp [mkS_val1,Nat.mod_eq_of_lt hpy]
    · simp [mkS_val2,Nat.mod_eq_of_lt hpz]⟩,1)

/-- The exact frozen normalized scalar blocking row equals the finite-array row. -/
theorem qOnePathSum_row (hy : ny*2 = L 1+1) (hz : nz*2 = L 2+1)
    (p : ℕ) (hp : p+2 ≤ L 0+1) (heven : p%2 = 0)
    (A : Bond L → ℝ) (c : Fin ny × Fin nz) :
    qOnePathSum 2 A (row hy hz p hp heven c) =
      blockRow (tiling hy hz) (shift1 L) (component A 1) p c := by
  have hp0 : p < L 0+1 := by omega
  have hy0 : 2*c.1.val < L 1+1 := by omega
  have hz0 : 2*c.2.val < L 2+1 := by omega
  have hfit : ∀ μ, ((mkS L p (2*c.1.val) (2*c.2.val)) μ).val+2 ≤ L μ+1 := by
    intro μ
    fin_cases μ
    · simpa [mkS_val0,Nat.mod_eq_of_lt hp0] using hp
    · change (2*c.1.val) % (L 1+1) + 2 ≤ L 1+1
      rw [Nat.mod_eq_of_lt hy0]
      omega
    · change (2*c.2.val) % (L 2+1) + 2 ≤ L 2+1
      rw [Nat.mod_eq_of_lt hz0]
      omega
  simp only [qOnePathSum,row,longBondValue_ell2]
  rw [sum_block_eq_cube _ 2 hfit]
  simp only [mkS_val0,mkS_val1,mkS_val2,Nat.mod_eq_of_lt hp0,
    Nat.mod_eq_of_lt hy0,Nat.mod_eq_of_lt hz0]
  simp only [blockRow,component,← shift_site_one,site_tiling,shift_mkS1]
  simp [cube,Finset.sum_range_succ,Fintype.sum_prod_type,Fin.sum_univ_two]
  ring

/-- Sum over all physical even transverse cells, with the exact level-one factor. -/
theorem sum_qOnePathSum_row (hy : ny*2 = L 1+1) (hz : nz*2 = L 2+1)
    (p : ℕ) (hp : p+2 ≤ L 0+1) (heven : p%2 = 0) (A : Bond L → ℝ) :
    ∑ c : Fin ny × Fin nz, qOnePathSum 2 A (row hy hz p hp heven c) =
      coarseFlux (component A 1) p := by
  simp_rw [qOnePathSum_row]
  exact sum_blockRow _ _ _ _

/-- A nonzero sum of genuine scalar Q1 rows forces nonzero actual curl. -/
theorem exists_curl_of_qOnePathSum (hy : ny*2 = L 1+1) (hz : nz*2 = L 2+1)
    (p : ℕ) (hp : p+2 ≤ L 0+1) (heven : p%2 = 0) (A : Bond L → ℝ)
    (l : ℕ) (hlp : l ≤ p) (hl : flux (component A 1) l = 0)
    (hb : (∑ c : Fin ny × Fin nz, qOnePathSum 2 A (row hy hz p hp heven c)) ≠ 0) :
    ∃ x, l ≤ x ∧ x < p+1 ∧ ∃ t : Slice L,
      AdalyFormal.Balaban.LatticeOperators.curlValue A (plaq01 L x t) ≠ 0 := by
  apply exists_curl01 A l p hlp hl
  simpa [sum_qOnePathSum_row] using hb

open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

/-- Functionals commute with the actual flat Q1 jet, including its 1/2 factor. -/
theorem sum_Q1jet_row (hy : ny*2 = L 1+1) (hz : nz*2 = L 2+1)
    (p : ℕ) (hp : p+2 ≤ L 0+1) (heven : p%2 = 0)
    (hdiv : ∀ μ, 2 ∣ L μ+1) (A : Bond L → SuTwo) (φ : SuTwo →ₗ[ℝ] ℝ) :
    ∑ c : Fin ny × Fin nz, φ (Q1jet 2 flatCfg A (row hy hz p hp heven c)) =
      coarseFlux (component (fun e => φ (A e)) 1) p := by
  simp_rw [Q1jet_flat 2 (by decide) hdiv,AdalyFormal.IngredientFamily.q1SU2_functional]
  exact sum_qOnePathSum_row hy hz p hp heven _

/-- A level-one full-tower row is exactly the normalized Q1 jet. -/
theorem Qfull_level_one (G : TowerGeom L) (hG : G.ell = 2) (U : Cfg L)
    (A : BondFnL2 L) (p : BIdx G) (hp : (p.1 : ℕ) = 1)
    (c : CoarseBond L 2) (hc : p.2.1 = (c.1.1,c.2)) :
    QfullOf G U A p = Q1jet 2 U (fun e => A e) c := by
  change (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) •
    (WithLp.ofLp (QlinB G U p.1 A)) p.2.1 = _
  rw [hc,hp,QlinB_apply]
  simp only [QlinCompL,bgTower,AdalyFormal.Balaban.UbarTowerCov.UbarTower,
    hG,pow_zero,pow_one,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply]
  rfl

/-- Exact sum identity for genuine frozen full-tower rows on a transverse layer.
Only row membership/indexing is supplied; no Fourier or source-column formula is assumed. -/
theorem sum_Qfull_level_one (G : TowerGeom L) (hG : G.ell = 2)
    (hy : ny*2 = L 1+1) (hz : nz*2 = L 2+1)
    (p : ℕ) (hp : p+2 ≤ L 0+1) (heven : p%2 = 0)
    (hdiv : ∀ μ, 2 ∣ L μ+1) (A : BondFnL2 L) (φ : SuTwo →ₗ[ℝ] ℝ)
    (idx : Fin ny × Fin nz → BIdx G)
    (hi : ∀ c, ((idx c).1 : ℕ) = 1)
    (hb : ∀ c, (idx c).2.1 = ((row hy hz p hp heven c).1.1,1)) :
    ∑ c : Fin ny × Fin nz, φ (QfullOf G flatCfg A (idx c)) =
      coarseFlux (component (fun e => φ (A e)) 1) p := by
  have he (c : Fin ny × Fin nz) :=
    Qfull_level_one G hG flatCfg A (idx c) (hi c) (row hy hz p hp heven c) (hb c)
  simp_rw [he]
  exact sum_Q1jet_row hy hz p hp heven hdiv _ φ

/-- Nonzero aggregated genuine top jet implies nonzero curl of a constrained lift.
The constraint equality is the QH=1 application, kept explicit here. -/
theorem exists_curl_of_constrained_jet (G : TowerGeom L) (hG : G.ell = 2)
    (hy : ny*2 = L 1+1) (hz : nz*2 = L 2+1)
    (p : ℕ) (hp : p+2 ≤ L 0+1) (heven : p%2 = 0)
    (hdiv : ∀ μ, 2 ∣ L μ+1) (A : BondFnL2 L) (φ : SuTwo →ₗ[ℝ] ℝ)
    (z : FSp G) (idx : Fin ny × Fin nz → BIdx G)
    (hi : ∀ c, ((idx c).1 : ℕ) = 1)
    (hb : ∀ c, (idx c).2.1 = ((row hy hz p hp heven c).1.1,1))
    (hQ : QfullOf G flatCfg A = z)
    (l : ℕ) (hlp : l ≤ p)
    (hl : flux (component (fun e => φ (A e)) 1) l = 0)
    (hzjet : (∑ c : Fin ny × Fin nz, φ (z (idx c))) ≠ 0) :
    ∃ x, l ≤ x ∧ x < p+1 ∧ ∃ t : Slice L,
      AdalyFormal.Balaban.LatticeOperators.curlValue (fun e => φ (A e)) (plaq01 L x t) ≠ 0 := by
  apply exists_curl01 (fun e => φ (A e)) l p hlp hl
  have he := sum_Qfull_level_one G hG hy hz p hp heven hdiv A φ idx hi hb
  rw [hQ] at he
  exact he ▸ hzjet

/-- The level-zero constraint is literally the fine bond value. -/
theorem Qfull_level_zero (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L)
    (p : BIdx G) (hp : (p.1 : ℕ) = 0) : QfullOf G U A p = A p.2.1 := by
  change (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) •
    (WithLp.ofLp (QlinB G U p.1 A)) p.2.1 = _
  have he : QlinB G U p.1 A = A := by simpa only [hp] using QlinB_zero G U A
  rw [he]
  simp [hp]

/-- The actual quadratic jet is zero at every level-zero row. -/
theorem C2full_level_zero (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L)
    (p : BIdx G) (hp : (p.1 : ℕ) = 0) : C2fullOf G U A p = 0 := by
  have he : C2rawB G U p.1 A = 0 := by
    rw [C2rawB_eq]
    simp only [hp,C2CompL_zero,map_zero]
  change (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) •
    (WithLp.ofLp (C2rawB G U p.1 A)) p.2.1 = 0
  rw [he]
  simp

/-- QH=1 and the zero level-zero jet give the collar flux hypothesis automatically,
provided the collar bonds are identified as actual level-zero rows. -/
theorem collar_flux_zero (G : TowerGeom L) (U : Cfg L) (A v : BondFnL2 L)
    (hQ : QfullOf G U A = C2fullOf G U v) (φ : SuTwo →ₗ[ℝ] ℝ)
    (l : ℕ) (μ : Fin 3) (idx0 : Slice L → BIdx G)
    (hi : ∀ t, ((idx0 t).1 : ℕ) = 0)
    (hb : ∀ t, (idx0 t).2.1 = (site L l t,μ)) :
    flux (component (fun e => φ (A e)) μ) l = 0 := by
  apply flux_zero_of_layer_zero
  intro t
  have he := congrArg (fun z : FSp G => z (idx0 t)) hQ
  rw [Qfull_level_zero G U A (idx0 t) (hi t),
    C2full_level_zero G U v (idx0 t) (hi t),hb] at he
  rw [he,map_zero]

#print axioms Qfull_level_zero
#print axioms C2full_level_zero
#print axioms collar_flux_zero
#print axioms sum_Q1jet_row
#print axioms Qfull_level_one
#print axioms sum_Qfull_level_one
#print axioms exists_curl_of_constrained_jet
#print axioms tiling
#print axioms site_tiling
#print axioms row
#print axioms qOnePathSum_row
#print axioms sum_qOnePathSum_row
#print axioms exists_curl_of_qOnePathSum
end AdalyFormal.Round10.Nonvanishing.PhysicalBlocking
namespace AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane




#print axioms dilLu
#print axioms dilTower
#print axioms dil_unit_size
#print axioms dil_fine_size
end AdalyFormal.Round4.Guarded.RefuteR1

namespace AdalyFormal.Round10.Nonvanishing.DilatedFlux

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (curlValue)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Round10.Nonvanishing.Flux
open AdalyFormal.Round10.Nonvanishing.TorusFlux
open AdalyFormal.Round10.Nonvanishing.Coordinate (mkS mkS_val0)
open AdalyFormal.Round10.Nonvanishing.PhysicalBlocking

abbrev L (q R : ℕ) := scaleUp 2 1 (dilLu q R)
abbrev G (q R : ℕ) := geomOf 2 1 (dilTower q R)
def blockCount (q R : ℕ) : ℕ := 4*q*(R+1)
def blockBase (q R j : ℕ) : ℕ := 2*(R*q)+4*q+2*j

theorem side_one {q : ℕ} (hq : 0 < q) (R : ℕ) : (4*q)*2 = L q R 1+1 := by
  rw [dil_fine_size hq,if_neg (show (1 : Fin 3) ≠ 0 by decide)]
  omega

theorem side_two {q : ℕ} (hq : 0 < q) (R : ℕ) : (4*q)*2 = L q R 2+1 := by
  rw [dil_fine_size hq,if_neg (show (2 : Fin 3) ≠ 0 by decide)]
  omega

theorem blockBase_even (q R j : ℕ) : blockBase q R j % 2 = 0 := by
  simp [blockBase,Nat.add_mod,Nat.mul_mod]

theorem blockBase_bounds {q R j : ℕ} (hq : 0 < q) (hj : j < blockCount q R) :
    2*(R*q)+4*q ≤ blockBase q R j ∧
    blockBase q R j+2 ≤ 10*(R*q)+12*q ∧
    blockBase q R j+2 ≤ L q R 0+1 := by
  have hc : blockCount q R = 4*(R*q)+4*q := by unfold blockCount; ring
  rw [hc] at hj
  rw [dil_fine_size hq]
  norm_num
  unfold blockBase
  omega

theorem two_dvd_sides {q : ℕ} (hq : 0 < q) (R : ℕ) : ∀ μ, 2 ∣ L q R μ+1 := by
  intro μ
  rw [dil_fine_size hq]
  split <;> omega

/-- Actual top-level row at every physical even transverse site. -/
def topIdx {q R j : ℕ} (hq : 0 < q) (hj : j < blockCount q R)
    (c : Fin (4*q) × Fin (4*q)) : BIdx (G q R) :=
  let r := row (side_one hq R) (side_two hq R) (blockBase q R j)
    (blockBase_bounds hq hj).2.2 (blockBase_even q R j) c
  ⟨⟨1,by change 1 < 1+1; decide⟩,⟨(r.1.1,1),by
    refine ⟨Or.inl ?_,?_⟩
    · change (∀ μ : Fin 3, 2^1 ∣ (r.1.1 μ).val) ∧ r.1.1 ∈ (dilTower q R).Om 1 ∧
        r.1.1 ∉ (dilTower q R).Om 2
      refine ⟨?_,?_,?_⟩
      · have he := mem_CoarseLattice.mp r.1.2
        intro μ
        simpa using Nat.dvd_of_mod_eq_zero (he μ)
      · have hbounds := blockBase_bounds hq hj
        change 2*(R*q)+4*q ≤ (r.1.1 0).val ∧ (r.1.1 0).val < 10*(R*q)+12*q
        change 2*(R*q)+4*q ≤ blockBase q R j % (L q R 0+1) ∧
          blockBase q R j % (L q R 0+1) < 10*(R*q)+12*q
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      · simp [dilTower]
    · intro hh
      rcases hh with hh | hh
      · exact not_OmGe_of_lt (G := G q R) (j := 2) (by change 1 < 2; decide) _ hh
      · exact not_OmGe_of_lt (G := G q R) (j := 2) (by change 1 < 2; decide) _ hh⟩⟩

@[simp] theorem topIdx_level {q R j : ℕ} (hq : 0 < q) (hj : j < blockCount q R)
    (c : Fin (4*q) × Fin (4*q)) : ((topIdx hq hj c).1 : ℕ) = 1 := rfl

@[simp] theorem topIdx_bond {q R j : ℕ} (hq : 0 < q) (hj : j < blockCount q R)
    (c : Fin (4*q) × Fin (4*q)) :
    (topIdx hq hj c).2.1 =
      ((row (side_one hq R) (side_two hq R) (blockBase q R j)
        (blockBase_bounds hq hj).2.2 (blockBase_even q R j) c).1.1,1) := rfl

/-- Omega_1 cannot reach the left collar through a positive-size block. -/
theorem not_OmGe_one {q R : ℕ} {x : PeriodicLatticeSite (L q R)}
    (hx : (x 0).val < 2*(R*q)+4*q) : ¬ OmGe (G q R) 1 x := by
  rintro ⟨i,hi,hik,y,hy,hyx⟩
  have he : i = 1 := by change i ≤ 1 at hik; omega
  subst i
  have hy0 : 2*(R*q)+4*q ≤ (y 0).val := hy.2.1.1
  have := (hyx 0).1
  omega

/-- The direction-1 bonds at the first Omega_0 layer are genuine level-zero rows. -/
def collarIdx {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (t : Slice (L q R)) : BIdx (G q R) :=
  ⟨⟨0,by change 0 < 1+1; decide⟩,⟨(site (L q R) (4*q) t,1),by
    have hmul : 0 < R*q := Nat.mul_pos hR hq
    have hside : L q R 0+1 = 12*(R*q)+16*q := by
      simpa [L] using dil_fine_size hq R 0
    have hx : (site (L q R) (4*q) t 0).val = 4*q := by
      change (4*q) % (L q R 0+1) = 4*q
      rw [Nat.mod_eq_of_lt (by omega)]
    refine ⟨Or.inl ?_,?_⟩
    · change (∀ μ, 2^0 ∣ (site (L q R) (4*q) t μ).val) ∧
        site (L q R) (4*q) t ∈ (dilTower q R).Om 0 ∧
        site (L q R) (4*q) t ∉ (dilTower q R).Om 1
      refine ⟨by simp,?_,?_⟩
      · change 4*q ≤ (site (L q R) (4*q) t 0).val ∧
          (site (L q R) (4*q) t 0).val < 12*(R*q)+12*q
        rw [hx]
        omega
      · change ¬ (2*(R*q)+4*q ≤ (site (L q R) (4*q) t 0).val ∧
          (site (L q R) (4*q) t 0).val < 10*(R*q)+12*q)
        rw [hx]
        omega
    · intro hh
      rcases hh with hh | hh
      · exact not_OmGe_one (by rw [hx]; omega) hh
      · apply not_OmGe_one (x := coarseShift (site (L q R) (4*q) t) 1 1) _ hh
        simpa [coarseShift,site_zero] using
          (show (4*q) % (L q R 0+1) < 2*(R*q)+4*q by
            change (site (L q R) (4*q) t 0).val < _
            rw [hx]; omega)⟩⟩

@[simp] theorem collarIdx_level {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (t : Slice (L q R)) : ((collarIdx hq hR t).1 : ℕ) = 0 := rfl

@[simp] theorem collarIdx_bond {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (t : Slice (L q R)) : (collarIdx hq hR t).2.1 = (site (L q R) (4*q) t,1) := rfl

/-- Every plaquette located between this collar and the selected top block lies inside Omega_0. -/
theorem plaq01_in {q R j : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (hj : j < blockCount q R) {x : ℕ} (hxl : 4*q ≤ x) (hxp : x < blockBase q R j+1)
    (t : Slice (L q R)) : plaq01 (L q R) x t ∈ plaqIn ((dilTower q R).Om 0) := by
  have hbounds := blockBase_bounds hq hj
  have hmul : 0 < R*q := Nat.mul_pos hR hq
  have hside : L q R 0+1 = 12*(R*q)+16*q := by
    simpa [L] using dil_fine_size hq R 0
  have hx : x < L q R 0+1 := by omega
  have hx1 : x+1 < L q R 0+1 := by omega
  simp [plaqIn,periodicPlaquetteBoundaryEdges,plaq01,dilTower,
    shift_site_zero,shift_site_one,site_zero,
    Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hx1]
  omega

/-- Physical sum of the actual quadratic top jet, retaining its 1/2 normalization. -/
noncomputable def jetAggregate {q R j : ℕ} (hq : 0 < q) (hj : j < blockCount q R)
    (φ : SuTwo →ₗ[ℝ] ℝ) (v : BondFnL2 (L q R)) : ℝ :=
  ∑ c : Fin (4*q) × Fin (4*q), φ (C2fullOf (G q R) flatCfg v (topIdx hq hj c))

/-- For the actual dilated geometry, a nonzero aggregated top jet detects localized curl.
This theorem does NOT assert that a vacuum crossing vector has a nonzero aggregate. -/
theorem localized_curl_of_jetAggregate {q R j : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (hj : j < blockCount q R) (φ : SuTwo →ₗ[ℝ] ℝ) (A v : BondFnL2 (L q R))
    (hQ : QfullOf (G q R) flatCfg A = C2fullOf (G q R) flatCfg v)
    (hne : jetAggregate hq hj φ v ≠ 0) :
    ∃ p ∈ plaqIn ((dilTower q R).Om 0), curlValue (fun e => φ (A e)) p ≠ 0 := by
  have hz := collar_flux_zero (G q R) flatCfg A v hQ φ (4*q) 1
    (collarIdx hq hR) (collarIdx_level hq hR) (collarIdx_bond hq hR)
  obtain ⟨x,hxl,hxp,t,ht⟩ := exists_curl_of_constrained_jet (G q R) rfl
    (side_one hq R) (side_two hq R) (blockBase q R j) (blockBase_bounds hq hj).2.2
    (blockBase_even q R j) (two_dvd_sides hq R) A φ (C2fullOf (G q R) flatCfg v)
    (topIdx hq hj) (topIdx_level hq hj) (topIdx_bond hq hj) hQ (4*q)
    (by unfold blockBase; omega) hz hne
  exact ⟨plaq01 (L q R) x t,plaq01_in hq hR hj hxl hxp t,ht⟩

open scoped RealInnerProductSpace
open AdalyFormal.Balaban.SuTwoInner (pauliE3)

#print axioms L
#print axioms G
#print axioms blockCount
#print axioms blockBase
#print axioms side_one
#print axioms side_two
#print axioms blockBase_even
#print axioms blockBase_bounds
#print axioms two_dvd_sides
#print axioms topIdx
#print axioms topIdx_level
#print axioms topIdx_bond
#print axioms not_OmGe_one
#print axioms collarIdx
#print axioms collarIdx_level
#print axioms collarIdx_bond
#print axioms plaq01_in
#print axioms jetAggregate
#print axioms localized_curl_of_jetAggregate
end AdalyFormal.Round10.Nonvanishing.DilatedFlux
