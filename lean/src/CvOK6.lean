import CvOK5

/-!
# CvOK6 -- the pole of the chain model for the relaxed row geometry: corank-1 crossing, nonvanishing window multipliers (lane omega)

`chain_poleD`: like CvK7 `chain_pole` for `RowGeomD` (collar singleton end rows), with the additional conclusions needed for the bordered determinant:
 PSD on `V` at `cs`, positive definite for `c in (cs,1]`, and the radical at `cs` is ONE-DIMENSIONAL (every `e in V` with `qF cs e = 0` is a multiple of `es`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open Finset
open AdalyFormal.CoverJacobi

variable {n a b : ℕ}

theorem BF_smul_left (C : ℕ) (c t : ℝ) (e f : Fin n → ℝ) : BF C c (t • e) f = t * BF C c e f := by
  unfold BF
  simp only [dlt_smul]
  have : ∑ y ∈ range (n - 1), t * dlt e y * dlt f y = t * ∑ y ∈ range (n - 1), dlt e y * dlt f y := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun y _ => by ring)
  rw [this]; ring

theorem BF_add_left (C : ℕ) (c : ℝ) (e f g : Fin n → ℝ) : BF C c (e + f) g = BF C c e g + BF C c f g := by
  unfold BF
  simp only [dlt_add]
  have : ∑ y ∈ range (n - 1), (dlt e y + dlt f y) * dlt g y =
      ∑ y ∈ range (n - 1), dlt e y * dlt g y + ∑ y ∈ range (n - 1), dlt f y * dlt g y := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun y _ => by ring)
  rw [this]; ring

theorem nx_smul (t : ℝ) (e : Fin n → ℝ) (x : ℤ) : nx (t • e) x = t * nx e x := by
  unfold nx
  by_cases h : 0 < n
  · simp [dif_pos h]
  · simp [dif_neg h]

theorem nx_sub (e f : Fin n → ℝ) (x : ℤ) : nx (e - f) x = nx e x - nx f x := by
  unfold nx
  by_cases h : 0 < n
  · simp [dif_pos h]
  · simp [dif_neg h]

/-- the window multipliers cannot vanish on two rows. -/
theorem chain_tailD {R : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeomD n R a b st ln rowOf) (C : ℕ) (c : ℝ)
    (hC1 : 1 ≤ C) (hC2 : C + 1 < n) {e : Fin n → ℝ} (he : e ∈ Vsub rowOf) (hne : e ≠ 0)
    (hrad : ∀ d : Fin n → ℝ, d ∈ Vsub rowOf → BF C c e d = 0)
    {i0 : ℕ} (ha1 : 1 ≤ a) (hia : a + 1 ≤ i0) (hC : st i0 = C) (hL : 3 ≤ ln i0)
    (hc : c ≠ 0) (hnl : ((ln i0 : ℝ) - 2) * ((ln i0 : ℝ) + 3) / 6 + 1 / c ≠ 0)
    {i1 N Lw : ℕ} (hi1 : i0 < i1) (hN : 1 ≤ N) (hi1N : i1 + N + b < R) (hLw : ∀ k, k ≤ N → ln (i1 + k) = Lw)
    {a b : ℕ} (hab : a < b) (hbN : b ≤ N)
    (ha : rowMu C c e st (i1 + a) = 0) (hb : rowMu C c e st (i1 + b) = 0) : False := by
  have hLw2 : 2 ≤ Lw := by
    have := g.lnI (i1 + 0) (by omega) (by omega)
    rwa [hLw 0 (Nat.zero_le _)] at this
  have hright : ∀ i, i0 < i → ∀ j, st i + j ≥ C + 3 := by
    intro i hi j
    have h1' := st_monoD g (show i0 + 1 ≤ i by omega)
    have h2 := g.stS i0
    omega
  have hflat_of : ∀ i, i < R → i0 < i → BlockELs (st i : ℤ) (ln i) (nx e) (rowMu C c e st i) := by
    intro i hi hcase
    apply rowEL_flatD g C c hC1 hC2 hrad hi
    intro j hj
    have := hright i hcase j; omega
  have hsum_of : ∀ i, i < R → BlockSums (st i : ℤ) (ln i) (nx e) := fun i hi => rowSum_of_memD g he hi
  have hstw := st_add_windowD g i1 Lw N hLw
  have hwin := fat_two_zero_s hLw2 (nx e) (fun k => rowMu C c e st (i1 + k)) (st i1 : ℤ) N hN
    (fun k hk => by
      have := hflat_of (i1 + k) (by omega) (by omega)
      rw [hstw k hk, hLw k hk] at this
      exact this)
    (fun k hk => by
      have := hsum_of (i1 + k) (by omega)
      rw [hstw k hk, hLw k hk] at this
      exact this)
    a b hab hbN ha hb
  have hz0 : StateZero (nx e) (st i1 : ℤ) := by
    have := hwin.2 0 (Nat.zero_le _)
    simpa using this
  exact hne (radical_zero_of_state g C c hC1 hC2 he hrad ha1 hia hC hL hc hnl hi1 (by omega) hz0)

theorem chain_poleD {R : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeomD n R a b st ln rowOf)
    {i0 K k r : ℕ} (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hia : a + 1 ≤ i0) (hi0b : i0 + b < R) (hC : st i0 = K + 1) (hL : ln i0 = k + 3)
    (hn : n = (K + 1) + (k + 3) + r)
    {i1 N Lw : ℕ} (hi1 : i0 < i1) (hN : 1 ≤ N) (hi1N : i1 + N + b < R) (hLw : ∀ j, j ≤ N → ln (i1 + j) = Lw) :
    ∃ cs : ℝ, cLoc (k + 2) < cs ∧ cs < 1 ∧ cs ≠ 0 ∧ ∃ es : Fin n → ℝ, es ∈ Vsub rowOf ∧ es ≠ 0 ∧
      qF (K + 1) cs es = 0 ∧ (∀ e : Fin n → ℝ, e ∈ Vsub rowOf → 0 ≤ qF (K + 1) cs e) ∧
      (∀ c : ℝ, cs < c → c ≤ 1 → ∀ e : Fin n → ℝ, e ∈ Vsub rowOf → e ≠ 0 → 0 < qF (K + 1) c e) ∧
      (∀ d : Fin n → ℝ, d ∈ Vsub rowOf → BF (K + 1) cs es d = 0) ∧
      (∀ e : Fin n → ℝ, e ∈ Vsub rowOf → qF (K + 1) cs e = 0 → ∃ t : ℝ, e = t • es) ∧
      ∀ a b : ℕ, a < b → b ≤ N → ¬ (rowMu (K + 1) cs es st (i1 + a) = 0 ∧ rowMu (K + 1) cs es st (i1 + b) = 0) := by
  have hi0 : i0 < R := by omega
  have hi0R : i0 + 1 < R := by omega
  have hC1 : 1 ≤ K + 1 := by omega
  have hC2 : K + 1 + 1 < n := by omega
  have he1 := e1vec_memD g hi0 hC hL hn
  have hneg : qF (K + 1) (cLoc (k + 2)) (e1vec (K + 1) (k + 3) n) < 0 := by
    have := qF_e1vec K k r (cLoc (k + 2))
    subst hn
    rw [this]
    exact locEnergy_neg k
  have hc1 : cLoc (k + 2) < 1 := lt_trans (cLoc_neg k) one_pos
  obtain ⟨cs, h1, h2, ⟨es, hes, hne, h0⟩, hpsd, hpos, hrad⟩ :=
    chain_crossing rowOf (K + 1) (cLoc (k + 2)) hc1 (e1vec (K + 1) (k + 3) n) he1 hneg
  have hcs0 : cs ≠ 0 := by
    intro hz
    rw [hz] at h0
    exact hne (qF_zero_eq_zeroD g (K + 1) hC1 hC2 (by omega) hi0R (by omega) hi0b hC hes h0)
  have hL3 : 3 ≤ ln i0 := by omega
  have hnl : ((ln i0 : ℝ) - 2) * ((ln i0 : ℝ) + 3) / 6 + 1 / cs ≠ 0 := by
    rw [hL]
    exact hnl_of_gt k cs h1 hcs0
  have hradEs := hrad es hes h0
  refine ⟨cs, h1, h2, hcs0, es, hes, hne, h0, hpsd, hpos, hradEs, ?_, ?_⟩
  · -- one-dimensional radical
    intro e he hq
    have hrade := hrad e he hq
    -- es has nx es 1 ≠ 0
    have hn1 : nx es (a : ℤ) ≠ 0 := by
      intro h
      exact hne (radical_zero_of_first g (K + 1) cs hC1 hC2 hes hradEs ha1 hia hi0b hC hL3 hcs0 hnl h)
    set t := nx e (a : ℤ) / nx es (a : ℤ) with ht
    have hd : e - t • es ∈ Vsub rowOf := (Vsub rowOf).sub_mem he ((Vsub rowOf).smul_mem t hes)
    have hradd : ∀ d : Fin n → ℝ, d ∈ Vsub rowOf → BF (K + 1) cs (e - t • es) d = 0 := by
      intro d hd'
      have : e - t • es = e + (-t) • es := by rw [neg_smul, sub_eq_add_neg]
      rw [this, BF_add_left, BF_smul_left, hrade d hd', hradEs d hd']; ring
    have h1' : nx (e - t • es) (a : ℤ) = 0 := by
      rw [nx_sub, nx_smul, ht]; field_simp; ring
    have := radical_zero_of_first g (K + 1) cs hC1 hC2 hd hradd ha1 hia hi0b hC hL3 hcs0 hnl h1'
    exact ⟨t, sub_eq_zero.mp this⟩
  · intro a b hab hbN ⟨ha, hb⟩
    exact chain_tailD g (K + 1) cs hC1 hC2 hes hne hradEs ha1 hia hC hL3 hcs0 hnl hi1 hN hi1N hLw hab hbN ha hb

#print axioms chain_tailD
#print axioms chain_poleD

end AdalyFormal.CoverOmega
