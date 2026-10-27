import DLR28

/-!
# DL29 -- the geometry of the jet footprint: reach (oscillation of the weight) and multiplicity (overlap count)

* `Reach m x z` : `z` is reached from `x` by at most `m` positive unit steps.  `Reach_lip` : `|φ z − φ x| ≤ m θ'` (`WtLip θ' φ`).
* `OnPath_reach`, `endpoint_reach`, `gamma_len_le` (staircase of a strided block has `≤ 3(ℓ−1)` coarse steps),
  **`VisStep_reach`** : every edge read by the one-step map at stride `s` is based within `(3(ℓ−1)+ℓ)s` positive steps of `c₀`;
  `Rfoot`, **`Foot_reach`**, **`Rfoot_le`** : `Rfoot ℓ k ≤ 5 ℓ^k` (`ℓ ≥ 2`).
* `Reach_disp` : `Reach m y z → (z_ν − y_ν).val ≤ m` (cyclic difference).
* **`card_reach_coarse_le`** : for `n ∣ L_ν + 1`, at most `(m/n + 1)³` sites `y` on the `n`-lattice reach a given `z` in `m` steps
  (injection `y ↦ ((z_ν − y_ν).val / n)_ν`; the residue mod `n` is fixed by `z`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.TowerLawCov (coarsePathEndpoint coarseGammaPath)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)

variable {L : PeriodicLatticeExtent}

/-- `z` is reached from `x` by at most `m` positive unit steps -/
def Reach (m : ℕ) (x z : PeriodicLatticeSite L) : Prop :=
  ∃ l : List (Fin 3), l.length ≤ m ∧ z = l.foldl (fun w μ => periodicLatticeShift w μ) x

theorem Reach_refl (x : PeriodicLatticeSite L) : Reach 0 x x := ⟨[], le_rfl, rfl⟩

theorem Reach_mono {m m' : ℕ} (h : m ≤ m') {x z : PeriodicLatticeSite L} (hr : Reach m x z) : Reach m' x z := by
  obtain ⟨l, hl, hz⟩ := hr
  exact ⟨l, hl.trans h, hz⟩

theorem Reach_trans {m m' : ℕ} {x y z : PeriodicLatticeSite L} (h1 : Reach m x y) (h2 : Reach m' y z) :
    Reach (m + m') x z := by
  obtain ⟨l1, hl1, rfl⟩ := h1
  obtain ⟨l2, hl2, rfl⟩ := h2
  exact ⟨l1 ++ l2, by rw [List.length_append]; omega, by rw [List.foldl_append]⟩

theorem iterate_shift_foldl (μ : Fin 3) : ∀ (s : ℕ) (x : PeriodicLatticeSite L),
    (fun z => periodicLatticeShift z μ)^[s] x = (List.replicate s μ).foldl (fun w ν => periodicLatticeShift w ν) x
  | 0, _ => rfl
  | s + 1, x => by
      rw [Function.iterate_succ_apply, List.replicate_succ, List.foldl_cons]
      exact iterate_shift_foldl μ s _

theorem Reach_coarseShift (s : ℕ) (x : PeriodicLatticeSite L) (μ : Fin 3) : Reach s x (coarseShift x s μ) :=
  ⟨List.replicate s μ, by simp, iterate_shift_foldl μ s x⟩

theorem Reach_lip (θ' : ℝ) (φ : PeriodicLatticeSite L → ℝ) (hφ : WtLip θ' φ) {m : ℕ} {x z : PeriodicLatticeSite L}
    (h : Reach m x z) : |φ z - φ x| ≤ m * θ' := by
  have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ x 0)
  obtain ⟨l, hl, rfl⟩ := h
  have key : ∀ (l : List (Fin 3)) (x : PeriodicLatticeSite L),
      |φ (l.foldl (fun w μ => periodicLatticeShift w μ) x) - φ x| ≤ l.length * θ' := by
    intro l
    induction l with
    | nil => intro x; simp
    | cons μ rest ih =>
        intro x
        rw [List.foldl_cons, List.length_cons]
        have h1 := ih (periodicLatticeShift x μ)
        have h2 := hφ x μ
        calc |φ (rest.foldl (fun w μ => periodicLatticeShift w μ) (periodicLatticeShift x μ)) - φ x|
            ≤ |φ (rest.foldl (fun w μ => periodicLatticeShift w μ) (periodicLatticeShift x μ))
                - φ (periodicLatticeShift x μ)| + |φ (periodicLatticeShift x μ) - φ x| := abs_sub_le _ _ _
          _ ≤ rest.length * θ' + θ' := add_le_add h1 h2
          _ = ((rest.length + 1 : ℕ) : ℝ) * θ' := by push_cast; ring
  calc _ ≤ l.length * θ' := key l x
    _ ≤ m * θ' := mul_le_mul_of_nonneg_right (by exact_mod_cast hl) hθ

theorem OnPath_reach (s : ℕ) : ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L) (e : PeriodicLatticeEdge L),
    OnPath s y p e → Reach (s * p.length) y e.1
  | [], _, _, h => h.elim
  | μ :: rest, y, e, h => by
      rcases h with h | h
      · rw [h]; exact Reach_mono (Nat.zero_le _) (Reach_refl y)
      · have := Reach_trans (Reach_coarseShift s y μ) (OnPath_reach s rest _ e h)
        exact Reach_mono (by rw [List.length_cons, Nat.mul_succ]; omega) this

theorem endpoint_reach (s : ℕ) : ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L),
    Reach (s * p.length) y (coarsePathEndpoint s y p)
  | [], y => Reach_refl y
  | μ :: rest, y => by
      have := Reach_trans (Reach_coarseShift s y μ) (endpoint_reach s rest (coarseShift y s μ))
      exact Reach_mono (by rw [List.length_cons, Nat.mul_succ]; omega) this

theorem steps_le (s ell : ℕ) (hs : 0 < s) (a b : PeriodicLatticeSite L) (μ : Fin 3)
    (h1 : (a μ).val ≤ (b μ).val) (h2 : (b μ).val < (a μ).val + s * ell) :
    (b μ - a μ).val / s ≤ ell - 1 := by
  rw [Fin.sub_val_of_le (Fin.le_def.mpr h1)]
  have h3 : (b μ).val - (a μ).val < s * ell := by omega
  have h4 : ((b μ).val - (a μ).val) / s < ell := by
    rw [Nat.div_lt_iff_lt_mul hs]; linarith [mul_comm s ell]
  omega

theorem gamma_len_le (s ell : ℕ) (hs : 0 < s) (y x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf y s ell) :
    (coarseGammaPath s y x).length ≤ 3 * (ell - 1) := by
  rw [mem_stepBlockOf] at hx
  unfold coarseGammaPath AdalyFormal.Balaban.TowerLawCov.coarseStraightSegment
    AdalyFormal.Balaban.TowerLawCov.coarseCoordSteps
  simp only [List.length_append, List.length_replicate]
  have hy1 : (Function.update y 2 (x 2) : PeriodicLatticeSite L) 1 = y 1 :=
    Function.update_of_ne (by decide) _ _
  have hy0 : (Function.update (Function.update y 2 (x 2)) 1 (x 1) : PeriodicLatticeSite L) 0 = y 0 := by
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
  rw [hy1, hy0]
  have a2 := steps_le s ell hs y x 2 (hx 2).1 (hx 2).2.1
  have a1 := steps_le s ell hs y x 1 (hx 1).1 (hx 1).2.1
  have a0 := steps_le s ell hs y x 0 (hx 0).1 (hx 0).2.1
  omega

theorem block_reach (s ell : ℕ) (hs : 0 < s) (y x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf y s ell) :
    Reach (3 * (ell - 1) * s) y x := by
  have hx' := (mem_stepBlockOf.mp hx)
  have he := AdalyFormal.Balaban.QjComposite.coarsePathEndpoint_coarseGammaPath
    (s := s) (y := y) (x := x) (fun μ => ⟨(hx' μ).1, (hx' μ).2.2⟩)
  have h := endpoint_reach s (coarseGammaPath s y x) y
  rw [he] at h
  exact Reach_mono (by
    have := gamma_len_le s ell hs y x hx
    calc s * (coarseGammaPath s y x).length ≤ s * (3 * (ell - 1)) := Nat.mul_le_mul_left s this
      _ = 3 * (ell - 1) * s := by ring) h

/-- the one-step reach radius -/
def Rstep (ell s : ℕ) : ℕ := (3 * (ell - 1) + ell) * s

theorem VisStep_reach (s ell : ℕ) (hs : 0 < s) (c e : PeriodicLatticeEdge L) (h : VisStep s ell c e) :
    Reach (Rstep ell s) c.1 e.1 := by
  have hcp : Reach (s * ell) c.1 (cPlusS s ell c) := by
    rw [AdalyFormal.Balaban.UbarTowerCov.cPlusS_eq]; exact Reach_coarseShift (s * ell) c.1 c.2
  unfold Rstep
  rcases h with ⟨x, hx, he⟩ | ⟨x, hx, he⟩ | ⟨x, hx, he⟩ | ⟨x, hx, he⟩ | he
  · have h1 := OnPath_reach s _ c.1 e he
    have hl := gamma_len_le s ell hs c.1 x hx
    exact Reach_mono (by nlinarith [Nat.mul_le_mul_left s hl]) h1
  · have h1 := OnPath_reach s _ (cPlusS s ell c) e he
    have hl := gamma_len_le s ell hs (cPlusS s ell c) x hx
    exact Reach_mono (by nlinarith [Nat.mul_le_mul_left s hl]) (Reach_trans hcp h1)
  · have h0 := block_reach s ell hs c.1 x hx
    have h1 := OnPath_reach s _ x e he
    rw [List.length_replicate] at h1
    exact Reach_mono (by nlinarith) (Reach_trans h0 h1)
  · have h1 := OnPath_reach s _ (cPlusS s ell c) e he
    have hl := gamma_len_le s ell hs c.1 x hx
    exact Reach_mono (by nlinarith [Nat.mul_le_mul_left s hl]) (Reach_trans hcp h1)
  · have h1 := OnPath_reach s _ c.1 e he
    rw [List.length_replicate] at h1
    exact Reach_mono (by nlinarith) h1

/-- the footprint radius -/
def Rfoot (ell : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => Rstep ell (ell ^ j) + Rfoot ell j

theorem Foot_reach (ell : ℕ) (hell : 0 < ell) : ∀ (j : ℕ) (c e : PeriodicLatticeEdge L),
    Foot ell j c e → Reach (Rfoot ell j) c.1 e.1
  | 0, c, e, h => by
      have h' : e = c := h
      rw [h']; exact Reach_refl c.1
  | j + 1, c, e, h => by
      obtain ⟨e', hv, hf⟩ := h
      exact Reach_trans (VisStep_reach (ell ^ j) ell (pow_pos hell j) c e' hv) (Foot_reach ell hell j e' e hf)

theorem Rfoot_le (ell : ℕ) (hell : 2 ≤ ell) : ∀ j, Rfoot ell j ≤ 5 * ell ^ j
  | 0 => by simp [Rfoot]
  | j + 1 => by
      have ih := Rfoot_le ell hell j
      show (3 * (ell - 1) + ell) * ell ^ j + Rfoot ell j ≤ 5 * ell ^ (j + 1)
      rw [pow_succ]
      have h1 : 3 * (ell - 1) + ell + 5 ≤ 5 * ell := by omega
      nlinarith [Nat.mul_le_mul_right (ell ^ j) h1]

/-! ## displacement and the overlap count -/

theorem shift_disp (x : PeriodicLatticeSite L) (μ ν : Fin 3) : ((periodicLatticeShift x μ) ν - x ν).val ≤ 1 := by
  by_cases h : ν = μ
  · subst h
    simp only [periodicLatticeShift, Function.update_self, add_sub_cancel_left]
    rw [Fin.val_one']
    exact Nat.mod_le _ _
  · simp only [periodicLatticeShift, Function.update_of_ne h, sub_self, Fin.val_zero, zero_le]

theorem Reach_disp {m : ℕ} {y z : PeriodicLatticeSite L} (h : Reach m y z) (ν : Fin 3) : (z ν - y ν).val ≤ m := by
  obtain ⟨l, hl, rfl⟩ := h
  have key : ∀ (l : List (Fin 3)) (x : PeriodicLatticeSite L),
      ((l.foldl (fun w μ => periodicLatticeShift w μ) x) ν - x ν).val ≤ l.length := by
    intro l
    induction l with
    | nil => intro x; simp
    | cons μ rest ih =>
        intro x
        rw [List.foldl_cons, List.length_cons]
        have h1 := ih (periodicLatticeShift x μ)
        have h2 := shift_disp x μ ν
        have e : (rest.foldl (fun w μ => periodicLatticeShift w μ) (periodicLatticeShift x μ)) ν - x ν
            = ((rest.foldl (fun w μ => periodicLatticeShift w μ) (periodicLatticeShift x μ)) ν
                - (periodicLatticeShift x μ) ν) + ((periodicLatticeShift x μ) ν - x ν) := by
          rw [sub_add_sub_cancel]
        rw [e, Fin.val_add]
        exact (Nat.mod_le _ _).trans (by omega)
  exact (key l y).trans hl

theorem sub_val_mod (n : ℕ) {N : ℕ} (hN : n ∣ N) (a b : Fin N) (hb : n ∣ b.val) : (a - b).val % n = a.val % n := by
  rw [Fin.val_sub, Nat.mod_mod_of_dvd _ hN]
  have h1 : n ∣ N - b.val := Nat.dvd_sub hN hb
  obtain ⟨t, ht⟩ := h1
  rw [ht, Nat.add_comm, Nat.add_mul_mod_self_left]

open Classical in
theorem card_reach_coarse_le (n : ℕ) (hn : 0 < n) (hdvd : ∀ ν : Fin 3, n ∣ L ν + 1) (m : ℕ) (z : PeriodicLatticeSite L) :
    (Finset.univ.filter (fun y : PeriodicLatticeSite L => (∀ ν, n ∣ (y ν).val) ∧ Reach m y z)).card ≤ (m / n + 1) ^ 3 := by
  have hcard : (Finset.univ : Finset (Fin 3 → Fin (m / n + 1))).card = (m / n + 1) ^ 3 := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn
    (fun y : PeriodicLatticeSite L => fun ν : Fin 3 =>
      (⟨min ((z ν - y ν).val / n) (m / n), Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (m / n + 1))) ?_ ?_
  · intro y _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
  · intro y hy y' hy' hyy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hy hy'
    funext ν
    have h1 := congrFun hyy ν
    simp only [Fin.mk.injEq] at h1
    have hm1 : (z ν - y ν).val / n ≤ m / n := Nat.div_le_div_right (Reach_disp hy.2 ν)
    have hm2 : (z ν - y' ν).val / n ≤ m / n := Nat.div_le_div_right (Reach_disp hy'.2 ν)
    rw [min_eq_left hm1, min_eq_left hm2] at h1
    have h2 : (z ν - y ν).val % n = (z ν - y' ν).val % n := by
      rw [sub_val_mod n (hdvd ν) _ _ (hy.1 ν), sub_val_mod n (hdvd ν) _ _ (hy'.1 ν)]
    have h3 : (z ν - y ν).val = (z ν - y' ν).val := by
      rw [← Nat.div_add_mod (z ν - y ν).val n, ← Nat.div_add_mod (z ν - y' ν).val n, h1, h2]
    have h4 : z ν - y ν = z ν - y' ν := Fin.ext h3
    exact sub_right_injective h4

#print axioms Reach_mono
#print axioms Reach_trans
#print axioms Reach_coarseShift
#print axioms Reach_lip
#print axioms OnPath_reach
#print axioms endpoint_reach
#print axioms gamma_len_le
#print axioms block_reach
#print axioms VisStep_reach
#print axioms Foot_reach
#print axioms Rfoot_le
#print axioms shift_disp
#print axioms Reach_disp
#print axioms sub_val_mod
#print axioms card_reach_coarse_le

end AdalyFormal.DLayer
