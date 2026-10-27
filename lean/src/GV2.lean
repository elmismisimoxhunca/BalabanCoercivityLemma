import GV1

/-!
# GV2 -- walks in coordinate boxes; flatness of flattened charts; transition growth (m2_glue3, 2026-10-15)

* `IBox lo hi` (product of integer intervals), `l1` (ℓ¹ distance, ℕ-valued).
* `bwalk_box` / `walk_box`: explicit walks of length `l1 p p'` between any two points of a box.
* `flat_bound`: a chart whose bonds at a base point are `1` has `|G(p,ν) − 1| ≤ l1(p, b) · t₂` on a box.
* `trans_box`: transitions move by at most `l1 · β₀` inside a box where both charts are `β₀/2`-flat.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2Glue3

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.M2Glue2
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

variable {L : PeriodicLatticeExtent}

def IBox (lo hi : Z3) : Set Z3 := {z | ∀ i, lo i ≤ z i ∧ z i ≤ hi i}

def l1 (p p' : Z3) : ℕ := (p 0 - p' 0).natAbs + (p 1 - p' 1).natAbs + (p 2 - p' 2).natAbs

theorem ev_sub_add (p : Z3) (i : Fin 3) : p - ev i + ev i = p := by
  funext j; simp only [Pi.add_apply, Pi.sub_apply]; ring

theorem exists_ne_of_l1 {p p' : Z3} {n : ℕ} (h : l1 p p' = n + 1) : ∃ i, p i ≠ p' i := by
  by_contra hc
  push Not at hc
  unfold l1 at h
  rw [hc 0, hc 1, hc 2] at h
  simp at h

theorem l1_sub_ev {p p' : Z3} {n : ℕ} {i : Fin 3} (h : l1 p p' = n + 1) (hi : p' i < p i) :
    l1 (p - ev i) p' = n := by
  unfold l1 at *
  fin_cases i <;> simp [ev] at hi ⊢ <;> omega

theorem l1_add_ev {p p' : Z3} {n : ℕ} {i : Fin 3} (h : l1 p p' = n + 1) (hi : p i < p' i) :
    l1 (p + ev i) p' = n := by
  unfold l1 at *
  fin_cases i <;> simp [ev] at hi ⊢ <;> omega

theorem sub_ev_mem {lo hi p p' : Z3} {i : Fin 3} (hp : p ∈ IBox lo hi) (hp' : p' ∈ IBox lo hi) (h : p' i < p i) :
    p - ev i ∈ IBox lo hi := by
  intro j
  have a := hp j; have b := hp' i
  simp only [Pi.sub_apply, ev]
  split_ifs with hj
  · subst hj; constructor <;> omega
  · simp only [sub_zero]; exact a

theorem add_ev_mem_box {lo hi p p' : Z3} {i : Fin 3} (hp : p ∈ IBox lo hi) (hp' : p' ∈ IBox lo hi) (h : p i < p' i) :
    p + ev i ∈ IBox lo hi := by
  intro j
  have a := hp j; have b := hp' i
  simp only [Pi.add_apply, ev]
  split_ifs with hj
  · subst hj; constructor <;> omega
  · simp only [add_zero]; exact a

/-- bond walks inside a box. -/
theorem bwalk_box (v : PeriodicLatticeSite L) {E : Set (PeriodicLatticeSite L)} {lo hi : Z3}
    (hE : ∀ z ∈ IBox lo hi, iota v z ∈ E) {p' : Z3} (hp' : p' ∈ IBox lo hi) :
    ∀ n : ℕ, ∀ p, p ∈ IBox lo hi → l1 p p' = n → BWalk E (iota v p') n (iota v p) := by
  intro n
  induction n with
  | zero =>
    intro p _ h
    have e : p = p' := by
      unfold l1 at h; funext j; fin_cases j <;> simp <;> omega
    rw [e]; exact BWalk.refl _
  | succ n ih =>
    intro p hp h
    obtain ⟨i, hne⟩ := exists_ne_of_l1 h
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- step down from p + e_i
      have hm := add_ev_mem_box hp hp' hlt
      have w := ih (p + ev i) hm (l1_add_ev h hlt)
      rw [← iota_shift] at w
      exact BWalk.bwd i w (hE p hp) (by rw [iota_shift]; exact hE _ hm)
    · have hm := sub_ev_mem hp hp' hgt
      have w := ih (p - ev i) hm (l1_sub_ev h hgt)
      have s := BWalk.fwd i w (hE _ hm) (by rw [iota_shift, ev_sub_add]; exact hE p hp)
      rw [iota_shift, ev_sub_add] at s
      exact s

/-- stencil walks inside a box. -/
theorem walk_box (v : PeriodicLatticeSite L) {D : Set (PeriodicLatticeSite L)} {ν : Fin 3} {lo hi : Z3}
    (hD : ∀ z i, z ∈ IBox lo hi → z + ev i ∈ IBox lo hi →
      iota v z ∈ D ∧ iota v (z + ev ν) ∈ D ∧ iota v (z + ev i) ∈ D ∧ iota v (z + ev i + ev ν) ∈ D)
    {p' : Z3} (hp' : p' ∈ IBox lo hi) :
    ∀ n : ℕ, ∀ p, p ∈ IBox lo hi → l1 p p' = n → Walk D ν (iota v p') n (iota v p) := by
  intro n
  induction n with
  | zero =>
    intro p _ h
    have e : p = p' := by
      unfold l1 at h; funext j; fin_cases j <;> simp <;> omega
    rw [e]; exact Walk.refl _
  | succ n ih =>
    intro p hp h
    obtain ⟨i, hne⟩ := exists_ne_of_l1 h
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hm := add_ev_mem_box hp hp' hlt
      have w := ih (p + ev i) hm (l1_add_ev h hlt)
      rw [← iota_shift] at w
      obtain ⟨d0, d1, d2, d3⟩ := hD p i hp hm
      exact Walk.bwd i w d0 (by rw [iota_shift]; exact d1) (by rw [iota_shift]; exact d2)
        (by rw [iota_shift2]; exact d3)
    · have hm := sub_ev_mem hp hp' hgt
      have w := ih (p - ev i) hm (l1_sub_ev h hgt)
      have hm' : p - ev i + ev i ∈ IBox lo hi := by rw [ev_sub_add]; exact hp
      obtain ⟨d0, d1, d2, d3⟩ := hD (p - ev i) i hm hm'
      have s := Walk.fwd i w d0 (by rw [iota_shift]; exact d1) (by rw [iota_shift]; exact d2)
        (by rw [iota_shift2]; exact d3)
      rw [iota_shift, ev_sub_add] at s
      exact s

/-- flatness: bond values grow at most linearly from a base point where they are `1`. -/
theorem flat_bound {v : PeriodicLatticeSite L} {U : LinkCfg L} {g : PeriodicLatticeSite L → SU2}
    {D : Set (PeriodicLatticeSite L)} {t1 t2 : ℝ} (hg : GChart U g D t1 t2) {ν : Fin 3} {lo hi b : Z3}
    (hD : ∀ z i, z ∈ IBox lo hi → z + ev i ∈ IBox lo hi →
      iota v z ∈ D ∧ iota v (z + ev ν) ∈ D ∧ iota v (z + ev i) ∈ D ∧ iota v (z + ev i + ev ν) ∈ D)
    (hb : b ∈ IBox lo hi) (hbase : periodicGaugeTransform g U (iota v b, ν) = 1)
    {p : Z3} (hp : p ∈ IBox lo hi) :
    frobNorm (((periodicGaugeTransform g U (iota v p, ν) : SU2) : M2) - 1) ≤ (l1 p b : ℝ) * t2 := by
  have w := walk_box v hD hb (l1 p b) p hp rfl
  have := bond_growth hg w
  rw [hbase] at this
  simpa using this

/-- transitions inside a box. -/
theorem trans_box {v : PeriodicLatticeSite L} {U : LinkCfg L} {gP gQ : PeriodicLatticeSite L → SU2} {Rb : ℕ}
    (hinj : Set.InjOn (iota v) (Box (Rb + 1))) {lo hi : Z3} (hbox : IBox lo hi ⊆ Box Rb) {β : ℝ}
    (hβ : ∀ z μ, z ∈ IBox lo hi → z + ev μ ∈ IBox lo hi →
      frobNorm (((periodicGaugeTransform gP U (iota v z, μ) : SU2) : M2) - 1)
        + frobNorm (((periodicGaugeTransform gQ U (iota v z, μ) : SU2) : M2) - 1) ≤ β)
    {p p' : Z3} (hp : p ∈ IBox lo hi) (hp' : p' ∈ IBox lo hi) :
    frobNorm (((trans gP gQ (iota v p) : SU2) : M2) - (trans gP gQ (iota v p') : M2)) ≤ (l1 p p' : ℝ) * β := by
  have w := bwalk_box v (E := lift v (IBox lo hi)) (fun z hz => iota_mem_lift hz) hp' (l1 p p') p hp rfl
  refine trans_growth (U := U) (β := fun _ => β) ?_ w β (fun _ _ => le_rfl)
  intro z μ hz hzμ
  obtain ⟨q, rfl, hq, hqμ⟩ := bond_lift hinj hbox hz hzμ
  exact hβ q μ hq hqμ

/-- `l1` against the real coordinates. -/
theorem l1_le (p b : Z3) : (l1 p b : ℝ) ≤ rho p + 3 / 2 + |(b 0 : ℝ)| + |(b 1 : ℝ)| + |(b 2 : ℝ)| := by
  have e : ∀ i, (((p i - b i).natAbs : ℕ) : ℝ) ≤ |qc p i| + 1 / 2 + |(b i : ℝ)| := by
    intro i
    have : (((p i - b i).natAbs : ℕ) : ℝ) = |(p i : ℝ) - b i| := by
      rw [Nat.cast_natAbs, Int.cast_abs]; push_cast; rfl
    rw [this]
    unfold qc
    have h1 := abs_sub ((p i : ℝ) + 1 / 2) (b i : ℝ)
    have h2 : (p i : ℝ) - b i = ((p i : ℝ) + 1 / 2) - b i - 1 / 2 := by ring
    rw [h2]
    have h3 := abs_sub (((p i : ℝ) + 1 / 2) - b i) (1 / 2 : ℝ)
    have h4 : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
    linarith
  unfold l1 rho
  simp only [Nat.cast_add]
  linarith [e 0, e 1, e 2]

end AdalyFormal.M2Glue3
