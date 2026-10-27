import UZ1

/-!
# UZ2 -- clause-1 chart on the `ℓ¹` ball from cell charts, by stacking (lane unif_20261016)

Cells of side `s` with offset `o`: `cellZ s o p μ = (p μ + o μ) / s` (floor division).
`stack_interval` : for a set `F` that does not constrain coordinate `μ` (`Cyl μ F`), charts (constant `t`) on every
piece `Bz r ∩ F ∩ {cell_μ = i}` and holonomy bound `η` on `Bz r` give a chart on `Bz r ∩ F ∩ {z - m' ≤ cell_μ ≤ z + m}`
(`z` = cell of the origin) with constant `t + (m + m')(2t + η)`.
`ball_chart1` : cell charts on every `Bz r ∩ cell` give a chart on the whole `Bz r` (three nested intervals: x, then y, then z),
with an explicit constant depending only on `t`, `η` and the cell count `n` with `r ≤ n s`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.UnifLane.Z

open AdalyFormal.M2Glue3 (Z3 ev)
open AdalyFormal.M2BallCharts (Bz)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

/-- cell index along `μ`. -/
def cellZ (s : ℤ) (o p : Z3) (μ : Fin 3) : ℤ := (p μ + o μ) / s

/-- `F` does not constrain coordinate `μ`. -/
def Cyl (μ : Fin 3) (F : Set Z3) : Prop := ∀ p q : Z3, (∀ ν, ν ≠ μ → p ν = q ν) → (p ∈ F ↔ q ∈ F)

/-- the holonomy bound on the ball. -/
def HolB (W : Z3 → Fin 3 → SU2) (D : Set Z3) (η : ℝ) : Prop :=
  ∀ q μ ν, q ∈ D → q + ev μ ∈ D → q + ev ν ∈ D → q + ev μ + ev ν ∈ D → frobNorm (((hol W q μ ν : SU2) : M2) - 1) ≤ η

theorem ev_apply_self (μ : Fin 3) : ev μ μ = 1 := by simp [ev]
theorem ev_apply_ne {μ ν : Fin 3} (h : ν ≠ μ) : ev μ ν = 0 := by simp [ev, h]

theorem cellZ_add_ev_ne {s : ℤ} {o p : Z3} {μ ν : Fin 3} (h : ν ≠ μ) : cellZ s o (p + ev ν) μ = cellZ s o p μ := by
  simp [cellZ, ev_apply_ne (Ne.symm h)]

theorem div_eq_iff' {a k s : ℤ} (hs : 0 < s) : a / s = k ↔ k * s ≤ a ∧ a < k * s + s := by
  constructor
  · rintro rfl
    refine ⟨Int.ediv_mul_le a hs.ne', ?_⟩
    have := Int.lt_ediv_add_one_mul_self a hs
    linarith
  · rintro ⟨h1, h2⟩
    have a1 : k ≤ a / s := (Int.le_ediv_iff_mul_le hs).mpr h1
    have a2 : a / s < k + 1 := (Int.ediv_lt_iff_lt_mul hs).mpr (by linarith)
    omega

theorem div_mono' {a b s : ℤ} (hs : 0 < s) (h : a ≤ b) : a / s ≤ b / s := Int.ediv_le_ediv hs h

/-- the update of one coordinate. -/
def setc (p : Z3) (μ : Fin 3) (c : ℤ) : Z3 := Function.update p μ c

theorem setc_self (p : Z3) (μ : Fin 3) (c : ℤ) : setc p μ c μ = c := by simp [setc]
theorem setc_ne (p : Z3) {μ ν : Fin 3} (c : ℤ) (h : ν ≠ μ) : setc p μ c ν = p ν := by simp [setc, h]

theorem setc_add_self (p : Z3) (μ : Fin 3) (c : ℤ) : setc (p + ev μ) μ c = setc p μ c := by
  funext ν; by_cases h : ν = μ
  · subst h; simp [setc]
  · simp [setc, h, ev_apply_ne h]

theorem setc_add_ne (p : Z3) {μ ν : Fin 3} (c : ℤ) (h : ν ≠ μ) : setc (p + ev ν) μ c = setc p μ c + ev ν := by
  funext κ; by_cases hk : κ = μ
  · subst hk; simp [setc, ev_apply_ne (Ne.symm h)]
  · simp [setc, hk]

theorem setc_eq_self (p : Z3) (μ : Fin 3) : setc p μ (p μ) = p := by simp [setc]

theorem Bz_setc {r : ℕ} {p : Z3} (hp : p ∈ Bz r) (μ : Fin 3) {c : ℤ} (hc : c.natAbs ≤ (p μ).natAbs) : setc p μ c ∈ Bz r := by
  have h : ∀ ν, (setc p μ c ν).natAbs ≤ (p ν).natAbs := by
    intro ν
    by_cases hν : ν = μ
    · subst hν; rw [setc_self]; exact hc
    · rw [setc_ne _ _ hν]
  simp only [Bz, Set.mem_setOf_eq] at hp ⊢
  have := h 0; have := h 1; have := h 2
  omega

theorem natAbs_le_of {a c : ℤ} (h0 : 0 ≤ c) (h1 : c ≤ a) : c.natAbs ≤ a.natAbs := by omega
theorem natAbs_le_of' {a c : ℤ} (h0 : c ≤ 0) (h1 : a ≤ c) : c.natAbs ≤ a.natAbs := by omega

theorem cyl_setc {μ : Fin 3} {F : Set Z3} (hF : Cyl μ F) {p : Z3} (hp : p ∈ F) (c : ℤ) : setc p μ c ∈ F :=
  (hF p _ (fun ν h => (setc_ne p c h).symm)).mp hp

/-- the range region and the cell pieces. -/
def Rg (s : ℤ) (o : Z3) (r : ℕ) (μ : Fin 3) (F : Set Z3) (a b : ℤ) : Set Z3 :=
  {p | p ∈ Bz r ∧ p ∈ F ∧ a ≤ cellZ s o p μ ∧ cellZ s o p μ ≤ b}

def Pc (s : ℤ) (o : Z3) (r : ℕ) (μ : Fin 3) (F : Set Z3) (i : ℤ) : Set Z3 :=
  {p | p ∈ Bz r ∧ p ∈ F ∧ cellZ s o p μ = i}

theorem cell_mono_ev {s : ℤ} (hs : 0 < s) (o p : Z3) (ν : Fin 3) : cellZ s o p ν ≤ cellZ s o (p + ev ν) ν := by
  unfold cellZ; apply div_mono' hs; simp [ev_apply_self]

theorem cell_succ_le {s : ℤ} (hs : 0 < s) (o p : Z3) (ν : Fin 3) : cellZ s o (p + ev ν) ν ≤ cellZ s o p ν + 1 := by
  have h1 := (div_eq_iff' hs).mp (rfl : cellZ s o p ν = cellZ s o p ν)
  have h2 : (p + ev ν) ν + o ν < (cellZ s o p ν + 1) * s + s := by
    simp only [Pi.add_apply, ev_apply_self]; nlinarith
  have := (Int.ediv_lt_iff_lt_mul hs).mpr (show (p + ev ν) ν + o ν < (cellZ s o p ν + 1 + 1) * s by linarith)
  show ((p + ev ν) ν + o ν) / s ≤ cellZ s o p ν + 1
  omega

theorem step_right (W : Z3 → Fin 3 → SU2) {s : ℤ} (hs : 0 < s) (o : Z3) (r : ℕ) (μ : Fin 3) {F : Set Z3}
    (hF : Cyl μ F) {t tO η : ℝ} (ht : 0 ≤ t) (htO : 0 ≤ tO) (hη : 0 ≤ η) (hhol : HolB W (Bz r) η)
    {a b : ℤ} (hab : a ≤ b) (hzb : o μ / s ≤ b) {Go Gn : Z3 → SU2}
    (hGo : C1 W Go (Rg s o r μ F a b) tO) (hGn : C1 W Gn (Pc s o r μ F (b + 1)) t) :
    ∃ G, C1 W G (Rg s o r μ F a (b + 1)) (tO + 2 * t + η) := by
  set z : ℤ := o μ / s with hz
  have hzhi : o μ < z * s + s := ((div_eq_iff' hs).mp hz.symm).2
  set pl : ℤ := (b + 1) * s - o μ with hpl
  have hpl1 : 1 ≤ pl := by nlinarith
  set O := Rg s o r μ F a b with hO
  set N := Pc s o r μ F (b + 1) with hN
  have hbN : ∀ p ∈ N, setc p μ pl ∈ N := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hp
    have hc := (div_eq_iff' hs).mp h3
    refine ⟨Bz_setc h1 μ (natAbs_le_of (by omega) (by linarith)), cyl_setc hF h2 pl, ?_⟩
    show (setc p μ pl μ + o μ) / s = b + 1
    rw [setc_self, div_eq_iff' hs]; constructor <;> linarith
  have hbO : ∀ p ∈ N, setc p μ pl - ev μ ∈ O := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hp
    have hc := (div_eq_iff' hs).mp h3
    have e : setc p μ pl - ev μ = setc p μ (pl - 1) := by
      funext κ; by_cases hk : κ = μ
      · subst hk; simp [setc, ev_apply_self]
      · simp [setc, hk, ev_apply_ne hk]
    rw [e]
    have hcell : cellZ s o (setc p μ (pl - 1)) μ = b := by
      show (setc p μ (pl - 1) μ + o μ) / s = b
      rw [setc_self, div_eq_iff' hs]; constructor <;> nlinarith
    exact ⟨Bz_setc h1 μ (natAbs_le_of (by omega) (by linarith)), cyl_setc hF h2 _, by rw [hcell]; exact hab,
      by rw [hcell]⟩
  have hcross : ∀ p ∈ O, ∀ ν, p + ev ν ∈ N → ν = μ ∧ setc (p + ev μ) μ pl = p + ev μ := by
    intro p hp ν hpν
    obtain ⟨_, _, _, h4⟩ := hp
    obtain ⟨_, _, h7⟩ := hpν
    by_cases hνμ : ν = μ
    · subst hνμ
      refine ⟨rfl, ?_⟩
      have hc' := (div_eq_iff' hs).mp h7
      have hlt : p ν + o ν < (b + 1) * s := by
        by_contra hh; push_neg at hh
        have := (Int.le_ediv_iff_mul_le hs).mpr hh
        have h4' : (p ν + o ν) / s ≤ b := h4
        omega
      have hpv : (p + ev ν) ν = pl := by
        simp only [Pi.add_apply, ev_apply_self] at hc' ⊢
        rw [hpl]; linarith
      conv_rhs => rw [← setc_eq_self (p + ev ν) ν, hpv]
    · exfalso
      rw [cellZ_add_ev_ne hνμ] at h7
      omega
  have hno : ∀ p ∈ N, ∀ ν, p + ev ν ∈ O → False := by
    intro p hp ν hpν
    obtain ⟨_, _, h3⟩ := hp
    obtain ⟨_, _, _, h7⟩ := hpν
    by_cases hνμ : ν = μ
    · subst hνμ
      have := cell_mono_ev hs o p ν
      omega
    · rw [cellZ_add_ev_ne hνμ] at h7; omega
  have hdisj : ∀ p ∈ N, p ∉ O := by
    intro p hp hpO
    obtain ⟨_, _, h3⟩ := hp
    obtain ⟨_, _, _, h7⟩ := hpO
    omega
  obtain ⟨G, hG, -⟩ := stackP W μ htO ht hη hGo hGn (fun p => setc p μ pl) hbN hbO
    (fun p _ _ => setc_add_self p μ pl) (fun p _ ν hν _ => setc_add_ne p pl hν) hcross hno hdisj
    (fun q hq ν _ h1 h2 h3 => hhol q ν μ hq.1 h1.1 h2.1 (add_right_comm q (ev μ) (ev ν) ▸ h3.1))
  refine ⟨G, hG.mono (fun p hp => ?_) le_rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := hp
  by_cases hc : cellZ s o p μ ≤ b
  · exact Or.inl ⟨h1, h2, h3, hc⟩
  · exact Or.inr ⟨h1, h2, by omega⟩

theorem step_left (W : Z3 → Fin 3 → SU2) {s : ℤ} (hs : 0 < s) (o : Z3) (r : ℕ) (μ : Fin 3) {F : Set Z3}
    (hF : Cyl μ F) {t tO η : ℝ} (ht : 0 ≤ t) (htO : 0 ≤ tO) (hη : 0 ≤ η) (hhol : HolB W (Bz r) η)
    {a b : ℤ} (hab : a ≤ b) (hza : a ≤ o μ / s) {Go Gn : Z3 → SU2}
    (hGo : C1 W Go (Rg s o r μ F a b) tO) (hGn : C1 W Gn (Pc s o r μ F (a - 1)) t) :
    ∃ G, C1 W G (Rg s o r μ F (a - 1) b) (tO + 2 * t + η) := by
  set z : ℤ := o μ / s with hz
  have hzlo : z * s ≤ o μ := ((div_eq_iff' hs).mp hz.symm).1
  set pl : ℤ := a * s - o μ - 1 with hpl
  have hpl1 : pl ≤ -1 := by nlinarith
  set O := Rg s o r μ F a b with hO
  set N := Pc s o r μ F (a - 1) with hN
  have hbN : ∀ p ∈ N, setc p μ pl ∈ N := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hp
    have hc := (div_eq_iff' hs).mp h3
    refine ⟨Bz_setc h1 μ (natAbs_le_of' (by omega) (by nlinarith)), cyl_setc hF h2 pl, ?_⟩
    show (setc p μ pl μ + o μ) / s = a - 1
    rw [setc_self, div_eq_iff' hs]; constructor <;> nlinarith
  have hbO : ∀ p ∈ N, setc p μ pl + ev μ ∈ O := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hp
    have hc := (div_eq_iff' hs).mp h3
    have e : setc p μ pl + ev μ = setc p μ (pl + 1) := by
      funext κ; by_cases hk : κ = μ
      · subst hk; simp [setc, ev_apply_self]
      · simp [setc, hk, ev_apply_ne hk]
    rw [e]
    have hcell : cellZ s o (setc p μ (pl + 1)) μ = a := by
      show (setc p μ (pl + 1) μ + o μ) / s = a
      rw [setc_self, div_eq_iff' hs]; constructor <;> nlinarith
    exact ⟨Bz_setc h1 μ (natAbs_le_of' (by omega) (by nlinarith)), cyl_setc hF h2 _, by rw [hcell],
      by rw [hcell]; exact hab⟩
  have hcross : ∀ p ∈ N, ∀ ν, p + ev ν ∈ O → ν = μ ∧ setc p μ pl = p := by
    intro p hp ν hpν
    obtain ⟨_, _, h3⟩ := hp
    obtain ⟨_, _, h6, _⟩ := hpν
    by_cases hνμ : ν = μ
    · subst hνμ
      refine ⟨rfl, ?_⟩
      have hc := (div_eq_iff' hs).mp h3
      have hge : a * s ≤ (p + ev ν) ν + o ν := (Int.le_ediv_iff_mul_le hs).mp h6
      have hpv : p ν = pl := by
        simp only [Pi.add_apply, ev_apply_self] at hge
        rw [hpl]; nlinarith
      rw [← hpv, setc_eq_self]
    · exfalso
      rw [cellZ_add_ev_ne hνμ] at h6
      omega
  have hno : ∀ p ∈ O, ∀ ν, p + ev ν ∈ N → False := by
    intro p hp ν hpν
    obtain ⟨_, _, h3, _⟩ := hp
    obtain ⟨_, _, h7⟩ := hpν
    by_cases hνμ : ν = μ
    · subst hνμ
      have := cell_mono_ev hs o p ν
      omega
    · rw [cellZ_add_ev_ne hνμ] at h7; omega
  have hdisj : ∀ p ∈ N, p ∉ O := by
    intro p hp hpO
    obtain ⟨_, _, h3⟩ := hp
    obtain ⟨_, _, h6, _⟩ := hpO
    omega
  obtain ⟨G, hG, -⟩ := stackM W μ htO ht hη hGo hGn (fun p => setc p μ pl) hbN hbO
    (fun p _ _ => setc_add_self p μ pl) (fun p _ ν hν _ => setc_add_ne p pl hν) hcross hno hdisj
    (fun B hB ν _ h1 h2 h3 => hhol B ν μ hB.1 h1.1 h2.1 h3.1)
  refine ⟨G, hG.mono (fun p hp => ?_) le_rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := hp
  by_cases hc : a ≤ cellZ s o p μ
  · exact Or.inl ⟨h1, h2, hc, h4⟩
  · exact Or.inr ⟨h1, h2, by omega⟩

/-- **interval stacking along `μ`.** -/
theorem stack_interval (W : Z3 → Fin 3 → SU2) {s : ℤ} (hs : 0 < s) (o : Z3) (r : ℕ) (μ : Fin 3) {F : Set Z3}
    (hF : Cyl μ F) {t η : ℝ} (ht : 0 ≤ t) (hη : 0 ≤ η) (hhol : HolB W (Bz r) η)
    (hpc : ∀ i : ℤ, ∃ G, C1 W G (Pc s o r μ F i) t) :
    ∀ m m' : ℕ, ∃ G, C1 W G (Rg s o r μ F (o μ / s - m') (o μ / s + m)) (t + ((m : ℝ) + m') * (2 * t + η)) := by
  have right : ∀ m : ℕ, ∃ G, C1 W G (Rg s o r μ F (o μ / s) (o μ / s + m)) (t + (m : ℝ) * (2 * t + η)) := by
    intro m
    induction m with
    | zero =>
      obtain ⟨G, hG⟩ := hpc (o μ / s)
      exact ⟨G, hG.mono (fun p hp => ⟨hp.1, hp.2.1, by have := hp.2.2; simp at this ⊢; omega⟩) (by simp)⟩
    | succ m ih =>
      obtain ⟨Go, hGo⟩ := ih
      obtain ⟨Gn, hGn⟩ := hpc (o μ / s + m + 1)
      have h0 : 0 ≤ t + (m : ℝ) * (2 * t + η) := by positivity
      obtain ⟨G, hG⟩ := step_right W hs o r μ hF ht h0 hη hhol (a := o μ / s) (b := o μ / s + m) (by omega) (by omega)
        hGo hGn
      refine ⟨G, ?_⟩
      have e : o μ / s + ((m + 1 : ℕ) : ℤ) = o μ / s + m + 1 := by push_cast; ring
      rw [e]; exact hG.mono le_rfl.subset (by push_cast; linarith)
  intro m m'
  induction m' with
  | zero =>
    obtain ⟨G, hG⟩ := right m
    exact ⟨G, by simpa using hG⟩
  | succ m' ih =>
    obtain ⟨Go, hGo⟩ := ih
    obtain ⟨Gn, hGn⟩ := hpc (o μ / s - m' - 1)
    have h0 : 0 ≤ t + ((m : ℝ) + m') * (2 * t + η) := by positivity
    obtain ⟨G, hG⟩ := step_left W hs o r μ hF ht h0 hη hhol (a := o μ / s - m') (b := o μ / s + m) (by omega) (by omega)
      hGo hGn
    refine ⟨G, ?_⟩
    have e : o μ / s - ((m' + 1 : ℕ) : ℤ) = o μ / s - m' - 1 := by push_cast; ring
    rw [e]; exact hG.mono le_rfl.subset (by push_cast; linarith)

end AdalyFormal.UnifLane.Z
