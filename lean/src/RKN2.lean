import RKN1
import RKA2
/-!
# RKN2 -- ALL-BOND, k-UNIFORM bound for the genuine blocked tower (every `ell ≥ 2`), and `RegTower` from it.

`D l = Alog (bg l) − Alog (st l)` obeys `D (l+1) = blkM_l (D l) + src_l` exactly, `‖src_l‖ ≤ sig ell · (ell²)^l (q0+e²)`
(RKN1), hence `D L = Σ_{l<L} Tcomp ell (l+1) (L−1−l) src_l` and (RKL3, rate `lamK ell < ell²`)
  `‖D L‖ ≤ Kc ell · (ell²)^L · (q0 + e²)`,  `Kc ell = 7 sig ell / (ell² − lamK ell)`,  at EVERY bond, every `L ≤ k`,
under the smallness `TowerSmall ell k e q0` (k enters only through `ell^k e` and `(ell²)^k (q0+e²)`).
`tower_allbond`: charts + defect bound; `dv_bg_le`: `dv (bg l b) ≤ 2 ell^l e + Kc (ell²)^l (q0+e²)` for all bonds;
`regTower_allbond`: R2's `RegTower ell (ubarTowerSU2 ell U) k` from `(8 ell − 6)(2 ell^k e + Kc (ell²)^k (q0+e²)) < r0`.
Kernel-checked; standard axioms only (see the #print axioms lines).
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.RegBgKU
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Exp)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_nonneg)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2 ubarTowerSU2)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)
open AdalyFormal.CurvBlock (blkM bondM Chart strT dv pw chart_small strT_link_le dv_exp_le)
open AdalyFormal.IngredientFamilyR2 (LogReg RegTower)
open AdalyFormal.NonflatJet (r0 mem_LogReg_of_frob_lt)

variable {L : PeriodicLatticeExtent}

def sig (ell : ℕ) : ℝ := 2008 * Real.pi * (ell : ℝ) ^ 2 + 3 * ((ell : ℝ) - 1) * (ell : ℝ) * (2 + 128 * Real.pi)

def Kc (ell : ℕ) : ℝ := 7 * sig ell / ((ell : ℝ) ^ 2 - lamK ell)

def Bnd (ell : ℕ) (e q0 : ℝ) (l : ℕ) : ℝ := Kc ell * (((ell : ℝ) ^ 2) ^ l * (q0 + e ^ 2))

def kap (ell : ℕ) (e q0 : ℝ) (l : ℕ) : ℝ := 2 * ((ell : ℝ) ^ l * e) + Bnd ell e q0 l

/-- smallness at the top level `k` (all lower levels follow by monotonicity). -/
structure TowerSmall (ell k : ℕ) (e q0 : ℝ) : Prop where
  h1 : (ell : ℝ) ^ k * e ≤ 1 / 2
  h2 : 8 * (ell : ℝ) * kap ell e q0 k ≤ 1 / (8 * Real.pi)
  h3 : ((ell : ℝ) ^ 2) ^ k * q0 ≤ 1
  h4 : Kc ell ^ 2 * (((ell : ℝ) ^ 2) ^ k * (q0 + e ^ 2)) ≤ 1

theorem sig_pos (ell : ℕ) (hell : 1 ≤ ell) : 0 < sig ell := by
  have h : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  unfold sig; have hpi := Real.pi_pos
  have : 0 ≤ 3 * ((ell : ℝ) - 1) * (ell : ℝ) * (2 + 128 * Real.pi) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)) (by positivity)
  have : 0 < 2008 * Real.pi * (ell : ℝ) ^ 2 := by positivity
  linarith

theorem Kc_pos (ell : ℕ) (hell : 2 ≤ ell) : 0 < Kc ell := by
  unfold Kc
  have := sig_pos ell (by omega)
  have := lamK_lt_sq ell hell
  apply div_pos (by positivity); linarith

theorem lamK_nonneg (ell : ℕ) : 0 ≤ lamK ell := by unfold lamK Emax; positivity

/-- generic unrolling of a recursion driven by the linear blocking. -/
theorem unroll_gen (ell : ℕ) (X Y : ℕ → Fld L) (h0 : X 0 = 0)
    (hX : ∀ i, X (i + 1) = blkM (ell ^ i) ell (X i) + Y i) :
    ∀ m, X m = ∑ i ∈ Finset.range m, Tcomp ell (i + 1) (m - 1 - i) (Y i) := by
  intro m; induction m with
  | zero => simp [h0]
  | succ m ih =>
      rw [Finset.sum_range_succ, hX m, ih, blkM_sum]
      congr 1
      · refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi' := Finset.mem_range.mp hi
        have e1 : m + 1 - 1 - i = (m - 1 - i) + 1 := by omega
        have e2 : i + 1 + (m - 1 - i) = m := by omega
        rw [e1]; show _ = blkM (ell ^ (i + 1 + (m - 1 - i))) ell _; rw [e2]
      · rw [show m + 1 - 1 - m = 0 by omega]; rfl

theorem unroll (ell : ℕ) (X : ℕ → Fld L) (h0 : X 0 = 0) :
    ∀ m, X m = ∑ i ∈ Finset.range m, Tcomp ell (i + 1) (m - 1 - i) (X (i + 1) - blkM (ell ^ i) ell (X i)) :=
  unroll_gen ell X (fun i => X (i + 1) - blkM (ell ^ i) ell (X i)) h0 (fun i => by abel)

theorem geom_sum_le (lam mu : ℝ) (h0 : 0 ≤ lam) (h : lam ≤ mu) :
    ∀ m : ℕ, (mu - lam) * ∑ i ∈ Finset.range m, lam ^ (m - 1 - i) * mu ^ i ≤ mu ^ m := by
  have hmu : 0 ≤ mu := le_trans h0 h
  intro m; induction m with
  | zero => simp
  | succ m ih =>
      have hs : ∑ i ∈ Finset.range (m + 1), lam ^ (m + 1 - 1 - i) * mu ^ i
          = lam * ∑ i ∈ Finset.range m, lam ^ (m - 1 - i) * mu ^ i + mu ^ m := by
        rw [Finset.sum_range_succ, Finset.mul_sum]
        congr 1
        · refine Finset.sum_congr rfl (fun i hi => ?_)
          have hi' := Finset.mem_range.mp hi
          rw [show m + 1 - 1 - i = (m - 1 - i) + 1 by omega, pow_succ]; ring
        · rw [show m + 1 - 1 - m = 0 by omega]; ring
      rw [hs, pow_succ]
      have h1 := mul_le_mul_of_nonneg_left ih h0
      have h2 : 0 ≤ mu - lam := by linarith
      nlinarith [pow_nonneg hmu m]

/-- the source arithmetic. -/
theorem src_arith (ell : ℕ) (hell : 1 ≤ ell) (a p b : ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hb2 : b ^ 2 ≤ p + a ^ 2) :
    200 * Real.pi * ((ell : ℝ) ^ 2 * (2 * a + b) ^ 2) + 2 * Real.pi * ((ell : ℝ) * (2 * a)) ^ 2
      + 3 * ((ell : ℝ) - 1) * (ell : ℝ) * (p + p ^ 3 / 8 + 32 * Real.pi * (2 * a) ^ 2)
      ≤ sig ell * (p + a ^ 2) := by
  have hl : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hpi := Real.pi_pos
  have hk2 : (2 * a + b) ^ 2 ≤ 10 * (p + a ^ 2) := by nlinarith [sq_nonneg (2 * a - b)]
  have hp3 : p ^ 3 ≤ p := by nlinarith [mul_nonneg hp hp, mul_le_mul_of_nonneg_left hp1 (mul_nonneg hp hp)]
  have hc : 0 ≤ 3 * ((ell : ℝ) - 1) * (ell : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  have t1 : 200 * Real.pi * ((ell : ℝ) ^ 2 * (2 * a + b) ^ 2) ≤ 2000 * Real.pi * (ell : ℝ) ^ 2 * (p + a ^ 2) := by
    have := mul_le_mul_of_nonneg_left hk2 (by positivity : (0:ℝ) ≤ 200 * Real.pi * (ell : ℝ) ^ 2); nlinarith
  have t2 : 2 * Real.pi * ((ell : ℝ) * (2 * a)) ^ 2 ≤ 8 * Real.pi * (ell : ℝ) ^ 2 * (p + a ^ 2) := by
    have : 2 * Real.pi * ((ell : ℝ) * (2 * a)) ^ 2 = 8 * Real.pi * (ell : ℝ) ^ 2 * a ^ 2 := by ring
    rw [this]; have := mul_nonneg (by positivity : (0:ℝ) ≤ 8 * Real.pi * (ell : ℝ) ^ 2) hp; nlinarith
  have t3 : p + p ^ 3 / 8 + 32 * Real.pi * (2 * a) ^ 2 ≤ (2 + 128 * Real.pi) * (p + a ^ 2) := by nlinarith
  have t3' := mul_le_mul_of_nonneg_left t3 hc
  have es : sig ell * (p + a ^ 2) = 2000 * Real.pi * (ell : ℝ) ^ 2 * (p + a ^ 2) + 8 * Real.pi * (ell : ℝ) ^ 2 * (p + a ^ 2)
      + 3 * ((ell : ℝ) - 1) * (ell : ℝ) * ((2 + 128 * Real.pi) * (p + a ^ 2)) := by unfold sig; ring
  rw [es]; linarith

/-- **The all-bond tower theorem.** -/
theorem tower_allbond (ell k : ℕ) (hell : 2 ≤ ell) (U : PeriodicLinkConfiguration SU2 L) (e q0 : ℝ)
    (he0 : 0 ≤ e) (hq0 : 0 ≤ q0) (hlinks : ∀ b, dv (U b) ≤ e) (h0 : ∀ y ν μ, dv (pw 1 U y ν μ) ≤ q0)
    (S : TowerSmall ell k e q0) :
    ∀ L', L' ≤ k → ∀ l, l ≤ L' → ∀ b,
      Chart (ubarTowerSU2 ell U l) (Alog (ubarTowerSU2 ell U l)) (kap ell e q0 l) b ∧
      frobNorm ((Alog (ubarTowerSU2 ell U l) - Alog (strT ell U l)) b) ≤ Bnd ell e q0 l := by
  have hell0 : 0 < ell := by omega
  have hl1 : (1 : ℝ) ≤ ell := by exact_mod_cast (by omega : 1 ≤ ell)
  have hpi := Real.pi_pos
  set mu : ℝ := (ell : ℝ) ^ 2 with hmu
  have hmu1 : 1 ≤ mu := by rw [hmu]; nlinarith
  have hKc := Kc_pos ell hell
  have hlam := lamK_lt_sq ell hell
  have hlam0 := lamK_nonneg ell
  -- monotone smallness
  have hel : ∀ l, l ≤ k → (ell : ℝ) ^ l * e ≤ (ell : ℝ) ^ k * e := fun l hl =>
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hl1 hl) he0
  have hmul : ∀ l, l ≤ k → mu ^ l ≤ mu ^ k := fun l hl => pow_le_pow_right₀ hmu1 hl
  have hQ0 : 0 ≤ q0 + e ^ 2 := by positivity
  have hBnd0 : ∀ l, 0 ≤ Bnd ell e q0 l := fun l => by unfold Bnd; positivity
  have hkapmono : ∀ l, l ≤ k → kap ell e q0 l ≤ kap ell e q0 k := by
    intro l hl; unfold kap Bnd
    have := hel l hl
    have := mul_le_mul_of_nonneg_right (hmul l hl) hQ0
    have := mul_le_mul_of_nonneg_left this hKc.le
    nlinarith
  -- straight-tower charts
  have hstch : ∀ l, l ≤ k → ∀ b, Chart (strT ell U l) (Alog (strT ell U l)) (2 * ((ell : ℝ) ^ l * e)) b := by
    intro l hl b
    have hd := strT_link_le ell U e hlinks l b
    have hd1 : dv (strT ell U l b) ≤ 1 := hd.trans ((hel l hl).trans (S.h1.trans (by norm_num)))
    obtain ⟨h1, h2, h3⟩ := chart_small _ hd1
    exact ⟨h1.symm, h2, h3.trans (by linarith)⟩
  -- the source bound at a level whose bg-chart is known
  have hsrc : ∀ l, l < k → (∀ b, Chart (ubarTowerSU2 ell U l) (Alog (ubarTowerSU2 ell U l)) (kap ell e q0 l) b) →
      ∀ c, frobNorm (((Alog (ubarTowerSU2 ell U (l + 1)) - Alog (strT ell U (l + 1)))
        - blkM (ell ^ l) ell (Alog (ubarTowerSU2 ell U l) - Alog (strT ell U l))) c)
        ≤ sig ell * (mu ^ l * (q0 + e ^ 2)) := by
    intro l hl hch c
    have hkap0 : 0 ≤ kap ell e q0 l := by unfold kap; have := hBnd0 l; positivity
    have hsm : 8 * (ell : ℝ) * kap ell e q0 l ≤ 1 / (8 * Real.pi) :=
      le_trans (mul_le_mul_of_nonneg_left (hkapmono l hl.le) (by positivity)) S.h2
    have hb := (step_bg ell l hell0 U (kap ell e q0 l) hkap0 hsm hch c).2
    have hkT0 : 0 ≤ 2 * ((ell : ℝ) ^ l * e) := by positivity
    have hkT : (ell : ℝ) * (2 * ((ell : ℝ) ^ l * e)) ≤ 1 / (2 * Real.pi) := by
      have h2 := S.h2; unfold kap at h2
      have := hel l hl.le; have := hBnd0 k
      have : 1 / (8 * Real.pi) ≤ 1 / (2 * Real.pi) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      nlinarith
    have hst := step_st ell l U _ hkT0 hkT (hstch l hl.le) c
    have hk4 : 4 * (2 * ((ell : ℝ) ^ l * e)) ≤ 1 / (2 * Real.pi) := by
      have hl2 : (2 : ℝ) ≤ ell := by exact_mod_cast hell
      have : 4 * (2 * ((ell : ℝ) ^ l * e)) ≤ (ell : ℝ) * (2 * ((ell : ℝ) ^ l * e)) * 2 := by
        nlinarith [mul_le_mul_of_nonneg_right hl2 hkT0]
      have h2 := S.h2; unfold kap at h2
      have := hel l hl.le; have := hBnd0 k
      have : 1 / (8 * Real.pi) * 2 ≤ 1 / (2 * Real.pi) := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      nlinarith
    have hP : mu ^ l * q0 ≤ 1 := le_trans (mul_le_mul_of_nonneg_right (hmul l hl.le) hq0) S.h3
    have hs := src_st ell l hell0 U q0 _ hkT0 hk4 h0 hP (hstch l hl.le) c
    -- algebra
    have e1 : ((Alog (ubarTowerSU2 ell U (l + 1)) - Alog (strT ell U (l + 1)))
        - blkM (ell ^ l) ell (Alog (ubarTowerSU2 ell U l) - Alog (strT ell U l))) c
        = (Alog (ubarTowerSU2 ell U (l + 1)) c - blkM (ell ^ l) ell (Alog (ubarTowerSU2 ell U l)) c)
          - (Alog (strT ell U (l + 1)) c - bondM (ell ^ l) ell (Alog (strT ell U l)) c)
          + (blkM (ell ^ l) ell (Alog (strT ell U l)) c - bondM (ell ^ l) ell (Alog (strT ell U l)) c) := by
      rw [blkM_sub]; simp only [Pi.sub_apply]; abel
    rw [e1]
    have t := frob_add ((Alog (ubarTowerSU2 ell U (l + 1)) c - blkM (ell ^ l) ell (Alog (ubarTowerSU2 ell U l)) c)
          - (Alog (strT ell U (l + 1)) c - bondM (ell ^ l) ell (Alog (strT ell U l)) c))
      (blkM (ell ^ l) ell (Alog (strT ell U l)) c - bondM (ell ^ l) ell (Alog (strT ell U l)) c)
    have t' := frob_sub (Alog (ubarTowerSU2 ell U (l + 1)) c - blkM (ell ^ l) ell (Alog (ubarTowerSU2 ell U l)) c)
      (Alog (strT ell U (l + 1)) c - bondM (ell ^ l) ell (Alog (strT ell U l)) c)
    -- the arithmetic with a = ell^l e, p = mu^l q0, b = Bnd l
    have hb2 : Bnd ell e q0 l ^ 2 ≤ mu ^ l * q0 + ((ell : ℝ) ^ l * e) ^ 2 := by
      have hx : 0 ≤ mu ^ l * (q0 + e ^ 2) := by positivity
      have hsmall : Kc ell ^ 2 * (mu ^ l * (q0 + e ^ 2)) ≤ 1 :=
        le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hmul l hl.le) hQ0) (by positivity)) S.h4
      have e2 : Bnd ell e q0 l ^ 2 = (Kc ell ^ 2 * (mu ^ l * (q0 + e ^ 2))) * (mu ^ l * (q0 + e ^ 2)) := by
        unfold Bnd; rw [← hmu]; ring
      have e3 : mu ^ l * q0 + ((ell : ℝ) ^ l * e) ^ 2 = mu ^ l * (q0 + e ^ 2) := by rw [hmu, ← pow_mul, mul_pow, ← pow_mul]; ring
      rw [e2, e3]; nlinarith
    have ha := src_arith ell (by omega) ((ell : ℝ) ^ l * e) (mu ^ l * q0) (Bnd ell e q0 l) (by positivity)
      (by positivity) hP hb2
    have e4 : mu ^ l * q0 + ((ell : ℝ) ^ l * e) ^ 2 = mu ^ l * (q0 + e ^ 2) := by
      rw [hmu, ← pow_mul, mul_pow, ← pow_mul]; ring
    rw [e4] at ha
    have hkapdef : kap ell e q0 l = 2 * ((ell : ℝ) ^ l * e) + Bnd ell e q0 l := rfl
    rw [hkapdef] at hb
    have hP' : ((ell : ℝ) ^ 2) ^ l * q0 = mu ^ l * q0 := by rw [hmu]
    rw [hP'] at hs
    nlinarith
  -- main induction
  intro L'
  induction L' with
  | zero =>
      intro _ l hl b
      have hl0 : l = 0 := by omega
      subst hl0
      have hd1 : dv (U b) ≤ 1 := (hlinks b).trans (by have := S.h1; have : (ell : ℝ) ^ k * e ≥ e := by
                                                        have := one_le_pow₀ (n := k) hl1; nlinarith
                                                      linarith)
      obtain ⟨h1, h2, h3⟩ := chart_small (U b) hd1
      refine ⟨⟨h1.symm, h2, ?_⟩, ?_⟩
      · show frobNorm (su2Log (U b)) ≤ kap ell e q0 0
        unfold kap; have := hBnd0 0; have := hlinks b; simp only [pow_zero, one_mul]; linarith
      · show frobNorm (su2Log (U b) - su2Log (U b)) ≤ Bnd ell e q0 0
        rw [sub_self, AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero]; exact hBnd0 0
  | succ n ih =>
      intro hLk l hl b
      rcases Nat.lt_or_ge l (n + 1) with hlt | hge
      · exact ih (by omega) l (by omega) b
      have hlL : l = n + 1 := by omega
      subst hlL
      have IH := ih (by omega)
      -- defect bound by unrolling
      set D : ℕ → Fld L := fun j => Alog (ubarTowerSU2 ell U j) - Alog (strT ell U j) with hD
      have hD0 : D 0 = 0 := by
        funext b'; simp only [hD, Pi.sub_apply, Pi.zero_apply]
        show su2Log (U b') - su2Log (U b') = 0; exact sub_self _
      have hun := unroll ell D hD0 (n + 1)
      have hterm : ∀ i ∈ Finset.range (n + 1), ∀ c,
          frobNorm (Tcomp ell (i + 1) (n + 1 - 1 - i) (D (i + 1) - blkM (ell ^ i) ell (D i)) c)
            ≤ 7 * lamK ell ^ (n + 1 - 1 - i) * (sig ell * (mu ^ i * (q0 + e ^ 2))) := by
        intro i hi c
        have hi' := Finset.mem_range.mp hi
        have hch : ∀ b, Chart (ubarTowerSU2 ell U i) (Alog (ubarTowerSU2 ell U i)) (kap ell e q0 i) b :=
          fun b => (IH i (by omega) b).1
        exact Tcomp_le ell hell0 (lamK ell) le_rfl (n + 1 - 1 - i) (i + 1) _ _ (by have := sig_pos ell (by omega); positivity)
          (hsrc i (by omega) hch) c
      have hDb : frobNorm (D (n + 1) b) ≤ Bnd ell e q0 (n + 1) := by
        rw [hun, Finset.sum_apply]
        refine (frob_sum _ _).trans ((Finset.sum_le_sum (fun i hi => hterm i hi b)).trans ?_)
        have hg := geom_sum_le (lamK ell) mu hlam0 hlam.le (n + 1)
        have hsig := sig_pos ell (by omega)
        have hden : 0 < mu - lamK ell := by linarith
        have e5 : ∑ i ∈ Finset.range (n + 1), 7 * lamK ell ^ (n + 1 - 1 - i) * (sig ell * (mu ^ i * (q0 + e ^ 2)))
            = 7 * sig ell * (q0 + e ^ 2) * ∑ i ∈ Finset.range (n + 1), lamK ell ^ (n + 1 - 1 - i) * mu ^ i := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => by ring)
        rw [e5]
        have hS : ∑ i ∈ Finset.range (n + 1), lamK ell ^ (n + 1 - 1 - i) * mu ^ i ≤ mu ^ (n + 1) / (mu - lamK ell) := by
          rw [le_div_iff₀ hden]; linarith
        unfold Bnd Kc
        rw [← hmu]
        calc 7 * sig ell * (q0 + e ^ 2) * ∑ i ∈ Finset.range (n + 1), lamK ell ^ (n + 1 - 1 - i) * mu ^ i
            ≤ 7 * sig ell * (q0 + e ^ 2) * (mu ^ (n + 1) / (mu - lamK ell)) :=
              mul_le_mul_of_nonneg_left hS (by positivity)
          _ = 7 * sig ell / (mu - lamK ell) * (mu ^ (n + 1) * (q0 + e ^ 2)) := by field_simp
      -- chart at level n+1
      have hchL : ∀ b, Chart (ubarTowerSU2 ell U n) (Alog (ubarTowerSU2 ell U n)) (kap ell e q0 n) b :=
        fun b => (IH n le_rfl b).1
      have hkap0 : 0 ≤ kap ell e q0 n := by unfold kap; have := hBnd0 n; positivity
      have hsm : 8 * (ell : ℝ) * kap ell e q0 n ≤ 1 / (8 * Real.pi) :=
        le_trans (mul_le_mul_of_nonneg_left (hkapmono n (by omega)) (by positivity)) S.h2
      have hexp := (step_bg ell n hell0 U (kap ell e q0 n) hkap0 hsm hchL b).1
      have hT := (hstch (n + 1) hLk b).2.2
      refine ⟨⟨hexp.symm, AdalyFormal.Balaban.Bch2.isSu2_su2Log _, ?_⟩, hDb⟩
      have e6 : Alog (ubarTowerSU2 ell U (n + 1)) b = Alog (strT ell U (n + 1)) b + D (n + 1) b := by
        simp only [hD, Pi.sub_apply]; abel
      rw [e6]
      refine (frob_add _ _).trans ?_
      unfold kap; linarith

theorem dv_bg_le (ell k : ℕ) (hell : 2 ≤ ell) (U : PeriodicLinkConfiguration SU2 L) (e q0 : ℝ)
    (he0 : 0 ≤ e) (hq0 : 0 ≤ q0) (hlinks : ∀ b, dv (U b) ≤ e) (h0 : ∀ y ν μ, dv (pw 1 U y ν μ) ≤ q0)
    (S : TowerSmall ell k e q0) (l : ℕ) (hl : l ≤ k) (b : PeriodicLatticeEdge L) :
    dv (ubarTowerSU2 ell U l b) ≤ kap ell e q0 l := by
  obtain ⟨⟨h1, h2, h3⟩, _⟩ := tower_allbond ell k hell U e q0 he0 hq0 hlinks h0 S l hl l le_rfl b
  rw [h1]; exact (dv_exp_le h2).trans h3

/-- **k-uniform `RegTower` at ALL bonds, every `ell ≥ 2`.** -/
theorem regTower_allbond (ell k : ℕ) (hell : 2 ≤ ell) (U : PeriodicLinkConfiguration SU2 L) (e q0 : ℝ)
    (he0 : 0 ≤ e) (hq0 : 0 ≤ q0) (hlinks : ∀ b, dv (U b) ≤ e) (h0 : ∀ y ν μ, dv (pw 1 U y ν μ) ≤ q0)
    (S : TowerSmall ell k e q0) (hthr : (8 * (ell : ℝ) - 6) * kap ell e q0 k < r0) :
    RegTower ell (ubarTowerSU2 ell U) k := by
  have hell0 : 0 < ell := by omega
  have hl1 : (1 : ℝ) ≤ ell := by exact_mod_cast (by omega : 1 ≤ ell)
  have hKc := Kc_pos ell hell
  refine AdalyFormal.PortSlice.regTower_of_frobSup hell0 (ubarTowerSU2 ell U) k (fun _ => kap ell e q0 k) ?_ r0
    (fun g h => mem_LogReg_of_frob_lt h) (fun _ _ => hthr)
  intro j hj
  refine AdalyFormal.AsmM0.frobSupBond_le_of _ (fun c => ?_)
  refine (dv_bg_le ell k hell U e q0 he0 hq0 hlinks h0 S j hj.le c).trans ?_
  unfold kap Bnd
  have hQ0 : 0 ≤ q0 + e ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hl1 hj.le) he0
  have hmu1 : (1 : ℝ) ≤ (ell : ℝ) ^ 2 := by nlinarith
  have h2 := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hmu1 hj.le) hQ0
  have h3 := mul_le_mul_of_nonneg_left h2 hKc.le
  linarith

#print axioms unroll
#print axioms geom_sum_le
#print axioms src_arith
#print axioms tower_allbond
#print axioms dv_bg_le
#print axioms regTower_allbond

#print axioms sig_pos
#print axioms Kc_pos
#print axioms unroll_gen
#print axioms lamK_nonneg
end AdalyFormal.RegBgKU
