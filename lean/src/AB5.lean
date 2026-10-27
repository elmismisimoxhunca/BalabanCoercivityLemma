import AB4
import CB4
import SpikeBlocked
/-!
# AB5 -- the genuine `SU(2)` tower on diagonal configurations: bridge, curvature, links (every `ell ≥ 1`)

For `U = torusCfg f` (all links on the maximal torus `diag(e^{iθ}, e^{-iθ})`):

* `ubarSU2_congr`: `ubarSU2 s ell V c` depends only on the bonds its loops read (locality).
* `ubarSU2_torusCfg_abs`: on the full principal branch `|loopAngle| < π`, `ubarSU2 = torus ∘ blkAngle`.
* `tower_torus`: if `ell^n ∣ L ρ + 1`, all fine curls are `≤ q0` and `3(ell−1)ell(ell²)^m q0 < π` for
  `m < n`, then at every `ell^l`-aligned bond (`l ≤ n`): `ubarTowerSU2 ell U l c = torus (linT ell f l c)`.
* `tower_torus_curv`: then `dv (pw (ell^l) (ubarTowerSU2 ell U l) y ν μ) ≤ √2 · (ell²)^l · q0` at
  every `ell^l`-aligned `y`: level-uniform curvature blocking of the GENUINE tower, constant `√2`
  (from `‖torus θ − 1‖ ≤ √2|θ|`), every `ell ≥ 1` — dyadic included — in the abelian sector.
* (links: see AB6, `tower_torus_link`.)

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Exp torus torus_add psiR su2Exp_psiR)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_mem_coarseLattice)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath coarsePathEndpoint)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf coarsePathEndpoint_coarseGammaPath)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS cPlusS_eq coarseBondVar gammaVarStrided loopVar
  stridedBlockedGauge)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2 ubarTowerSU2 ubarSU2_eq_blockedLink)
open AdalyFormal.Balaban.BlockingLinkEstimate (blockExponent)
open AdalyFormal.Balaban.AbelianBlockingRate (torusCfg pathAngle pathAngle_cons pathAngle_nil
  bondAngle loopAngle blkAngle coarseBondVar_torusCfg loopVar_torusCfg torus_inv
  frobNorm_torus_sub_one)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice coarseLattice_mem_fits)

variable {L : PeriodicLatticeExtent}

theorem hol_congr (s : ℕ) (V V' : PeriodicLinkConfiguration SU2 L) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L), (∀ b ∈ pathBonds s y p, V b = V' b) →
      coarsePathHolonomy s V y p = coarsePathHolonomy s V' y p := by
  intro p
  induction p with
  | nil => intro y _; rfl
  | cons μ rest ih =>
      intro y h
      show V (y, μ) * coarsePathHolonomy s V (coarseShift y s μ) rest
        = V' (y, μ) * coarsePathHolonomy s V' (coarseShift y s μ) rest
      rw [h _ (List.mem_cons_self ..), ih _ (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- **Locality of the blocking.** -/
theorem ubarSU2_congr (s ell : ℕ) (V V' : PeriodicLinkConfiguration SU2 L)
    (c : PeriodicLatticeEdge L)
    (h : ∀ x ∈ stepBlockOf c.1 s ell, ∀ b ∈ loopBonds s ell c x, V b = V' b)
    (hc : ∀ b ∈ pathBonds s c.1 (List.replicate ell c.2), V b = V' b) :
    ubarSU2 s ell V c = ubarSU2 s ell V' c := by
  have hcb : coarseBondVar s ell V c = coarseBondVar s ell V' c :=
    hol_congr s V V' _ _ hc
  have hl : ∀ x ∈ stepBlockOf c.1 s ell, loopVar s ell V c x = loopVar s ell V' c x := by
    intro x hx
    have m : ∀ b, (b ∈ pathBonds s c.1 (coarseGammaPath s c.1 x)
        ∨ b ∈ pathBonds s x (List.replicate ell c.2)
        ∨ b ∈ pathBonds s (cPlusS s ell c) (coarseGammaPath s c.1 x)) → V b = V' b := by
      intro b hb
      refine h x hx b ?_
      unfold loopBonds
      simp only [List.mem_append]
      rcases hb with hb | hb | hb
      · exact Or.inl (Or.inl (Or.inl hb))
      · exact Or.inl (Or.inl (Or.inr hb))
      · exact Or.inl (Or.inr hb)
    show gammaVarStrided s ell V c x * (coarseBondVar s ell V c)⁻¹
      = gammaVarStrided s ell V' c x * (coarseBondVar s ell V' c)⁻¹
    unfold gammaVarStrided
    rw [hol_congr s V V' _ _ (fun b hb => m b (Or.inl hb)),
      hol_congr s V V' _ _ (fun b hb => m b (Or.inr (Or.inl hb))),
      hol_congr s V V' _ _ (fun b hb => m b (Or.inr (Or.inr hb))), hcb]
  show stridedBlockedGauge _ s ell V c = stridedBlockedGauge _ s ell V' c
  unfold stridedBlockedGauge
  rw [Finset.sum_congr rfl (fun x hx => by rw [hl x hx]), hcb]

/-- `ubarSU2` on a torus configuration, full principal branch. -/
theorem ubarSU2_torusCfg_abs (s ell : ℕ) (F : PeriodicLatticeEdge L → ℝ)
    (c : PeriodicLatticeEdge L)
    (hbr : ∀ x ∈ stepBlockOf c.1 s ell, |loopAngle s ell F c x| < Real.pi) :
    ubarSU2 s ell (torusCfg F) c = torus (blkAngle s ell F c) := by
  rw [ubarSU2_eq_blockedLink]
  show su2Exp (blockExponent (stepBlockOf c.1 s ell) (fun _ => ((ell : ℝ) ^ 3)⁻¹)
      (fun x => loopVar s ell (torusCfg F) c x)) * coarseBondVar s ell (torusCfg F) c = _
  have hexp : blockExponent (stepBlockOf c.1 s ell) (fun _ => ((ell : ℝ) ^ 3)⁻¹)
      (fun x => loopVar s ell (torusCfg F) c x)
      = psiR (∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℝ) ^ 3)⁻¹ * loopAngle s ell F c x) := by
    unfold blockExponent psiR
    rw [Complex.ofReal_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    dsimp only
    rw [loopVar_torusCfg, AdalyFormal.SpikeBlocked.su2Log_torus_abs (hbr x hx)]
    unfold psiR
    rw [smul_smul]
    congr 1
    push_cast
    ring
  rw [hexp, su2Exp_psiR, coarseBondVar_torusCfg, ← torus_add, blkAngle]

theorem cl_mono (s ell : ℕ) {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L (s * ell)) :
    y ∈ CoarseLattice L s := by
  rw [mem_CoarseLattice] at hy ⊢
  intro ν
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Dvd.intro ell rfl) (Nat.dvd_of_mod_eq_zero (hy ν)))

theorem pathBonds_aligned (s : ℕ) (hdvd : ∀ ρ, s ∣ L ρ + 1) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L), y ∈ CoarseLattice L s →
      ∀ b ∈ pathBonds s y p, b.1 ∈ CoarseLattice L s := by
  intro p
  induction p with
  | nil => intro y _ b hb; simp [pathBonds] at hb
  | cons μ rest ih =>
      intro y hy b hb
      rcases List.mem_cons.mp hb with h | h
      · rw [h]; exact hy
      · exact ih _ (coarseShift_mem_coarseLattice hdvd hy μ) b h

theorem loopBonds_aligned (s ell : ℕ) (hdvd : ∀ ρ, s * ell ∣ L ρ + 1)
    (c : PeriodicLatticeEdge L) (hc : c.1 ∈ CoarseLattice L (s * ell))
    (x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf c.1 s ell) :
    ∀ b ∈ loopBonds s ell c x, b.1 ∈ CoarseLattice L s := by
  have hd : ∀ ρ, s ∣ L ρ + 1 := fun ρ => Nat.dvd_trans (Dvd.intro ell rfl) (hdvd ρ)
  have h1 := cl_mono s ell hc
  have hxa := block_aligned s ell hc hx
  have hp : cPlusS s ell c ∈ CoarseLattice L s := by
    rw [cPlusS_eq]; exact cl_mono s ell (coarseShift_mem_coarseLattice hdvd hc c.2)
  intro b hb
  unfold loopBonds at hb
  simp only [List.mem_append] at hb
  rcases hb with ((hb | hb) | hb) | hb
  · exact pathBonds_aligned s hd _ _ h1 b hb
  · exact pathBonds_aligned s hd _ _ hxa b hb
  · exact pathBonds_aligned s hd _ _ hp b hb
  · exact pathBonds_aligned s hd _ _ h1 b hb

/-- The block loop angle is the abelian ladder. -/
theorem loopAngle_eq_ladA (s ell : ℕ) (F : PeriodicLatticeEdge L → ℝ)
    (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf c.1 s ell) :
    loopAngle s ell F c x = ladA s F c.1 (coarseGammaPath s c.1 x) c.2 ell := by
  have hmem := mem_stepBlockOf.mp hx
  have hend : coarsePathEndpoint s c.1 (coarseGammaPath s c.1 x) = x :=
    coarsePathEndpoint_coarseGammaPath (fun μ => ⟨(hmem μ).1, (hmem μ).2.2⟩)
  unfold ladA loopAngle bondAngle
  rw [hend, ← cPlusS_eq]

theorem loopAngle_le (s ell : ℕ) (hs : 0 < s) (F : PeriodicLatticeEdge L → ℝ)
    (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf c.1 s ell)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (h : ∀ t ∈ ladPlaqs s c.2 ell c.1 (coarseGammaPath s c.1 x), |curlS s F t.1 t.2.1 t.2.2| ≤ Q) :
    |loopAngle s ell F c x| ≤ 3 * ((ell : ℝ) - 1) * (ell : ℝ) * Q := by
  have hell := AdalyFormal.Balaban.ClassPropagationUbar.ell_pos_of_mem hs hx
  have hg := AdalyFormal.Balaban.ClassPropagationUbar.gammaPath_length_le c.1 x hs hx
  have hgR : ((coarseGammaPath s c.1 x).length : ℝ) ≤ 3 * ((ell : ℝ) - 1) := by
    have h1 : ((coarseGammaPath s c.1 x).length : ℝ) ≤ ((3 * (ell - 1) : ℕ) : ℝ) := by
      exact_mod_cast hg
    rw [Nat.cast_mul, Nat.cast_sub hell] at h1; push_cast at h1; linarith
  rw [loopAngle_eq_ladA s ell F c x hx]
  refine le_trans (ladA_le s F c.2 ell Q _ c.1 h) ?_
  have : (0 : ℝ) ≤ (ell : ℝ) * Q := by positivity
  nlinarith

/-- **Bridge: the genuine tower on diagonal configurations.** -/
theorem tower_torus (ell : ℕ) (hell : 0 < ell) (f : PeriodicLatticeEdge L → ℝ) (q0 : ℝ)
    (hq0 : 0 ≤ q0) (h0 : ∀ y ν μ, |curlS 1 f y ν μ| ≤ q0) (n : ℕ)
    (hdvd : ∀ ρ, ell ^ n ∣ L ρ + 1)
    (hsmall : ∀ m < n, 3 * ((ell : ℝ) - 1) * (ell : ℝ) * (((ell : ℝ) ^ 2) ^ m * q0) < Real.pi) :
    ∀ l ≤ n, ∀ c : PeriodicLatticeEdge L, c.1 ∈ CoarseLattice L (ell ^ l) →
      ubarTowerSU2 ell (torusCfg f) l c = torus (linT ell f l c) := by
  intro l
  induction l with
  | zero => intro _ c _; rfl
  | succ k ih =>
      intro hk c hc
      have hs : 0 < ell ^ k := pow_pos hell k
      have hd1 : ∀ ρ, ell ^ k * ell ∣ L ρ + 1 := fun ρ =>
        Nat.dvd_trans (by rw [← pow_succ]; exact Nat.pow_dvd_pow ell hk) (hdvd ρ)
      have hd0 : ∀ ρ, ell ^ k ∣ L ρ + 1 := fun ρ =>
        Nat.dvd_trans (Nat.pow_dvd_pow ell (by omega)) (hdvd ρ)
      have hc' : c.1 ∈ CoarseLattice L (ell ^ k * ell) := by rw [← pow_succ]; exact hc
      have hck := cl_mono (ell ^ k) ell hc'
      show ubarSU2 (ell ^ k) ell (ubarTowerSU2 ell (torusCfg f) k) c
        = torus (blkAngle (ell ^ k) ell (linT ell f k) c)
      rw [ubarSU2_congr (ell ^ k) ell _ (torusCfg (linT ell f k)) c
        (fun x hx b hb => ih (by omega) b (loopBonds_aligned _ _ hd1 c hc' x hx b hb))
        (fun b hb => ih (by omega) b (pathBonds_aligned _ hd0 _ _ hck b hb))]
      refine ubarSU2_torusCfg_abs _ _ _ _ (fun x hx => ?_)
      have hQ : 0 ≤ ((ell : ℝ) ^ 2) ^ k * q0 := by positivity
      refine lt_of_le_of_lt (loopAngle_le (ell ^ k) ell hs (linT ell f k) c x hx _ hQ
        (fun t ht => linT_curl ell hell f q0 h0 n hdvd k (by omega) t.1
          (ladPlaqs_aligned _ hd0 _ _ _ _ hck t ht) t.2.1 t.2.2)) ?_
      exact hsmall k (by omega)

theorem dv_torus_le (θ : ℝ) : dv (torus θ) ≤ Real.sqrt 2 * |θ| := by
  unfold dv
  rw [frobNorm_torus_sub_one]
  have hc := Real.one_sub_sq_div_two_le_cos (x := θ)
  have h2 : Real.sqrt 2 * |θ| = Real.sqrt (2 * θ ^ 2) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq_eq_abs]
  rw [h2]
  exact Real.sqrt_le_sqrt (by nlinarith)

/-- **Level-uniform curvature blocking of the genuine tower, abelian sector, every `ell ≥ 1`.** -/
theorem tower_torus_curv (ell : ℕ) (hell : 0 < ell) (f : PeriodicLatticeEdge L → ℝ) (q0 : ℝ)
    (hq0 : 0 ≤ q0) (h0 : ∀ y ν μ, |curlS 1 f y ν μ| ≤ q0) (n : ℕ)
    (hdvd : ∀ ρ, ell ^ n ∣ L ρ + 1)
    (hsmall : ∀ m < n, 3 * ((ell : ℝ) - 1) * (ell : ℝ) * (((ell : ℝ) ^ 2) ^ m * q0) < Real.pi)
    (l : ℕ) (hl : l ≤ n) (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L (ell ^ l))
    (ν μ : Fin 3) :
    dv (pw (ell ^ l) (ubarTowerSU2 ell (torusCfg f) l) y ν μ)
      ≤ Real.sqrt 2 * (((ell : ℝ) ^ 2) ^ l * q0) := by
  have hd0 : ∀ ρ, ell ^ l ∣ L ρ + 1 := fun ρ => Nat.dvd_trans (Nat.pow_dvd_pow ell hl) (hdvd ρ)
  have T := tower_torus ell hell f q0 hq0 h0 n hdvd hsmall l hl
  have e1 := T (y, ν) hy
  have e2 := T (coarseShift y (ell ^ l) ν, μ) (coarseShift_mem_coarseLattice hd0 hy ν)
  have e3 := T (coarseShift y (ell ^ l) μ, ν) (coarseShift_mem_coarseLattice hd0 hy μ)
  have e4 := T (y, μ) hy
  have hpw : pw (ell ^ l) (ubarTowerSU2 ell (torusCfg f) l) y ν μ
      = torus (curlS (ell ^ l) (linT ell f l) y ν μ) := by
    unfold pw curlS
    rw [e1, e2, e3, e4, torus_inv, torus_inv, ← torus_add, ← torus_add, ← torus_add]
    congr 1
    try ring
  rw [hpw]
  refine le_trans (dv_torus_le _) ?_
  exact mul_le_mul_of_nonneg_left
    (linT_curl ell hell f q0 h0 n hdvd l hl y hy ν μ) (Real.sqrt_nonneg 2)

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.ubarSU2_congr
#print axioms AdalyFormal.CurvBlock.ubarSU2_torusCfg_abs
#print axioms AdalyFormal.CurvBlock.tower_torus
#print axioms AdalyFormal.CurvBlock.tower_torus_curv
