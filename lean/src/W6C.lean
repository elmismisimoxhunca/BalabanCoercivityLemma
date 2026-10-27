import W6B

/-!
# W6C -- the multi-level flat bond right inverse on a proper tower (W6 lane, 2026-10-13)

For a row `p = (j, (z, μ))` of `𝔅` (`n = ℓ^j`, `z⁺ = z + n e_μ`):
* `useUp p` : `1 ≤ j ∧ z ∉ Λ_j` (then `z⁺ ∈ Λ_j`);
* `phiK p` : the scalar kernel `gbK (tprof n) (pprof n) n · (z,μ)` (LOWER, on `B(z)`), or `gbK (uprof n) (pprof n) n · (z⁺,μ)`
  (UPPER, on `B(z⁺)`) if `useUp p`;
* `Eflat y = Σ_p phiK p • y_p`;  `kap p' p` = the flat row `p'` applied to `phiK p` (a real number); `Q₁ (Eflat y) = Σ_p kap · y_p`.
Facts (admissible tower, `ℓ ≥ 2`, `M ≥ 1`, `8ℓ ≤ R`):
* `phi_strat` : every bond in the support of `phiK p` is based at a site of stratum `j` (in `Ω₀`-touching position: `phi_supp`).
* `kap_same` : same level ⇒ `kap p' p = [p = p']` (generic block line sums, W6A);
* `kap_low` : `lev p > lev p'` ⇒ `0`;  `kap_far` : `lev p + 2 ≤ lev p'` ⇒ `0` (collar);
* `kap_N2` : `lev p + 1 = lev p'`, `lev p' + 1 = lev p''` ⇒ `kap p'' p' = 0 ∨ kap p' p = 0` (collar);
* **`kap_sq`** : `Σ_{p'} kap p'' p' · kap p' p = 2 kap p'' p − [p'' = p]`, i.e. `(K − I)² = 0`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.W6

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq coarseShift_mem_coarseLattice)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.StatementLane (Tower Admissible scaleUp bigSide pdist pcd BlockClosed)
open AdalyFormal.StatementLaneR8 (pdist_triangle pdist_comm pdist_self pdist_coarseShift_le)
open AdalyFormal.W6P (gbK gfac tprof pprof tprof_eq_zero pprof_eq_zero pprof_sum)

/-! ## coarse shifts are injective -/

theorem coarseShift_inj {L : PeriodicLatticeExtent} {x y : PeriodicLatticeSite L} {s : ℕ} {μ : Fin 3}
    (h : coarseShift x s μ = coarseShift y s μ) : x = y := by
  funext ν
  by_cases hν : ν = μ
  · subst hν
    apply Fin.ext
    have h1 := congrArg (fun w => (w ν).val) h
    simp only [coarseShift_val_eq] at h1
    have h2 : (x ν).val ≡ (y ν).val [MOD (L ν + 1)] := Nat.ModEq.add_right_cancel' s h1
    have hx := (x ν).isLt
    have hy := (y ν).isLt
    unfold Nat.ModEq at h2
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h2
  · have h1 := congrArg (fun w => w ν) h
    simp only [coarseShift_apply_ne _ _ _ _ hν] at h1
    exact h1

theorem cbUp_inj {L : PeriodicLatticeExtent} {n : ℕ} (hdvd : ∀ ν, n ∣ L ν + 1) {c c' : CoarseBond L n}
    (h : cbUp n hdvd c = cbUp n hdvd c') : c = c' := by
  obtain ⟨⟨y, hy⟩, μ⟩ := c
  obtain ⟨⟨y', hy'⟩, μ'⟩ := c'
  simp only [cbUp, Prod.mk.injEq, Subtype.mk.injEq] at h
  obtain ⟨h1, rfl⟩ := h
  have := coarseShift_inj h1
  subst this; rfl

section kernel
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

/-- the row uses the UPPER kernel -/
def useUp (p : BIdx (geomOf ell k S)) : Prop := 1 ≤ (p.1 : ℕ) ∧ p.2.1.1 ∉ (geomOf ell k S).Lam (p.1 : ℕ)

open Classical in
/-- **the kernel of a row** -/
noncomputable def phiK (hell : 0 < ell) (p : BIdx (geomOf ell k S)) (b : Bond (scaleUp ell k Lu)) : ℝ :=
  if useUp p then
    gbK (AdalyFormal.W6.uprof (ell ^ (p.1 : ℕ))) (pprof (ell ^ (p.1 : ℕ))) (ell ^ (p.1 : ℕ)) b.1 b.2
      (cbUp (ell ^ (p.1 : ℕ)) (hdvdL hell p) (rowCB hell p))
  else gbK (tprof (ell ^ (p.1 : ℕ))) (pprof (ell ^ (p.1 : ℕ))) (ell ^ (p.1 : ℕ)) b.1 b.2 (rowCB hell p)

/-- support of a row kernel: direction of the row, based in `B(z)` (lower) or `B(z⁺)` (upper). -/
theorem phi_support (hell : 0 < ell) (p : BIdx (geomOf ell k S)) (b : Bond (scaleUp ell k Lu))
    (h : phiK hell p b ≠ 0) :
    b.2 = p.2.1.2 ∧ ((¬ useUp p ∧ b.1 ∈ blockOf p.2.1.1 (ell ^ (p.1 : ℕ)))
      ∨ (useUp p ∧ b.1 ∈ blockOf (coarseShift p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2) (ell ^ (p.1 : ℕ)))) := by
  classical
  have hn : 0 < ell ^ (p.1 : ℕ) := pow_pos hell _
  unfold phiK at h
  by_cases hu : useUp p
  · rw [if_pos hu] at h
    obtain ⟨h1, h2⟩ := gbK_support hn (hdvdL hell p) (AdalyFormal.W6.uprof_eq_zero _) (pprof_eq_zero _) h
    exact ⟨h1.symm, Or.inr ⟨hu, h2⟩⟩
  · rw [if_neg hu] at h
    obtain ⟨h1, h2⟩ := gbK_support hn (hdvdL hell p) (tprof_eq_zero _) (pprof_eq_zero _) h
    exact ⟨h1.symm, Or.inl ⟨hu, h2⟩⟩

/-- **every bond carrying a level-`j` kernel is based at a site of stratum `j`** -/
theorem phi_strat (hell : 0 < ell) (hS : Admissible ell M R k S) (p : BIdx (geomOf ell k S))
    (b : Bond (scaleUp ell k Lu)) (h : phiK hell p b ≠ 0) : AdalyFormal.M1.strat S k b.1 = (p.1 : ℕ) := by
  have hj : (p.1 : ℕ) ≤ k := Nat.lt_succ_iff.mp p.1.isLt
  obtain ⟨-, hs⟩ := phi_support hell p b h
  rcases hs with ⟨hu, hb⟩ | ⟨hu, hb⟩
  · by_cases hL : p.2.1.1 ∈ (geomOf ell k S).Lam (p.1 : ℕ)
    · exact strat_of_block hell hS hj hL hb
    · have hj0 : (p.1 : ℕ) = 0 := by
        by_contra hne; exact hu ⟨Nat.one_le_iff_ne_zero.mpr hne, hL⟩
      have hn1 : ell ^ (p.1 : ℕ) = 1 := by rw [hj0, pow_zero]
      have hb1 : b.1 = p.2.1.1 := by
        funext μ; apply Fin.ext
        have := (mem_blockOf.mp hb) μ
        rw [hn1] at this; omega
      rw [hb1]
      have := strat_le_of_not hS (row_out hell hS p).1
      omega
  · have hL : coarseShift p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2 ∈ (geomOf ell k S).Lam (p.1 : ℕ) := by
      rcases p.2.2.1 with h1 | h1
      · exact absurd h1 hu.2
      · exact h1
    exact strat_of_block hell hS hj hL hb

/-- the kernel lives on bonds touching `Ω₀` (so `Eflat` maps into `E₀`). -/
theorem phi_supp (hell : 0 < ell) (hS : Admissible ell M R k S) (p : BIdx (geomOf ell k S))
    (b : Bond (scaleUp ell k Lu)) (h : phiK hell p b ≠ 0) : b ∈ bondsOm0 (geomOf ell k S) := by
  have hj : (p.1 : ℕ) ≤ k := Nat.lt_succ_iff.mp p.1.isLt
  obtain ⟨hdir, hs⟩ := phi_support hell p b h
  have hom : ∀ {y s : PeriodicLatticeSite (scaleUp ell k Lu)}, y ∈ (geomOf ell k S).Lam (p.1 : ℕ) →
      s ∈ blockOf y (ell ^ (p.1 : ℕ)) → s ∈ S.Om 0 := by
    intro y s hy hb
    exact ((AdalyFormal.M1Site.properTower_geomOf hell hS).cover s).mpr ⟨(p.1 : ℕ), hj, y, hy, hb⟩
  rcases hs with ⟨hu, hb⟩ | ⟨hu, hb⟩
  · by_cases hL : p.2.1.1 ∈ (geomOf ell k S).Lam (p.1 : ℕ)
    · exact Or.inl (hom hL hb)
    · have hj0 : (p.1 : ℕ) = 0 := by
        by_contra hne; exact hu ⟨Nat.one_le_iff_ne_zero.mpr hne, hL⟩
      have hn1 : ell ^ (p.1 : ℕ) = 1 := by rw [hj0, pow_zero]
      have hb1 : b.1 = p.2.1.1 := by
        funext μ; apply Fin.ext
        have := (mem_blockOf.mp hb) μ
        rw [hn1] at this; omega
      have hup : coarseShift p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2 ∈ (geomOf ell k S).Lam (p.1 : ℕ) := by
        rcases p.2.2.1 with h1 | h1
        · exact absurd h1 hL
        · exact h1
      right
      have e : periodicLatticeShift b.1 b.2 = coarseShift p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2 := by
        rw [hb1, hdir, hn1]; rfl
      rw [e]
      exact hom hup (by
        rw [mem_blockOf]; intro μ; exact ⟨le_rfl, by have := pow_pos hell (p.1 : ℕ); omega⟩)
  · have hL : coarseShift p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2 ∈ (geomOf ell k S).Lam (p.1 : ℕ) := by
      rcases p.2.2.1 with h1 | h1
      · exact absurd h1 hu.2
      · exact h1
    exact Or.inl (hom hL hb)

/-- the flat bond right inverse candidate `E y = Σ_p phiK p • y_p` -/
noncomputable def EflatL (hell : 0 < ell) : FSp (geomOf ell k S) →ₗ[ℝ] BondFnL2 (scaleUp ell k Lu) where
  toFun y := WithLp.toLp 2 (fun b => ∑ p, phiK hell p b • (WithLp.ofLp y) p)
  map_add' y y' := by
    refine PiLp.ext (fun b => ?_)
    simp [smul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    refine PiLp.ext (fun b => ?_)
    simp [Finset.smul_sum, smul_smul, mul_comm]

theorem EflatL_apply (hell : 0 < ell) (y : FSp (geomOf ell k S)) (b : Bond (scaleUp ell k Lu)) :
    (EflatL hell y) b = ∑ p, phiK hell p b • y p := rfl

theorem EflatL_mem (hell : 0 < ell) (hS : Admissible ell M R k S) (y : FSp (geomOf ell k S)) :
    EflatL hell y ∈ bondSupp (geomOf ell k S) := by
  intro b hb
  rw [EflatL_apply]
  refine Finset.sum_eq_zero (fun p _ => ?_)
  by_cases h : phiK hell p b = 0
  · rw [h, zero_smul]
  · exact absurd (phi_supp hell hS p b h) hb

/-- the row-matrix of `Q₁ E` -/
noncomputable def kap (hell : 0 < ell) (p' p : BIdx (geomOf ell k S)) : ℝ :=
  (1 / ((ell ^ (p'.1 : ℕ) : ℕ) : ℝ) ^ 4) * ∑ x ∈ blockOf p'.2.1.1 (ell ^ (p'.1 : ℕ)),
    ∑ i ∈ range (ell ^ (p'.1 : ℕ)), phiK hell p (pathSite x p'.2.1.2 i, p'.2.1.2)

/-- **`Q₁ (E y) = K y`** row by row -/
theorem Qflat_E (hell : 0 < ell) (y : FSp (geomOf ell k S)) (p' : BIdx (geomOf ell k S)) :
    (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull (EflatL hell y) p' = ∑ p, kap hell p' p • y p := by
  rw [Qflat_row hell]
  unfold lineCoarseRestrictSuTwo kap
  simp only [rowCB]
  have h1 : ∀ x : PeriodicLatticeSite (scaleUp ell k Lu), ∀ i : ℕ,
      (WithLp.ofLp (EflatL hell y)) (pathSite x p'.2.1.2 i, p'.2.1.2)
        = ∑ p, phiK hell p (pathSite x p'.2.1.2 i, p'.2.1.2) • y p := fun x i => rfl
  simp only [h1]
  have h2 : ∑ x ∈ blockOf p'.2.1.1 (ell ^ (p'.1 : ℕ)), ∑ i ∈ range (ell ^ (p'.1 : ℕ)),
      ∑ p, phiK hell p (pathSite x p'.2.1.2 i, p'.2.1.2) • y p
      = ∑ p, (∑ x ∈ blockOf p'.2.1.1 (ell ^ (p'.1 : ℕ)), ∑ i ∈ range (ell ^ (p'.1 : ℕ)),
          phiK hell p (pathSite x p'.2.1.2 i, p'.2.1.2)) • y p := by
    simp only [Finset.sum_smul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_comm]
  rw [h2, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [smul_smul]

/-- `kap` vanishes when the row reads none of the kernel -/
theorem kap_zero_of (hell : 0 < ell) (p' p : BIdx (geomOf ell k S))
    (h : ∀ x ∈ blockOf p'.2.1.1 (ell ^ (p'.1 : ℕ)), ∀ i < ell ^ (p'.1 : ℕ),
      phiK hell p (pathSite x p'.2.1.2 i, p'.2.1.2) = 0) : kap hell p' p = 0 := by
  unfold kap
  rw [Finset.sum_eq_zero (fun x hx => Finset.sum_eq_zero (fun i hi => h x hx i (mem_range.mp hi))), mul_zero]

/-- a nonzero `kap` exhibits a read bond carrying the kernel -/
theorem kap_ne (hell : 0 < ell) {p' p : BIdx (geomOf ell k S)} (h : kap hell p' p ≠ 0) :
    ∃ x ∈ blockOf p'.2.1.1 (ell ^ (p'.1 : ℕ)), ∃ i < ell ^ (p'.1 : ℕ),
      phiK hell p (pathSite x p'.2.1.2 i, p'.2.1.2) ≠ 0 := by
  by_contra hall
  push Not at hall
  exact h (kap_zero_of hell p' p hall)

/-- **same level: `kap p' p = [p = p']`** -/
theorem kap_same (hell : 0 < ell) (hell2 : 2 ≤ ell) (p' p : BIdx (geomOf ell k S)) (hl : (p.1 : ℕ) = (p'.1 : ℕ)) :
    kap hell p' p = if p = p' then 1 else 0 := by
  classical
  obtain ⟨j, b, hb⟩ := p
  obtain ⟨j', b', hb'⟩ := p'
  have hjj : j = j' := Fin.ext hl
  subst hjj
  have hn : 0 < ell ^ (j : ℕ) := pow_pos hell _
  have hpp : (⟨j, ⟨b, hb⟩⟩ : BIdx (geomOf ell k S)) = ⟨j, ⟨b', hb'⟩⟩ ↔ b = b' := by
    constructor
    · intro h
      have := Sigma.mk.inj_iff.mp h
      have h2 := eq_of_heq this.2
      exact congrArg Subtype.val h2
    · intro h; subst h; rfl
  have hrow : rowCB hell (⟨j, ⟨b, hb⟩⟩ : BIdx (geomOf ell k S))
      = (⟨b'.1, AdalyFormal.M1IMS.row_aligned hell ⟨j, ⟨b', hb'⟩⟩⟩, b'.2) ↔ b = b' := by
    simp only [rowCB]
    constructor
    · intro h
      have h1 := congrArg (fun c => c.1.1) h
      have h2 := congrArg (fun c => c.2) h
      simp only at h1 h2
      exact Prod.ext h1 h2
    · intro h; subst h; rfl
  have hn4 : ((ell ^ (j : ℕ) : ℕ) : ℝ) ^ 4 ≠ 0 := by positivity
  unfold kap phiK
  by_cases hu : useUp (⟨j, ⟨b, hb⟩⟩ : BIdx (geomOf ell k S))
  · have hj1 : 1 ≤ (j : ℕ) := hu.1
    have hn2 : 2 ≤ ell ^ (j : ℕ) := le_trans hell2 (by
      calc ell = ell ^ 1 := (pow_one ell).symm
        _ ≤ ell ^ (j : ℕ) := Nat.pow_le_pow_right (by omega) hj1)
    simp only [if_pos hu]
    rw [block_line_sum_gen (AdalyFormal.W6.uprof (ell ^ (j : ℕ))) (pprof (ell ^ (j : ℕ))) (ell ^ (j : ℕ)) hn
      (hdvdL hell ⟨j, ⟨b', hb'⟩⟩) (AdalyFormal.W6.uprof_eq_zero _) (pprof_eq_zero _) (pprof_sum _) b'.1
      (AdalyFormal.M1IMS.row_aligned hell ⟨j, ⟨b', hb'⟩⟩) b'.2]
    rw [AdalyFormal.W6.uprof_own _ hn2, AdalyFormal.W6.uprof_nxt _ hn2]
    have hup : cbUp (ell ^ (j : ℕ)) (hdvdL hell ⟨j, ⟨b, hb⟩⟩) (rowCB hell ⟨j, ⟨b, hb⟩⟩)
        = cbUp (ell ^ (j : ℕ)) (hdvdL hell ⟨j, ⟨b', hb'⟩⟩)
            (⟨b'.1, AdalyFormal.M1IMS.row_aligned hell ⟨j, ⟨b', hb'⟩⟩⟩, b'.2) ↔ b = b' := by
      constructor
      · intro h
        exact hrow.mp (cbUp_inj _ h)
      · intro h; subst h; rfl
    by_cases hbb : b = b'
    · rw [if_pos (hup.mpr hbb), if_pos (hpp.mpr hbb)]
      simp only [mul_zero, ite_self, zero_add]
      field_simp
    · rw [if_neg (fun h => hbb (hup.mp h)), if_neg (fun h => hbb (hpp.mp h))]
      simp
  · simp only [if_neg hu]
    rw [block_line_sum_gen (tprof (ell ^ (j : ℕ))) (pprof (ell ^ (j : ℕ))) (ell ^ (j : ℕ)) hn
      (hdvdL hell ⟨j, ⟨b', hb'⟩⟩) (tprof_eq_zero _) (pprof_eq_zero _) (pprof_sum _) b'.1
      (AdalyFormal.M1IMS.row_aligned hell ⟨j, ⟨b', hb'⟩⟩) b'.2]
    rw [AdalyFormal.W6.tprof_own _, AdalyFormal.W6.tprof_nxt _]
    by_cases hbb : b = b'
    · rw [if_pos (hrow.mpr hbb), if_pos (hpp.mpr hbb)]
      simp only [mul_zero, ite_self, add_zero]
      field_simp
    · rw [if_neg (fun h => hbb (hrow.mp h)), if_neg (fun h => hbb (hpp.mp h))]
      simp

/-- **higher-level kernels are invisible to lower rows** -/
theorem kap_low (hell : 0 < ell) (hS : Admissible ell M R k S) (p' p : BIdx (geomOf ell k S))
    (hl : (p'.1 : ℕ) < (p.1 : ℕ)) : kap hell p' p = 0 := by
  refine kap_zero_of hell p' p (fun x hx i hi => ?_)
  by_contra hne
  have h1 : AdalyFormal.M1.strat S k (pathSite x p'.2.1.2 i) = (p.1 : ℕ) := phi_strat hell hS p _ hne
  have h2 := read_strat_le hell hS p' hx hi
  omega

/-- **kernels two or more levels down are invisible (collar, `4ℓ ≤ R`)** -/
theorem kap_far (hell : 0 < ell) (hS : Admissible ell M R k S) (hM : 1 ≤ M) (hR : 4 * ell ≤ R)
    (p' p : BIdx (geomOf ell k S)) (hl : (p.1 : ℕ) + 2 ≤ (p'.1 : ℕ)) : kap hell p' p = 0 := by
  refine kap_zero_of hell p' p (fun x hx i hi => ?_)
  by_contra hne
  have hlk : (p'.1 : ℕ) ≤ k := Nat.lt_succ_iff.mp p'.1.isLt
  have h1 : AdalyFormal.M1.strat S k (pathSite x p'.2.1.2 i) = (p.1 : ℕ) := phi_strat hell hS p _ hne
  obtain ⟨a, haL, had⟩ := read_anchor hell p' hx hi
  have haO := (lam_strat hell hS hlk haL).1
  have hsn : pathSite x p'.2.1.2 i ∉ S.Om ((p'.1 : ℕ) - 1) := not_om_of_strat_lt hS (by omega) (by omega)
  have haO' : a ∈ S.Om (((p'.1 : ℕ) - 1) + 1) := by rw [Nat.sub_add_cancel (by omega)]; exact haO
  have hc := AdalyFormal.M1.collar hS (j := (p'.1 : ℕ) - 1) (by omega) hsn haO'
  rw [pdist_comm] at hc
  unfold bigSide at hc
  have hpow : ell ^ (p'.1 : ℕ) = ell * ell ^ ((p'.1 : ℕ) - 1) := by rw [← pow_succ']; congr 1; omega
  have hb : 4 * ell ^ (p'.1 : ℕ) ≤ R * (M * ell ^ ((p'.1 : ℕ) - 1)) := by
    rw [hpow]
    calc 4 * (ell * ell ^ ((p'.1 : ℕ) - 1)) = (4 * ell) * ell ^ ((p'.1 : ℕ) - 1) := by ring
      _ ≤ R * ell ^ ((p'.1 : ℕ) - 1) := Nat.mul_le_mul_right _ hR
      _ ≤ R * (M * ell ^ ((p'.1 : ℕ) - 1)) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hM)
  omega

/-- **no two consecutive interface steps (collar, `8ℓ ≤ R`)** -/
theorem kap_N2 (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 1 ≤ M) (hR : 8 * ell ≤ R)
    (p'' p' p : BIdx (geomOf ell k S)) (h1 : (p'.1 : ℕ) + 1 = (p''.1 : ℕ)) (h2 : (p.1 : ℕ) + 1 = (p'.1 : ℕ)) :
    kap hell p'' p' = 0 ∨ kap hell p' p = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hB⟩ := hcon
  have hlk : (p''.1 : ℕ) ≤ k := Nat.lt_succ_iff.mp p''.1.isLt
  have hn : 0 < ell ^ (p'.1 : ℕ) := pow_pos hell _
  -- the read of row p' carrying the level-(l-1) kernel
  obtain ⟨x, hx, i, hi, ht⟩ := kap_ne hell hB
  have hts : AdalyFormal.M1.strat S k (pathSite x p'.2.1.2 i) = (p.1 : ℕ) := phi_strat hell hS p _ ht
  -- the read of row p'' carrying the level-l kernel of p'
  obtain ⟨x', hx', i', hi', hs⟩ := kap_ne hell hA
  obtain ⟨-, hsb⟩ := phi_support hell p' _ hs
  have hzz : pdist p'.2.1.1 (coarseShift p'.2.1.1 (ell ^ (p'.1 : ℕ)) p'.2.1.2) ≤ ell ^ (p'.1 : ℕ) :=
    pdist_coarseShift_le p'.2.1.1 (ell ^ (p'.1 : ℕ)) p'.2.1.2
  have ht' : pdist p'.2.1.1 (pathSite x p'.2.1.2 i) ≤ 4 * ell ^ (p'.1 : ℕ) := by
    rcases reads_site hn (hdvdL hell p') (rowCB hell p') hx hi with h | h
    · have : pdist p'.2.1.1 (pathSite x p'.2.1.2 i) ≤ 3 * ell ^ (p'.1 : ℕ) := pdist_block_le h
      omega
    · have : pdist (coarseShift p'.2.1.1 (ell ^ (p'.1 : ℕ)) p'.2.1.2) (pathSite x p'.2.1.2 i)
          ≤ 3 * ell ^ (p'.1 : ℕ) := pdist_block_le h
      have := pdist_triangle p'.2.1.1 (coarseShift p'.2.1.1 (ell ^ (p'.1 : ℕ)) p'.2.1.2) (pathSite x p'.2.1.2 i)
      omega
  have hs' : pdist p'.2.1.1 (pathSite x' p''.2.1.2 i') ≤ 4 * ell ^ (p'.1 : ℕ) := by
    rcases hsb with ⟨-, h⟩ | ⟨-, h⟩
    · have : pdist p'.2.1.1 (pathSite x' p''.2.1.2 i') ≤ 3 * ell ^ (p'.1 : ℕ) := pdist_block_le h
      omega
    · have : pdist (coarseShift p'.2.1.1 (ell ^ (p'.1 : ℕ)) p'.2.1.2) (pathSite x' p''.2.1.2 i')
          ≤ 3 * ell ^ (p'.1 : ℕ) := pdist_block_le h
      have := pdist_triangle p'.2.1.1 (coarseShift p'.2.1.1 (ell ^ (p'.1 : ℕ)) p'.2.1.2) (pathSite x' p''.2.1.2 i')
      omega
  have hts' : pdist (pathSite x p'.2.1.2 i) (pathSite x' p''.2.1.2 i') ≤ 8 * ell ^ (p'.1 : ℕ) := by
    have := pdist_triangle (pathSite x p'.2.1.2 i) p'.2.1.1 (pathSite x' p''.2.1.2 i')
    rw [pdist_comm (pathSite x p'.2.1.2 i) p'.2.1.1] at this; omega
  -- the anchor of row p''
  obtain ⟨a, haL, had⟩ := read_anchor hell p'' hx' hi'
  have haO := (lam_strat hell hS hlk haL).1
  have haO' : a ∈ S.Om ((p'.1 : ℕ) + 1) := by rw [h1]; exact haO
  have had' : pdist a (pathSite x' p''.2.1.2 i') ≤ 4 * ell ^ ((p'.1 : ℕ) + 1) := by rw [h1]; exact had
  have htn : pathSite x p'.2.1.2 i ∉ S.Om (p'.1 : ℕ) := not_om_of_strat_lt hS (by omega) (by omega)
  have hc := AdalyFormal.M1.collar hS (j := (p'.1 : ℕ)) (by omega) htn haO'
  unfold bigSide at hc
  have htot : pdist (pathSite x p'.2.1.2 i) a ≤ 8 * ell ^ (p'.1 : ℕ) + 4 * ell ^ ((p'.1 : ℕ) + 1) := by
    have := pdist_triangle (pathSite x p'.2.1.2 i) (pathSite x' p''.2.1.2 i') a
    rw [pdist_comm (pathSite x' p''.2.1.2 i') a] at this; omega
  have hpow : ell ^ ((p'.1 : ℕ) + 1) = ell * ell ^ (p'.1 : ℕ) := by rw [pow_succ']
  have hb : 8 * ell ^ (p'.1 : ℕ) + 4 * ell ^ ((p'.1 : ℕ) + 1) ≤ R * (M * ell ^ (p'.1 : ℕ)) := by
    rw [hpow]
    have h8 : 8 * ell ^ (p'.1 : ℕ) + 4 * (ell * ell ^ (p'.1 : ℕ)) ≤ (8 * ell) * ell ^ (p'.1 : ℕ) := by nlinarith
    calc 8 * ell ^ (p'.1 : ℕ) + 4 * (ell * ell ^ (p'.1 : ℕ)) ≤ (8 * ell) * ell ^ (p'.1 : ℕ) := h8
      _ ≤ R * ell ^ (p'.1 : ℕ) := Nat.mul_le_mul_right _ hR
      _ ≤ R * (M * ell ^ (p'.1 : ℕ)) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hM)
  omega

/-- **`kap − I` is nilpotent of order two**: `Σ_{p'} kap p'' p' kap p' p = 2 kap p'' p − [p'' = p]`. -/
theorem kap_sq (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 1 ≤ M) (hR : 8 * ell ≤ R)
    (p'' p : BIdx (geomOf ell k S)) :
    ∑ p', kap hell p'' p' * kap hell p' p = 2 * kap hell p'' p - (if p'' = p then 1 else 0) := by
  classical
  have hR4 : 4 * ell ≤ R := by omega
  have hNlev : ∀ a b : BIdx (geomOf ell k S), kap hell a b - (if b = a then 1 else 0) ≠ 0 →
      (b.1 : ℕ) + 1 = (a.1 : ℕ) := by
    intro a b hne
    rcases lt_trichotomy (b.1 : ℕ) (a.1 : ℕ) with hlt | heq | hgt
    · by_contra hne'
      apply hne
      have hfar := kap_far hell hS hM hR4 a b (by omega)
      have hba : b ≠ a := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
      rw [hfar, if_neg hba, sub_zero]
    · exfalso; apply hne
      rw [kap_same hell hell2 a b heq, sub_self]
    · exfalso; apply hne
      have hba : b ≠ a := fun h => by rw [h] at hgt; exact lt_irrefl _ hgt
      rw [kap_low hell hS a b hgt, if_neg hba, sub_zero]
  have hNN : ∀ p', (kap hell p'' p' - (if p' = p'' then 1 else 0)) * (kap hell p' p - (if p = p' then 1 else 0)) = 0 := by
    intro p'
    by_contra hne
    have hA := left_ne_zero_of_mul hne
    have hB := right_ne_zero_of_mul hne
    have h1 := hNlev p'' p' hA
    have h2 := hNlev p' p hB
    have hne1 : p' ≠ p'' := fun h => by rw [h] at h1; omega
    have hne2 : p ≠ p' := fun h => by rw [h] at h2; omega
    rw [if_neg hne1, sub_zero] at hA
    rw [if_neg hne2, sub_zero] at hB
    rcases kap_N2 hell hell2 hS hM hR p'' p' p h1 h2 with h | h
    · exact hA h
    · exact hB h
  have hsum : ∑ p', (kap hell p'' p' - (if p' = p'' then 1 else 0)) * (kap hell p' p - (if p = p' then 1 else 0)) = 0 :=
    Finset.sum_eq_zero (fun p' _ => hNN p')
  have hexp : ∀ p', (kap hell p'' p' - (if p' = p'' then 1 else 0)) * (kap hell p' p - (if p = p' then 1 else 0))
      = kap hell p'' p' * kap hell p' p
        - ((if p' = p'' then 1 else 0) * kap hell p' p + kap hell p'' p' * (if p = p' then 1 else 0))
        + (if p' = p'' then 1 else 0) * (if p = p' then 1 else 0) := by
    intro p'; ring
  rw [Finset.sum_congr rfl (fun p' _ => hexp p'), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib] at hsum
  have e1 : ∑ p', (if p' = p'' then (1 : ℝ) else 0) * kap hell p' p = kap hell p'' p := by
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ p'']
    simp
  have e2 : ∑ p', kap hell p'' p' * (if p = p' then (1 : ℝ) else 0) = kap hell p'' p := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ p]
    simp
  have e3 : ∑ p', (if p' = p'' then (1 : ℝ) else 0) * (if p = p' then 1 else 0) = if p'' = p then 1 else 0 := by
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ p'']
    simp only [mem_univ, if_true]
    by_cases h : p'' = p
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  rw [e1, e2, e3] at hsum
  linarith

end kernel

end AdalyFormal.W6

#print axioms AdalyFormal.W6.coarseShift_inj
#print axioms AdalyFormal.W6.cbUp_inj
#print axioms AdalyFormal.W6.useUp
#print axioms AdalyFormal.W6.phiK
#print axioms AdalyFormal.W6.phi_support
#print axioms AdalyFormal.W6.phi_strat
#print axioms AdalyFormal.W6.phi_supp
#print axioms AdalyFormal.W6.EflatL
#print axioms AdalyFormal.W6.EflatL_apply
#print axioms AdalyFormal.W6.EflatL_mem
#print axioms AdalyFormal.W6.kap
#print axioms AdalyFormal.W6.Qflat_E
#print axioms AdalyFormal.W6.kap_zero_of
#print axioms AdalyFormal.W6.kap_ne
#print axioms AdalyFormal.W6.kap_same
#print axioms AdalyFormal.W6.kap_low
#print axioms AdalyFormal.W6.kap_far
#print axioms AdalyFormal.W6.kap_N2
#print axioms AdalyFormal.W6.kap_sq
