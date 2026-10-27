import BLC7

/-!
# UZ1 -- link fields on ℤ³, clause-1 charts, and the STACKING lemma (lane unif_20261016)

`gt W G p ν = G p · W p ν · G (p + e_ν)⁻¹` (gauge transform of a link field `W : ℤ³ → Fin 3 → SU(2)`),
`C1 W G S t` : every bond of `S` (both ends in `S`) is within `t` of `1`,
`hol W p μ ν` : the plaquette holonomy.

`stackP` / `stackM` : a chart `Go` on `O` and a chart `Gn` on `N`, with `N` attached to `O` across ONE direction `σ`
(above / below), columns of `N` projecting by `b` onto the interface: the gauge `κ · Gn` on `N`
(`κ` constant along `σ`, chosen so that every crossing bond is exactly `1`) and `Go` on `O` is a chart on `O ∪ N`
with constant `tO + 2 tN + η`, where `η` bounds the holonomies of the interface plaquettes.  No `M`, no smallness.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.UnifLane.Z

open AdalyFormal.M2Glue3 (Z3 ev)
open AdalyFormal.M2BallCharts (su2_mul_sub_one su2_inv_sub_one)
open AdalyFormal.M2Glue2 (frobNorm_conj_sub_one)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

/-- gauge transform of a link field on `ℤ³`. -/
def gt (W : Z3 → Fin 3 → SU2) (G : Z3 → SU2) (p : Z3) (ν : Fin 3) : SU2 := G p * W p ν * (G (p + ev ν))⁻¹

/-- clause-1 chart: every bond with both ends in `S` is within `t` of `1`. -/
def C1 (W : Z3 → Fin 3 → SU2) (G : Z3 → SU2) (S : Set Z3) (t : ℝ) : Prop :=
  ∀ p ν, p ∈ S → p + ev ν ∈ S → frobNorm (((gt W G p ν : SU2) : M2) - 1) ≤ t

/-- plaquette holonomy. -/
def hol (W : Z3 → Fin 3 → SU2) (p : Z3) (μ ν : Fin 3) : SU2 :=
  W p μ * W (p + ev μ) ν * (W (p + ev ν) μ)⁻¹ * (W p ν)⁻¹

theorem C1.mono {W : Z3 → Fin 3 → SU2} {G : Z3 → SU2} {S S' : Set Z3} {t t' : ℝ} (h : C1 W G S t) (hS : S' ⊆ S)
    (ht : t ≤ t') : C1 W G S' t' :=
  fun p ν a b => (h p ν (hS a) (hS b)).trans ht

/-! ## norm facts -/

theorem n_conj (C A : SU2) : frobNorm (((C * A * C⁻¹ : SU2) : M2) - 1) = frobNorm (((A : SU2) : M2) - 1) :=
  frobNorm_conj_sub_one C A

theorem n_inv (A : SU2) : frobNorm (((A⁻¹ : SU2) : M2) - 1) = frobNorm (((A : SU2) : M2) - 1) :=
  su2_inv_sub_one A

theorem n_mul (A B : SU2) : frobNorm (((A * B : SU2) : M2) - 1) ≤ frobNorm (((A : SU2) : M2) - 1) + frobNorm (((B : SU2) : M2) - 1) :=
  su2_mul_sub_one A B

/-- `|κ A κ'⁻¹ − 1| ≤ |A − 1| + |κ⁻¹ κ' − 1|`. -/
theorem n_twist (κ κ' A : SU2) :
    frobNorm (((κ * A * κ'⁻¹ : SU2) : M2) - 1) ≤ frobNorm (((A : SU2) : M2) - 1) + frobNorm (((κ⁻¹ * κ' : SU2) : M2) - 1) := by
  have e : κ * A * κ'⁻¹ = (κ * A * κ⁻¹) * (κ * (κ⁻¹ * κ')⁻¹ * κ⁻¹) := by group
  rw [e]
  refine (n_mul _ _).trans ?_
  rw [n_conj, n_conj, n_inv]

/-- the gauge transform of a product gauge. -/
theorem gt_mul (W : Z3 → Fin 3 → SU2) (κ G : Z3 → SU2) (p : Z3) (ν : Fin 3) :
    gt W (fun q => κ q * G q) p ν = κ p * gt W G p ν * (κ (p + ev ν))⁻¹ := by
  simp only [gt]; group

theorem ev_sub_add (q : Z3) (σ : Fin 3) : q + ev σ - ev σ = q := by abel
theorem sub_add_ev (q : Z3) (σ : Fin 3) : q - ev σ + ev σ = q := by abel

/-! ## stacking above (`N` on the `+σ` side of the interface) -/

theorem stackP (W : Z3 → Fin 3 → SU2) {O N : Set Z3} (σ : Fin 3) {Go Gn : Z3 → SU2} {tO tN η : ℝ}
    (htO : 0 ≤ tO) (htN : 0 ≤ tN) (hη : 0 ≤ η)
    (hO : C1 W Go O tO) (hN : C1 W Gn N tN) (b : Z3 → Z3)
    (hbN : ∀ p ∈ N, b p ∈ N) (hbO : ∀ p ∈ N, b p - ev σ ∈ O)
    (hcol : ∀ p ∈ N, p + ev σ ∈ N → b (p + ev σ) = b p)
    (htr : ∀ p ∈ N, ∀ ν, ν ≠ σ → p + ev ν ∈ N → b (p + ev ν) = b p + ev ν)
    (hcross : ∀ p ∈ O, ∀ ν, p + ev ν ∈ N → ν = σ ∧ b (p + ev σ) = p + ev σ)
    (hno : ∀ p ∈ N, ∀ ν, p + ev ν ∈ O → False)
    (hdisj : ∀ p ∈ N, p ∉ O)
    (hpl : ∀ q ∈ O, ∀ ν, ν ≠ σ → q + ev ν ∈ O → q + ev σ ∈ N → q + ev σ + ev ν ∈ N →
      frobNorm (((hol W q ν σ : SU2) : M2) - 1) ≤ η) :
    ∃ G : Z3 → SU2, C1 W G (O ∪ N) (tO + 2 * tN + η) ∧ ∀ p ∈ O, G p = Go p := by
  classical
  set κ : Z3 → SU2 := fun p => (Go (b p - ev σ) * W (b p - ev σ) σ) * (Gn (b p))⁻¹ with hκ
  set G : Z3 → SU2 := fun p => if p ∈ N then κ p * Gn p else Go p with hG
  have GN : ∀ p ∈ N, G p = κ p * Gn p := fun p hp => by simp [hG, hp]
  have GO : ∀ p ∈ O, G p = Go p := fun p hp => by
    have : p ∉ N := fun h => hdisj p h hp
    simp [hG, this]
  refine ⟨G, ?_, GO⟩
  intro p ν hp hpν
  rcases hp with hpO | hpN
  · rcases hpν with hpνO | hpνN
    · have e : gt W G p ν = gt W Go p ν := by simp only [gt, GO p hpO, GO _ hpνO]
      rw [e]; have := hO p ν hpO hpνO; linarith
    · obtain ⟨rfl, hb⟩ := hcross p hpO ν hpνN
      have e : gt W G p ν = 1 := by
        simp only [gt, GO p hpO, GN _ hpνN, hκ, hb, ev_sub_add]
        group
      rw [e]; simp; positivity
  · rcases hpν with hpνO | hpνN
    · exact (hno p hpN ν hpνO).elim
    · have e : gt W G p ν = κ p * gt W Gn p ν * (κ (p + ev ν))⁻¹ := by
        simp only [gt, GN p hpN, GN _ hpνN]; group
      rw [e]
      by_cases hνσ : ν = σ
      · subst hνσ
        have hk : κ (p + ev ν) = κ p := by simp only [hκ, hcol p hpN hpνN]
        rw [hk, n_conj]
        have := hN p ν hpN hpνN; linarith
      · refine (n_twist _ _ _).trans ?_
        set B := b p with hB
        set q := B - ev σ with hq
        have hqO : q ∈ O := hbO p hpN
        have hBN : B ∈ N := hbN p hpN
        have hb' : b (p + ev ν) = B + ev ν := htr p hpN ν hνσ hpνN
        have hB'N : B + ev ν ∈ N := hb' ▸ hbN _ hpνN
        have hq'O : q + ev ν ∈ O := by
          have := hbO _ hpνN; rw [hb'] at this
          rwa [show B + ev ν - ev σ = q + ev ν by rw [hq]; abel] at this
        have hqσ : q + ev σ = B := by rw [hq]; abel
        have hqνσ : q + ev ν + ev σ = B + ev ν := by rw [← hqσ]; abel
        have hqσν : q + ev σ + ev ν = B + ev ν := by rw [hqσ]
        -- the identity κ(p)⁻¹ κ(p+ν) = C (c A_o⁻¹ c⁻¹ h) C⁻¹ A_n
        have key : (κ p)⁻¹ * κ (p + ev ν) =
            (Gn B * (W q σ)⁻¹) * ((Go q)⁻¹ * (gt W Go q ν)⁻¹ * ((Go q)⁻¹)⁻¹ * hol W q ν σ) * (Gn B * (W q σ)⁻¹)⁻¹
              * gt W Gn B ν := by
          have e1 : κ p = Go q * W q σ * (Gn B)⁻¹ := by simp only [hκ, hB, hq]
          have e2 : κ (p + ev ν) = Go (q + ev ν) * W (q + ev ν) σ * (Gn (B + ev ν))⁻¹ := by
            simp only [hκ, hb']
            rw [show B + ev ν - ev σ = q + ev ν by rw [hq]; abel]
          rw [e1, e2]
          simp only [gt, hol, hqσ]
          group
        rw [key]
        have h2 := n_mul ((Gn B * (W q σ)⁻¹) * ((Go q)⁻¹ * (gt W Go q ν)⁻¹ * ((Go q)⁻¹)⁻¹ * hol W q ν σ) * (Gn B * (W q σ)⁻¹)⁻¹)
          (gt W Gn B ν)
        rw [n_conj] at h2
        have h1 := n_mul ((Go q)⁻¹ * (gt W Go q ν)⁻¹ * ((Go q)⁻¹)⁻¹) (hol W q ν σ)
        rw [n_conj, n_inv] at h1
        have hAo := hO q ν hqO hq'O
        have hh := hpl q hqO ν hνσ hq'O (hqσ ▸ hBN) (hqσν ▸ hB'N)
        have hAn := hN B ν hBN hB'N
        have hA := hN p ν hpN hpνN
        linarith

/-! ## stacking below (`N` on the `-σ` side of the interface) -/

theorem stackM (W : Z3 → Fin 3 → SU2) {O N : Set Z3} (σ : Fin 3) {Go Gn : Z3 → SU2} {tO tN η : ℝ}
    (htO : 0 ≤ tO) (htN : 0 ≤ tN) (hη : 0 ≤ η)
    (hO : C1 W Go O tO) (hN : C1 W Gn N tN) (b : Z3 → Z3)
    (hbN : ∀ p ∈ N, b p ∈ N) (hbO : ∀ p ∈ N, b p + ev σ ∈ O)
    (hcol : ∀ p ∈ N, p + ev σ ∈ N → b (p + ev σ) = b p)
    (htr : ∀ p ∈ N, ∀ ν, ν ≠ σ → p + ev ν ∈ N → b (p + ev ν) = b p + ev ν)
    (hcross : ∀ p ∈ N, ∀ ν, p + ev ν ∈ O → ν = σ ∧ b p = p)
    (hno : ∀ p ∈ O, ∀ ν, p + ev ν ∈ N → False)
    (hdisj : ∀ p ∈ N, p ∉ O)
    (hpl : ∀ B ∈ N, ∀ ν, ν ≠ σ → B + ev ν ∈ N → B + ev σ ∈ O → B + ev ν + ev σ ∈ O →
      frobNorm (((hol W B ν σ : SU2) : M2) - 1) ≤ η) :
    ∃ G : Z3 → SU2, C1 W G (O ∪ N) (tO + 2 * tN + η) ∧ ∀ p ∈ O, G p = Go p := by
  classical
  set κ : Z3 → SU2 := fun p => (Go (b p + ev σ) * (W (b p) σ)⁻¹) * (Gn (b p))⁻¹ with hκ
  set G : Z3 → SU2 := fun p => if p ∈ N then κ p * Gn p else Go p with hG
  have GN : ∀ p ∈ N, G p = κ p * Gn p := fun p hp => by simp [hG, hp]
  have GO : ∀ p ∈ O, G p = Go p := fun p hp => by
    have : p ∉ N := fun h => hdisj p h hp
    simp [hG, this]
  refine ⟨G, ?_, GO⟩
  intro p ν hp hpν
  rcases hp with hpO | hpN
  · rcases hpν with hpνO | hpνN
    · have e : gt W G p ν = gt W Go p ν := by simp only [gt, GO p hpO, GO _ hpνO]
      rw [e]; have := hO p ν hpO hpνO; linarith
    · exact (hno p hpO ν hpνN).elim
  · rcases hpν with hpνO | hpνN
    · obtain ⟨rfl, hb⟩ := hcross p hpN ν hpνO
      have e : gt W G p ν = 1 := by
        simp only [gt, GN p hpN, GO _ hpνO, hκ, hb]
        group
      rw [e]; simp; positivity
    · have e : gt W G p ν = κ p * gt W Gn p ν * (κ (p + ev ν))⁻¹ := by
        simp only [gt, GN p hpN, GN _ hpνN]; group
      rw [e]
      by_cases hνσ : ν = σ
      · subst hνσ
        have hk : κ (p + ev ν) = κ p := by simp only [hκ, hcol p hpN hpνN]
        rw [hk, n_conj]
        have := hN p ν hpN hpνN; linarith
      · refine (n_twist _ _ _).trans ?_
        set B := b p with hB
        set q := B + ev σ with hq
        have hqO : q ∈ O := hbO p hpN
        have hBN : B ∈ N := hbN p hpN
        have hb' : b (p + ev ν) = B + ev ν := htr p hpN ν hνσ hpνN
        have hB'N : B + ev ν ∈ N := hb' ▸ hbN _ hpνN
        have hq'O : q + ev ν ∈ O := by
          have := hbO _ hpνN; rw [hb'] at this
          rwa [show B + ev ν + ev σ = q + ev ν by rw [hq]; abel] at this
        have hq' : B + ev ν + ev σ = q + ev ν := by rw [hq]; abel
        have key : (κ p)⁻¹ * κ (p + ev ν) =
            (Gn B * W B σ) * ((Go q)⁻¹ * (gt W Go q ν)⁻¹ * ((Go q)⁻¹)⁻¹) * (Gn B * W B σ)⁻¹
              * (Gn B * (hol W B ν σ)⁻¹ * (Gn B)⁻¹) * gt W Gn B ν := by
          have e1 : κ p = Go q * (W B σ)⁻¹ * (Gn B)⁻¹ := by simp only [hκ, hB, hq]
          have e2 : κ (p + ev ν) = Go (q + ev ν) * (W (B + ev ν) σ)⁻¹ * (Gn (B + ev ν))⁻¹ := by
            simp only [hκ, hb', hq']
          rw [e1, e2]
          simp only [gt, hol, hq]
          group
        rw [key]
        have h2 := n_mul ((Gn B * W B σ) * ((Go q)⁻¹ * (gt W Go q ν)⁻¹ * ((Go q)⁻¹)⁻¹) * (Gn B * W B σ)⁻¹
          * (Gn B * (hol W B ν σ)⁻¹ * (Gn B)⁻¹)) (gt W Gn B ν)
        have h1 := n_mul ((Gn B * W B σ) * ((Go q)⁻¹ * (gt W Go q ν)⁻¹ * ((Go q)⁻¹)⁻¹) * (Gn B * W B σ)⁻¹)
          (Gn B * (hol W B ν σ)⁻¹ * (Gn B)⁻¹)
        rw [n_conj, n_conj, n_inv, n_conj, n_inv] at h1
        have hAo := hO q ν hqO hq'O
        have hh := hpl B hBN ν hνσ hB'N hqO (hq' ▸ hq'O)
        have hAn := hN B ν hBN hB'N
        have hA := hN p ν hpN hpνN
        linarith

end AdalyFormal.UnifLane.Z
