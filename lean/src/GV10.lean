import GV9

/-!
# GV10 -- preparing the six class-cube charts: flattening at a base point and local flatness (m2_glue3, 2026-10-15)

* raw chart domains `Hraw R σ b = Box(R+2) ∩ H_{σ,b}`; base points `baseP σ b` (`0`, resp. `−2 e_σ`);
* `flA`: `flatten` (GG8) of the raw chart at its base point with affine coordinates `phiA` (GV1 `coord`);
* `flat_prepared`: a chart on `lift Hraw` at `(·, s)` whose three bonds at the base point are `1` satisfies
  `|G(p,ν) − 1| ≤ 4 ρ(p) s` on `Hd R σ b = Box(R+1) ∩ H_{σ,b}` (explicit walks, `bond_growth`).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M2Glue3

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.M2Glue2
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 coe_mul coe_inv)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

variable {L : PeriodicLatticeExtent}

def Hraw (R : ℕ) (σ : Fin 3) (b : Bool) : Set Z3 := {p | p ∈ Box (R + 2) ∧ hsP σ b p}

def baseP (σ : Fin 3) (b : Bool) : Z3 := fun i => if b = false ∧ i = σ then -2 else 0

theorem baseP_abs (σ : Fin 3) (b : Bool) (i : Fin 3) : |baseP σ b i| ≤ 2 := by
  unfold baseP; split_ifs <;> norm_num

theorem baseP_hs (σ : Fin 3) (b : Bool) (μ : Fin 3) : hsP σ b (baseP σ b) ∧ hsP σ b (baseP σ b + ev μ) := by
  unfold hsP baseP ev
  cases b <;> simp <;> split_ifs <;> omega

theorem baseP_mem {R : ℕ} (hR : 1 ≤ R) (σ : Fin 3) (b : Bool) :
    baseP σ b ∈ Hraw R σ b ∧ ∀ μ, baseP σ b + ev μ ∈ Hraw R σ b := by
  have hb : ∀ i, |baseP σ b i| ≤ 2 := baseP_abs σ b
  refine ⟨⟨fun i => (hb i).trans (by push_cast; omega), (baseP_hs σ b 0).1⟩, fun μ => ⟨fun i => ?_, (baseP_hs σ b μ).2⟩⟩
  have := ev_abs μ i; have := hb i
  simp only [Pi.add_apply]
  calc |baseP σ b i + ev μ i| ≤ |baseP σ b i| + |ev μ i| := abs_add_le _ _
    _ ≤ ((R + 2 : ℕ) : ℤ) := by push_cast; omega

noncomputable def phiA (v : PeriodicLatticeSite L) (R : ℕ) (σ : Fin 3) (b : Bool) :
    Fin 3 → PeriodicLatticeSite L → ℝ :=
  fun σ' x => ((coord v (R + 2) x σ' : ℤ) : ℝ) - ((baseP σ b σ' : ℤ) : ℝ)

theorem affine_phiA {v : PeriodicLatticeSite L} {R : ℕ} (hinj : Set.InjOn (iota v) (Box (R + 3))) (σ : Fin 3)
    (b : Bool) : AffineOn (lift v (Hraw R σ b)) (phiA v R σ b) := by
  have hinj2 : Set.InjOn (iota v) (Box (R + 2)) := hinj.mono (Box_mono (Nat.le_succ _))
  intro x μ hx hxμ σ'
  obtain ⟨p, rfl, hp, hpμ⟩ := bond_lift (Rb := R + 2) hinj (fun _ h => h.1) hx hxμ
  unfold phiA
  rw [iota_shift, coord_iota hinj2 hp.1, coord_iota hinj2 hpμ.1]
  simp only [Pi.add_apply, ev]
  by_cases h : σ' = μ
  · subst h; simp; ring
  · simp [h, Ne.symm h]

theorem phiA_base {v : PeriodicLatticeSite L} {R : ℕ} (hinj : Set.InjOn (iota v) (Box (R + 3))) (hR : 1 ≤ R)
    (σ : Fin 3) (b : Bool) (σ' : Fin 3) : phiA v R σ b σ' (iota v (baseP σ b)) = 0 := by
  have hinj2 : Set.InjOn (iota v) (Box (R + 2)) := hinj.mono (Box_mono (Nat.le_succ _))
  unfold phiA
  rw [coord_iota hinj2 (baseP_mem hR σ b).1.1]; ring

noncomputable def flA (U : LinkCfg L) (v : PeriodicLatticeSite L) (R : ℕ)
    (g : Fin 3 → Bool → PeriodicLatticeSite L → SU2) (σ : Fin 3) (b : Bool) : PeriodicLatticeSite L → SU2 :=
  flatten U (g σ b) (iota v (baseP σ b)) (phiA v R σ b)

theorem flA_gchart {U : LinkCfg L} {v : PeriodicLatticeSite L} {R : ℕ} (hinj : Set.InjOn (iota v) (Box (R + 3)))
    (hR : 1 ≤ R) {g : Fin 3 → Bool → PeriodicLatticeSite L → SU2} {t1 t2 : ℝ} (ht1 : 0 ≤ t1) (ht12 : t1 ≤ 2)
    (hg : ∀ σ b, GChart U (g σ b) (lift v (Hraw R σ b)) t1 t2) (σ : Fin 3) (b : Bool) :
    GChart U (flA U v R g σ b) (lift v (Hraw R σ b)) ((11 / 2) * t1) (t2 + 43 * t1 ^ 2) := by
  have hb := baseP_mem hR σ b
  exact flatten_gchart (affine_phiA hinj σ b) ht1 ht12 (hg σ b) (iota_mem_lift hb.1)
    (fun σ' => by rw [iota_shift]; exact iota_mem_lift (hb.2 σ'))

theorem flA_base {U : LinkCfg L} {v : PeriodicLatticeSite L} {R : ℕ} (hinj : Set.InjOn (iota v) (Box (R + 3)))
    (hR : 1 ≤ R) {g : Fin 3 → Bool → PeriodicLatticeSite L → SU2} {t1 t2 : ℝ} (ht12 : t1 ≤ 2)
    (hg : ∀ σ b, GChart U (g σ b) (lift v (Hraw R σ b)) t1 t2) (σ : Fin 3) (b : Bool) (σ' : Fin 3) :
    periodicGaugeTransform (flA U v R g σ b) U (iota v (baseP σ b), σ') = 1 := by
  have hb := baseP_mem hR σ b
  have hy : iota v (baseP σ b) ∈ lift v (Hraw R σ b) := iota_mem_lift hb.1
  have hyσ : periodicLatticeShift (iota v (baseP σ b)) σ' ∈ lift v (Hraw R σ b) := by
    rw [iota_shift]; exact iota_mem_lift (hb.2 σ')
  exact flatten_base (affine_phiA hinj σ b) (phiA_base hinj hR σ b) hy hyσ ((hg σ b).1 _ σ' hy hyσ |>.trans ht12)

/-! ## local flatness -/

/-- the walk region for bonds in direction `ν` inside `H_{σ,b}`. -/
def regLo (R : ℕ) (σ : Fin 3) (b : Bool) : Z3 := fun i => if b = true ∧ i = σ then 0 else -((R : ℤ) + 1)
def regHi (R : ℕ) (σ : Fin 3) (b : Bool) (ν : Fin 3) : Z3 :=
  fun i => if b = false ∧ i = σ then -1 - (if ν = σ then 1 else 0) else (R : ℤ) + 1

theorem reg_raw {R : ℕ} {σ : Fin 3} {b : Bool} {ν : Fin 3} {z : Z3} (i : Fin 3)
    (hz : z ∈ IBox (regLo R σ b) (regHi R σ b ν)) (hzi : z + ev i ∈ IBox (regLo R σ b) (regHi R σ b ν)) :
    z ∈ Hraw R σ b ∧ z + ev ν ∈ Hraw R σ b ∧ z + ev i ∈ Hraw R σ b ∧ z + ev i + ev ν ∈ Hraw R σ b := by
  have box : ∀ w : Z3, w ∈ IBox (regLo R σ b) (regHi R σ b ν) → ∀ j, |w j| ≤ (R : ℤ) + 1 := by
    intro w hw j
    have := hw j
    unfold regLo regHi at this
    rw [abs_le]
    split_ifs at this <;> constructor <;> omega
  have hsv : ∀ w : Z3, w ∈ IBox (regLo R σ b) (regHi R σ b ν) → hsP σ b w ∧ hsP σ b (w + ev ν) := by
    intro w hw
    have := hw σ
    unfold regLo regHi at this
    unfold hsP
    simp only [Pi.add_apply, ev]
    cases b <;> simp at this ⊢ <;> split_ifs at this ⊢ <;> omega
  have bx : ∀ w : Z3, (∀ j, |w j| ≤ (R : ℤ) + 1) → ∀ μ, w ∈ Box (R + 2) ∧ w + ev μ ∈ Box (R + 2) := by
    intro w hw μ
    refine ⟨fun j => ?_, fun j => ?_⟩
    · have := hw j; push_cast; omega
    · have := hw j; have := ev_abs μ j
      simp only [Pi.add_apply]
      calc |w j + ev μ j| ≤ |w j| + |ev μ j| := abs_add_le _ _
        _ ≤ ((R + 2 : ℕ) : ℤ) := by push_cast; omega
  obtain ⟨a1, a2⟩ := bx z (box z hz) ν
  obtain ⟨c1, c2⟩ := bx (z + ev i) (box _ hzi) ν
  exact ⟨⟨a1, (hsv z hz).1⟩, ⟨a2, (hsv z hz).2⟩, ⟨c1, (hsv _ hzi).1⟩, ⟨c2, (hsv _ hzi).2⟩⟩

theorem target_in_reg {R : ℕ} {σ : Fin 3} {b : Bool} {ν : Fin 3} {p : Z3} (hp : p ∈ Hd R σ b)
    (hpν : p + ev ν ∈ Hd R σ b) : p ∈ IBox (regLo R σ b) (regHi R σ b ν) := by
  intro j
  have a := hp.1 j
  have c := hpν.2
  have c0 := hp.2
  rw [abs_le] at a
  push_cast at a
  unfold regLo regHi
  unfold hsP at c c0
  simp only [Pi.add_apply, ev] at c
  cases b <;> simp at c c0 ⊢ <;> split_ifs at c ⊢ <;> (try subst_vars) <;> omega

theorem base_in_reg {R : ℕ} (hR : 1 ≤ R) (σ : Fin 3) (b : Bool) (ν : Fin 3) :
    baseP σ b ∈ IBox (regLo R σ b) (regHi R σ b ν) := by
  intro j
  unfold regLo regHi baseP
  cases b <;> simp <;> split_ifs <;> omega

theorem flat_prepared {U : LinkCfg L} {v : PeriodicLatticeSite L} {R : ℕ} (hR : 1 ≤ R)
    {G : PeriodicLatticeSite L → SU2} {σ : Fin 3} {b : Bool} {t s : ℝ} (hs : 0 ≤ s)
    (hG : GChart U G (lift v (Hraw R σ b)) t s)
    (hbase : ∀ σ', periodicGaugeTransform G U (iota v (baseP σ b), σ') = 1) :
    ZCh U G v (Hd R σ b) (fun p => 4 * rho p * s) (fun _ => s) := by
  refine ⟨fun p ν hp hpν => ?_, fun p μ ν h0 h1 h2 h3 => ?_⟩
  · have hD : ∀ z i, z ∈ IBox (regLo R σ b) (regHi R σ b ν) → z + ev i ∈ IBox (regLo R σ b) (regHi R σ b ν) →
        iota v z ∈ lift v (Hraw R σ b) ∧ iota v (z + ev ν) ∈ lift v (Hraw R σ b) ∧
        iota v (z + ev i) ∈ lift v (Hraw R σ b) ∧ iota v (z + ev i + ev ν) ∈ lift v (Hraw R σ b) := by
      intro z i hz hzi
      obtain ⟨a, c, d, e⟩ := reg_raw i hz hzi
      exact ⟨iota_mem_lift a, iota_mem_lift c, iota_mem_lift d, iota_mem_lift e⟩
    have fb := flat_bound hG hD (base_in_reg hR σ b ν) (hbase ν) (target_in_reg hp hpν)
    refine fb.trans ?_
    have hl := l1_le p (baseP σ b)
    have hb : |((baseP σ b 0 : ℤ) : ℝ)| + |((baseP σ b 1 : ℤ) : ℝ)| + |((baseP σ b 2 : ℤ) : ℝ)| ≤ 2 := by
      unfold baseP; cases b <;> fin_cases σ <;> simp
    have hρ := rho_ge p
    have : (l1 p (baseP σ b) : ℝ) ≤ 4 * rho p := by linarith
    exact mul_le_mul_of_nonneg_right this hs
  · have hsub : Hd R σ b ⊆ Hraw R σ b := fun q hq => ⟨Box_mono (by omega) hq.1, hq.2⟩
    have := (zch_of_gchart hG).2 p μ ν (hsub h0) (hsub h1) (hsub h2) (hsub h3)
    exact this

end AdalyFormal.M2Glue3
