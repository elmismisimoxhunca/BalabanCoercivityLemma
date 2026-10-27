import D1IVT

/-!
Finite Dirichlet-chain source response.  This is an exact scalar block theorem,
not an identification of the frozen lattice operators or a crossing theorem.
Unlike a fixed-source estimate, it permits the source site to be selected.
-/
set_option autoImplicit false

namespace AdalyFormal.Round10.Nonvanishing.FreeProfile

open Finset

/-- Dirichlet fine Laplacian on interior indices 1 through n. -/
def lap (y : ℕ → ℝ) (i : ℕ) : ℝ := 2 * y (i + 1) - y i - y (i + 2)

/-- Energy including the two exterior Dirichlet edges. -/
def energy (n : ℕ) (y : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range (n + 1), (y (i + 1) - y i) ^ 2

lemma energy_nonneg (n : ℕ) (y : ℕ → ℝ) : 0 ≤ energy n y := by
  exact sum_nonneg fun i _ => sq_nonneg _

/-- Summation by parts, retaining both boundary terms. -/
theorem energy_identity (n : ℕ) (y : ℕ → ℝ) :
    energy n y = (∑ i ∈ range n, y (i + 1) * lap y i) +
      y 0 * (y 0 - y 1) + y (n + 1) * (y (n + 1) - y n) := by
  induction n with
  | zero => simp [energy, lap]; ring
  | succ n ih =>
    unfold energy at ih ⊢
    rw [sum_range_succ, ih, sum_range_succ]
    simp only [lap]
    ring

/-- Zero energy and one zero endpoint force every interior entry to vanish. -/
theorem eq_zero_of_energy_zero (n : ℕ) (y : ℕ → ℝ)
    (hleft : y 0 = 0) (he : energy n y = 0) :
    ∀ k ≤ n + 1, y k = 0 := by
  have hd : ∀ i < n + 1, y (i + 1) = y i := by
    intro i hi
    have hsq : (y (i + 1) - y i) ^ 2 ≤ energy n y :=
      single_le_sum (fun j _ => sq_nonneg (y (j + 1) - y j)) (mem_range.mpr hi)
    have hz : y (i + 1) - y i = 0 := by nlinarith [sq_nonneg (y (i + 1) - y i)]
    linarith
  intro k hk
  induction k with
  | zero => exact hleft
  | succ k ih =>
    rw [hd k (by omega), ih (by omega)]

/-- A nonzero coarse two-site average entails strictly positive fine energy. -/
theorem energy_pos_of_average_ne_zero (n : ℕ) (y b : ℕ → ℝ)
    (hleft : y 0 = 0)
    (havg : ∀ j < n, y (2*j+1) + y (2*j+2) = 2*b j)
    (hne : ∃ j < n, b j ≠ 0) : 0 < energy (2*n) y := by
  apply lt_of_le_of_ne (energy_nonneg _ _)
  intro he
  have hz := eq_zero_of_energy_zero (2*n) y hleft he.symm
  obtain ⟨j, hj, hb⟩ := hne
  have h := havg j hj
  rw [hz (2*j+1) (by omega), hz (2*j+2) (by omega)] at h
  exact hb (by linarith)

lemma sum_pair (n : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ range (2*n), f i) = ∑ j ∈ range n, (f (2*j) + f (2*j+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = (2*n+1)+1 by omega,
      sum_range_succ, sum_range_succ, ih, sum_range_succ]
    ring

/-- Stationarity under opposite changes of the two entries of each block. -/
def Stationary (n : ℕ) (y : ℕ → ℝ) : Prop :=
  ∀ j < n, lap y (2*j) = lap y (2*j+1)

/-- The selected even-site source response of the constrained lift. -/
def response (y : ℕ → ℝ) (j : ℕ) : ℝ := lap y (2*j)

/-- The effective source response has exactly half the fine Dirichlet energy. -/
theorem response_energy (n : ℕ) (y b : ℕ → ℝ)
    (hleft : y 0 = 0) (hright : y (2*n+1) = 0)
    (havg : ∀ j < n, y (2*j+1) + y (2*j+2) = 2*b j)
    (hstat : Stationary n y) :
    2 * (∑ j ∈ range n, b j * response y j) = energy (2*n) y := by
  rw [energy_identity, hleft, hright]
  simp only [zero_mul, add_zero]
  rw [sum_pair, mul_sum]
  apply sum_congr rfl
  intro j hj
  have hs := hstat j (mem_range.mp hj)
  have ha := havg j (mem_range.mp hj)
  simp only [response]
  rw [show 2*j+1+1 = 2*j+2 by omega, ← hs]
  rw [← add_mul, ha]
  ring

/-- No nonzero coarse jet vector is annihilated by every even-site source. -/
theorem response_pos (n : ℕ) (y b : ℕ → ℝ)
    (hleft : y 0 = 0) (hright : y (2*n+1) = 0)
    (havg : ∀ j < n, y (2*j+1) + y (2*j+2) = 2*b j)
    (hstat : Stationary n y) (hne : ∃ j < n, b j ≠ 0) :
    0 < ∑ j ∈ range n, b j * response y j := by
  have hp := energy_pos_of_average_ne_zero n y b hleft havg hne
  have he := response_energy n y b hleft hright havg hstat
  linarith

/-- A single source site already suffices; no bound between different jets is needed. -/
theorem exists_response_ne_zero (n : ℕ) (y b : ℕ → ℝ)
    (hleft : y 0 = 0) (hright : y (2*n+1) = 0)
    (havg : ∀ j < n, y (2*j+1) + y (2*j+2) = 2*b j)
    (hstat : Stationary n y) (hne : ∃ j < n, b j ≠ 0) :
    ∃ j < n, response y j ≠ 0 := by
  by_contra h
  push Not at h
  have hp := response_pos n y b hleft hright havg hstat hne
  have hz : (∑ j ∈ range n, b j * response y j) = 0 := by
    apply sum_eq_zero
    intro j hj
    rw [h j (mem_range.mp hj), mul_zero]
  linarith

/-- Abstract dictionary interface. The actual equality with the source pairing is
separate from the finite-chain theorem, so it cannot silently discharge the dictionary. -/
theorem exists_coupling_ne_zero (n : ℕ) (y b coupling : ℕ → ℝ) (factor : ℝ)
    (hleft : y 0 = 0) (hright : y (2*n+1) = 0)
    (havg : ∀ j < n, y (2*j+1) + y (2*j+2) = 2*b j)
    (hstat : Stationary n y) (hne : ∃ j < n, b j ≠ 0)
    (hfactor : factor ≠ 0)
    (hdict : ∀ j < n, coupling j = factor * response y j) :
    ∃ j < n, coupling j ≠ 0 := by
  obtain ⟨j, hj, hn⟩ := exists_response_ne_zero n y b hleft hright havg hstat hne
  refine ⟨j, hj, ?_⟩
  rw [hdict j hj]
  exact mul_ne_zero hfactor hn

#print axioms lap
#print axioms energy
#print axioms energy_nonneg
#print axioms energy_identity
#print axioms eq_zero_of_energy_zero
#print axioms energy_pos_of_average_ne_zero
#print axioms sum_pair
#print axioms Stationary
#print axioms response
#print axioms response_energy
#print axioms response_pos
#print axioms exists_response_ne_zero
#print axioms exists_coupling_ne_zero

end AdalyFormal.Round10.Nonvanishing.FreeProfile

namespace AdalyFormal.Round10.Nonvanishing.FreeProfile

open Finset

/-- Zero padding of a finite vector to the right. -/
def pad {n : ℕ} (a : Fin n → ℝ) (j : ℕ) : ℝ := if h : j < n then a ⟨j,h⟩ else 0

/-- Left Dirichlet value for block sequences. -/
def prev (a : ℕ → ℝ) (j : ℕ) : ℝ := if j = 0 then 0 else a (j-1)

/-- The exact finite tridiagonal system, with both boundary values zero. -/
def tri (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun a j := 6*a j + prev (pad a) j + pad a ((j : ℕ)+1)
  map_add' a b := by
    funext j
    simp only [Pi.add_apply, prev, pad]
    split_ifs <;> (try simp_all) <;> ring
  map_smul' c a := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, prev, pad]
    split_ifs <;> (try simp_all) <;> ring

lemma pad_abs_le {n : ℕ} (a : Fin n → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ j, |a j| ≤ M) (j : ℕ) : |pad a j| ≤ M := by
  unfold pad
  split_ifs
  · exact h _
  · simpa using hM

/-- Strict diagonal dominance proves injectivity, including all chain lengths. -/
theorem tri_injective (n : ℕ) : Function.Injective (tri n) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  by_cases hn : n = 0
  · subst n
    ext j
    exact Fin.elim0 j
  haveI : NeZero n := ⟨hn⟩
  obtain ⟨k, _, hk⟩ := (univ : Finset (Fin n)).exists_max_image (fun j => |a j|) univ_nonempty
  have hm : ∀ j, |a j| ≤ |a k| := fun j => hk j (mem_univ _)
  have hl : |prev (pad a) k| ≤ |a k| := by
    unfold prev
    split_ifs
    · simp
    · exact pad_abs_le a _ (abs_nonneg _) hm _
  have hr := pad_abs_le a _ (abs_nonneg (a k)) hm ((k : ℕ)+1)
  have he : 6*a k + prev (pad a) k + pad a ((k : ℕ)+1) = 0 := congrFun ha k
  have he' : 6*a k = -(prev (pad a) k + pad a ((k : ℕ)+1)) := by linarith
  have hb : 6*|a k| ≤ |prev (pad a) k| + |pad a ((k : ℕ)+1)| := by
    calc
      6*|a k| = |6*a k| := by rw [abs_mul]; norm_num
      _ = |prev (pad a) k + pad a ((k : ℕ)+1)| := by rw [he', abs_neg]
      _ ≤ _ := abs_add_le _ _
  have hz : |a k| = 0 := by linarith [abs_nonneg (a k)]
  funext j
  exact abs_eq_zero.mp (le_antisymm (by simpa [hz] using hm j) (abs_nonneg _))

/-- Every exact finite tridiagonal right-hand side has a solution. -/
theorem exists_tri_solution (n : ℕ) (r : ℕ → ℝ) :
    ∃ a : ℕ → ℝ, a n = 0 ∧
      ∀ j < n, 6*a j + prev a j + a (j+1) = r j := by
  obtain ⟨a, ha⟩ := (tri n).surjective_of_injective (tri_injective n) (fun j => r j)
  refine ⟨pad a, by simp [pad], ?_⟩
  intro j hj
  have he := congrFun ha ⟨j,hj⟩
  simpa only [tri, LinearMap.coe_mk, AddHom.coe_mk, pad, dif_pos hj] using he

/-- Fine lift of block averages b and alternating block amplitudes a. -/
def blockLift (a b : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k % 2 = 0 then
    (if k = 0 then 0 else b (k/2-1) - a (k/2-1))
  else b (k/2) + a (k/2)

lemma blockLift_zero (a b : ℕ → ℝ) : blockLift a b 0 = 0 := by simp [blockLift]

lemma blockLift_even (a b : ℕ → ℝ) (j : ℕ) :
    blockLift a b (2*j) = prev b j - prev a j := by
  by_cases hj : j = 0
  · subst j; simp [blockLift, prev]
  · simp [blockLift, prev, hj, show 2*j ≠ 0 by omega]

lemma blockLift_first (a b : ℕ → ℝ) (j : ℕ) :
    blockLift a b (2*j+1) = b j + a j := by
  simp [blockLift, show (2*j+1)/2 = j by omega]

lemma blockLift_second (a b : ℕ → ℝ) (j : ℕ) :
    blockLift a b (2*j+2) = b j - a j := by
  simp [blockLift]

lemma blockLift_average (a b : ℕ → ℝ) (j : ℕ) :
    blockLift a b (2*j+1) + blockLift a b (2*j+2) = 2*b j := by
  rw [blockLift_first, blockLift_second]
  ring

/-- The explicit finite source-response formula. -/
theorem blockLift_response (a b : ℕ → ℝ) (j : ℕ) :
    response (blockLift a b) j = b j - prev b j + 3*a j + prev a j := by
  unfold response lap
  rw [blockLift_first, blockLift_even, blockLift_second]
  ring

/-- The tridiagonal equation is precisely stationarity of the constrained lift. -/
theorem blockLift_stationary (n : ℕ) (a b : ℕ → ℝ)
    (heq : ∀ j < n, 6*a j + prev a j + a (j+1) = prev b j - b (j+1)) :
    Stationary n (blockLift a b) := by
  intro j hj
  have he := heq j hj
  unfold lap
  rw [blockLift_first, blockLift_even, blockLift_second,
    show 2*j+1+2 = 2*(j+1)+1 by omega, blockLift_first]
  linarith

/-- A stationary lift exists for every finite sequence of coarse averages. -/
theorem exists_stationary_lift (n : ℕ) (b : ℕ → ℝ) (hb : b n = 0) :
    ∃ y : ℕ → ℝ, y 0 = 0 ∧ y (2*n+1) = 0 ∧
      (∀ j < n, y (2*j+1) + y (2*j+2) = 2*b j) ∧ Stationary n y := by
  obtain ⟨a, ha, heq⟩ := exists_tri_solution n (fun j => prev b j - b (j+1))
  refine ⟨blockLift a b, blockLift_zero a b, ?_, ?_, blockLift_stationary n a b heq⟩
  · rw [blockLift_first, hb, ha, add_zero]
  · intro j _; exact blockLift_average a b j

/-- The concrete tridiagonal response is positive definite on coarse block data. -/
theorem tridiagonal_response_pos (n : ℕ) (a b : ℕ → ℝ)
    (ha : a n = 0) (hb : b n = 0)
    (heq : ∀ j < n, 6*a j + prev a j + a (j+1) = prev b j - b (j+1))
    (hne : ∃ j < n, b j ≠ 0) :
    0 < ∑ j ∈ range n, b j * (b j - prev b j + 3*a j + prev a j) := by
  have hp := response_pos n (blockLift a b) b (blockLift_zero a b)
    (by rw [blockLift_first, hb, ha, add_zero])
    (fun j _ => blockLift_average a b j) (blockLift_stationary n a b heq) hne
  simpa only [blockLift_response] using hp

#print axioms pad
#print axioms prev
#print axioms tri
#print axioms pad_abs_le
#print axioms tri_injective
#print axioms exists_tri_solution
#print axioms blockLift
#print axioms blockLift_zero
#print axioms blockLift_even
#print axioms blockLift_first
#print axioms blockLift_second
#print axioms blockLift_average
#print axioms blockLift_response
#print axioms blockLift_stationary
#print axioms exists_stationary_lift
#print axioms tridiagonal_response_pos

end AdalyFormal.Round10.Nonvanishing.FreeProfile

namespace AdalyFormal.Round10.Nonvanishing.FreeProfile

open Finset

lemma sum_prev_mul (n : ℕ) (a b : ℕ → ℝ) (hb : b n = 0) :
    (∑ j ∈ range n, prev a j * b j) = ∑ j ∈ range n, a j * b (j+1) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [sum_range_succ']
    simp only [prev, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel, zero_mul, add_zero]
    rw [sum_range_succ, hb, mul_zero, add_zero]

lemma sum_next_mul (n : ℕ) (a b : ℕ → ℝ) (ha : a n = 0) :
    (∑ j ∈ range n, a (j+1) * b j) = ∑ j ∈ range n, a j * prev b j := by
  simpa only [mul_comm] using (sum_prev_mul n b a ha).symm

lemma tri_pairing_symm (n : ℕ) (a c : ℕ → ℝ) (ha : a n = 0) (hc : c n = 0) :
    (∑ j ∈ range n, a j * (6*c j + prev c j + c (j+1))) =
      ∑ j ∈ range n, (6*a j + prev a j + a (j+1)) * c j := by
  simp_rw [mul_add, add_mul]
  simp only [sum_add_distrib]
  have h₁ := sum_prev_mul n a c hc
  have h₂ := sum_next_mul n a c ha
  have hm : (∑ j ∈ range n, a j * (6*c j)) = ∑ j ∈ range n, (6*a j)*c j := by
    apply sum_congr rfl
    intro j _
    ring
  rw [h₁, h₂, hm]
  ring

lemma sum_delta (n i : ℕ) (b : ℕ → ℝ) (hi : i < n) :
    (∑ j ∈ range n, (if j = i then (1 : ℝ) else 0) * b j) = b i := by
  simp [hi]

lemma sum_prev_delta (n i : ℕ) (b : ℕ → ℝ) (hi : i < n) :
    (∑ j ∈ range n, (if j+1 = i then (1 : ℝ) else 0) * b j) = prev b i := by
  by_cases hz : i = 0
  · subst i; simp [prev]
  · have he : ∀ j : ℕ, j+1 = i ↔ j = i-1 := by intro j; omega
    simp_rw [he]
    simp [prev, hz, show i-1 < n by omega]

/-- One even-site defect, anywhere in the core; the first site is the old source. -/
noncomputable def sourceRhs (i j : ℕ) : ℝ :=
  (3/2 : ℝ) * (if j = i then 1 else 0) +
  (1/2 : ℝ) * (if j+1 = i then 1 else 0)

/-- Exact finite tridiagonal amplitude for a selected source site. -/
noncomputable def sourceAmplitude (n i : ℕ) : ℕ → ℝ :=
  Classical.choose (exists_tri_solution n (sourceRhs i))

lemma sourceAmplitude_boundary (n i : ℕ) : sourceAmplitude n i n = 0 :=
  (Classical.choose_spec (exists_tri_solution n (sourceRhs i))).1

lemma sourceAmplitude_equation (n i : ℕ) :
    ∀ j < n, 6*sourceAmplitude n i j + prev (sourceAmplitude n i) j +
      sourceAmplitude n i (j+1) = sourceRhs i j :=
  (Classical.choose_spec (exists_tri_solution n (sourceRhs i))).2

/-- The exact source multiplier, with no limiting or floating-point constants. -/
def columnWeight (a : ℕ → ℝ) (i j : ℕ) : ℝ :=
  (if j = i then 1 else 0) - (if j+1 = i then 1 else 0) -
    2*prev a j + 2*a (j+1)

/-- Half-coupling to the source at site i. -/
noncomputable def sourceResponse (n i : ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range n, columnWeight (sourceAmplitude n i) i j * b j

lemma columnWeight_first (a : ℕ → ℝ) (j : ℕ) :
    columnWeight a 0 j = (if j = 0 then 1 else 0) - 2*prev a j + 2*a (j+1) := by
  simp [columnWeight]

/-- Reciprocity identifies the source sum with the local Dirichlet response. -/
theorem column_pairing (n i : ℕ) (a c b : ℕ → ℝ) (hi : i < n)
    (ha : a n = 0) (hc : c n = 0) (hb : b n = 0)
    (hsource : ∀ j < n, 6*c j + prev c j + c (j+1) = sourceRhs i j)
    (hlift : ∀ j < n, 6*a j + prev a j + a (j+1) = prev b j - b (j+1)) :
    (∑ j ∈ range n, columnWeight c i j * b j) =
      b i - prev b i + 3*a i + prev a i := by
  have he : (∑ j ∈ range n, c j * (prev b j - b (j+1))) =
      (3/2 : ℝ)*a i + (1/2 : ℝ)*prev a i := by
    calc
      _ = ∑ j ∈ range n, c j * (6*a j + prev a j + a (j+1)) := by
        apply sum_congr rfl
        intro j hj
        rw [hlift j (mem_range.mp hj)]
      _ = ∑ j ∈ range n, (6*c j + prev c j + c (j+1))*a j :=
        tri_pairing_symm n c a hc ha
      _ = ∑ j ∈ range n, sourceRhs i j * a j := by
        apply sum_congr rfl
        intro j hj
        rw [hsource j (mem_range.mp hj)]
      _ = _ := by
        simp only [sourceRhs, add_mul, mul_assoc, sum_add_distrib, ← mul_sum]
        rw [sum_delta n i a hi, sum_prev_delta n i a hi]
  have he' : (∑ j ∈ range n, c (j+1)*b j) -
      (∑ j ∈ range n, prev c j*b j) = (3/2 : ℝ)*a i + (1/2 : ℝ)*prev a i := by
    rw [sum_next_mul n c b hc, sum_prev_mul n c b hb]
    simpa only [mul_sub, sum_sub_distrib] using he
  simp only [columnWeight, sub_mul, add_mul, sum_add_distrib, sum_sub_distrib,
    mul_assoc, ← mul_sum]
  rw [sum_delta n i b hi, sum_prev_delta n i b hi]
  linarith

/-- The entire source-response matrix is positive definite for every finite length. -/
theorem sourceResponse_pos (n : ℕ) (b : ℕ → ℝ) (hb : b n = 0)
    (hne : ∃ j < n, b j ≠ 0) :
    0 < ∑ i ∈ range n, b i * sourceResponse n i b := by
  obtain ⟨a, ha, heq⟩ := exists_tri_solution n (fun j => prev b j - b (j+1))
  have hp := tridiagonal_response_pos n a b ha hb heq hne
  have hd : ∀ i < n, sourceResponse n i b = b i - prev b i + 3*a i + prev a i := by
    intro i hi
    exact column_pairing n i a (sourceAmplitude n i) b hi ha
      (sourceAmplitude_boundary n i) hb (sourceAmplitude_equation n i) heq
  convert hp using 1
  apply sum_congr rfl
  intro i hi
  rw [hd i (mem_range.mp hi)]

/-- For every nonzero finite jet vector, at least one single-site source couples.
No jet domination or sign hypothesis occurs. -/
theorem exists_sourceResponse_ne_zero (n : ℕ) (b : ℕ → ℝ) (hb : b n = 0)
    (hne : ∃ j < n, b j ≠ 0) :
    ∃ i < n, sourceResponse n i b ≠ 0 := by
  by_contra h
  push Not at h
  have hp := sourceResponse_pos n b hb hne
  have hz : (∑ i ∈ range n, b i * sourceResponse n i b) = 0 := by
    apply sum_eq_zero
    intro i hi
    rw [h i (mem_range.mp hi), mul_zero]
  linarith

/-- The only remaining hypotheses here are the actual block dictionary and a nonzero
jet. The theorem by itself does not provide either for a vacuum crossing vector. -/
theorem exists_actual_coupling_of_source_dictionary (n : ℕ) (b coupling : ℕ → ℝ)
    (factor : ℝ) (hb : b n = 0) (hne : ∃ j < n, b j ≠ 0) (hf : factor ≠ 0)
    (hdict : ∀ i < n, coupling i = factor * sourceResponse n i b) :
    ∃ i < n, coupling i ≠ 0 := by
  obtain ⟨i, hi, hr⟩ := exists_sourceResponse_ne_zero n b hb hne
  refine ⟨i, hi, ?_⟩
  rw [hdict i hi]
  exact mul_ne_zero hf hr

/-- Choice-independent hand-off: the dictionary may supply its own source amplitudes.
Any family satisfying the displayed finite equations separates every nonzero jet vector. -/
theorem source_columns_separate (n : ℕ) (b : ℕ → ℝ) (c : ℕ → ℕ → ℝ)
    (hb : b n = 0) (hne : ∃ j < n, b j ≠ 0)
    (hc : ∀ i < n, c i n = 0)
    (heq : ∀ i < n, ∀ j < n,
      6*c i j + prev (c i) j + c i (j+1) = sourceRhs i j) :
    ∃ i < n, (∑ j ∈ range n, columnWeight (c i) i j * b j) ≠ 0 := by
  obtain ⟨a, ha, he⟩ := exists_tri_solution n (fun j => prev b j - b (j+1))
  have hs := blockLift_stationary n a b he
  obtain ⟨i, hi, hr⟩ := exists_response_ne_zero n (blockLift a b) b
    (blockLift_zero a b) (by rw [blockLift_first, hb, ha, add_zero])
    (fun j _ => blockLift_average a b j) hs hne
  refine ⟨i, hi, ?_⟩
  rw [column_pairing n i a (c i) b hi ha (hc i hi) hb (heq i hi) he]
  simpa only [blockLift_response] using hr

/-- Fully explicit dictionary interface, with no choice-based matrix in its hypotheses. -/
theorem exists_coupling_of_source_columns (n : ℕ) (b coupling : ℕ → ℝ)
    (c : ℕ → ℕ → ℝ) (factor : ℝ)
    (hb : b n = 0) (hne : ∃ j < n, b j ≠ 0) (hf : factor ≠ 0)
    (hc : ∀ i < n, c i n = 0)
    (heq : ∀ i < n, ∀ j < n,
      6*c i j + prev (c i) j + c i (j+1) = sourceRhs i j)
    (hdict : ∀ i < n, coupling i = factor *
      (∑ j ∈ range n, columnWeight (c i) i j * b j)) :
    ∃ i < n, coupling i ≠ 0 := by
  obtain ⟨i, hi, hr⟩ := source_columns_separate n b c hb hne hc heq
  refine ⟨i, hi, ?_⟩
  rw [hdict i hi]
  exact mul_ne_zero hf hr

#print axioms source_columns_separate
#print axioms exists_coupling_of_source_columns
#print axioms sum_prev_mul
#print axioms sum_next_mul
#print axioms tri_pairing_symm
#print axioms sum_delta
#print axioms sum_prev_delta
#print axioms sourceRhs
#print axioms sourceAmplitude
#print axioms sourceAmplitude_boundary
#print axioms sourceAmplitude_equation
#print axioms columnWeight
#print axioms sourceResponse
#print axioms columnWeight_first
#print axioms column_pairing
#print axioms sourceResponse_pos
#print axioms exists_sourceResponse_ne_zero
#print axioms exists_actual_coupling_of_source_dictionary

end AdalyFormal.Round10.Nonvanishing.FreeProfile
