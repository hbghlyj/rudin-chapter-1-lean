import Mathlib

open scoped BigOperators ComplexConjugate

namespace Rudin.Chapter1

/-- Negation interchanges infimum and supremum for a nonempty, lower-bounded real set. -/
theorem inf_eq_neg_sup_neg {A : Set ℝ} (_hne : A.Nonempty) (_hbelow : BddBelow A) :
    sInf A = -sSup ((fun x : ℝ => -x) '' A) := by
  have hi : (fun x : ℝ => -x) '' A = -A := by ext x; simp
  rw [hi, ← Real.sInf_neg]
  simp

/-- Every positive real has a unique logarithm to a base greater than one. -/
theorem exists_unique_rpow_eq {b y : ℝ} (hb : 1 < b) (hy : 0 < y) :
    ∃! x : ℝ, b ^ x = y := by
  have hbpos : 0 < b := lt_trans (by norm_num) hb
  have hbne : b ≠ 1 := ne_of_gt hb
  refine ⟨Real.logb b y, Real.rpow_logb hbpos hbne hy, ?_⟩
  intro z hz
  exact (Real.strictMono_rpow_of_base_gt_one hb).injective
    (hz.trans (Real.rpow_logb hbpos hbne hy).symm)

/-- No linear order compatible with the ring operations can exist on `ℂ`. -/
theorem complex_cannot_be_ordered_field :
    ¬ ∃ (_ : LinearOrder ℂ), ∃ (_ : IsStrictOrderedRing ℂ), True := by
  sorry

/-- The lexicographic order on complex numbers, viewed as pairs of reals. -/
noncomputable def complexLex : LinearOrder ℂ := LinearOrder.lift' (fun z : ℂ => toLex (z.re, z.im)) (by
  intro z w h
  apply Complex.ext <;> simp_all)

/-- In the complex lexicographic order, the imaginary axis is bounded above. -/
theorem imaginaryAxis_bddAbove_lex :
    letI := complexLex
    BddAbove {z : ℂ | z.re = 0} := by
  simp [bddAbove_def]
  use 1
  intro z hz
  have h : ∀ a b : ℂ, letI := complexLex; a ≤ b ↔ toLex (a.re, a.im) ≤ toLex (b.re, b.im) := by
    intro a b
    rfl
  rw [h]
  simp only [hz, Complex.one_re, Complex.one_im]
  have hlt : (0 : ℝ) < 1 := by norm_num
  have h : Prod.Lex (fun a b => a < b) (fun a b => a ≤ b) ((0 : ℝ), z.im) ((1 : ℝ), 0) :=
    Prod.Lex.left (α := ℝ) (β := ℝ) (ra := fun a b => a < b) (rb := fun a b => a ≤ b) (a₁ := 0) (a₂ := 1) (b₁ := z.im) (b₂ := (0 : ℝ)) hlt
  exact h

/-- The imaginary axis has no least upper bound in the complex lexicographic order. -/
theorem imaginaryAxis_no_sup_lex :
    letI := complexLex
    ¬ ∃ s : ℂ, IsLUB {z : ℂ | z.re = 0} s := by
  letI := complexLex
  intro ⟨s, hs⟩
  have hub := hs.1
  have hlu := hs.2
  by_cases hre : s.re > 0
  · -- s.re > 0: construct a smaller upper bound t = (s.re/2, s.im)
    exfalso
    set t : ℂ := ⟨s.re / 2, s.im⟩
    -- t is an upper bound since t.re = s.re/2 > 0
    have ht_upper : t ∈ upperBounds {z : ℂ | z.re = 0} := fun z hz => by
      simp only [Set.mem_setOf_eq] at hz
      change toLex (z.re, z.im) ≤ toLex (t.re, t.im)
      simp [hz, t]
      rw [Prod.Lex.toLex_le_toLex]
      left
      linarith
    -- t < s since s.re/2 < s.re
    have ht_lt_s : t < s := by
      change toLex (t.re, t.im) < toLex (s.re, s.im)
      simp [t]
      rw [Prod.Lex.toLex_lt_toLex]
      left
      linarith
    exact ht_lt_s.not_ge (hlu ht_upper)
  · -- s.re ≤ 0, so s is not an upper bound
    exfalso
    rcases lt_trichotomy s.re 0 with hlt | heq | hgt
    · -- s.re < 0: 0 is in imaginary axis and 0 > s
      have : (0 : ℂ) ∈ {z : ℂ | z.re = 0} := by simp
      have h0_gt_s : (0 : ℂ) > s := by
        rw [show (0 : ℂ) > s ↔ s < (0 : ℂ) from gt_iff_lt]
        change toLex (s.re, s.im) < toLex ((0 : ℂ).re, (0 : ℂ).im)
        simp only [Complex.zero_re, Complex.zero_im]
        left
        exact hlt
      exact not_le_of_gt h0_gt_s (hub this)
    · -- s.re = 0: take z = (0, s.im + 1) which is in imaginary axis and > s
      exfalso
      set z : ℂ := ⟨0, s.im + 1⟩
      have hz : z ∈ {z : ℂ | z.re = 0} := by simp [z]
      have hz_gt_s : z > s := by
        rw [show z > s ↔ s < z from gt_iff_lt]
        change toLex (s.re, s.im) < toLex (z.re, z.im)
        simp [z]
        rw [heq]
        refine Prod.Lex.toLex_lt_toLex.mpr ?_
        right
        constructor
        · rfl
        · linarith
      exact not_le_of_gt hz_gt_s (hub hz)
    · -- s.re > 0 contradicts hre
      exact absurd hgt hre

/-- Rudin's explicit square-root formula in the upper half-plane. -/
theorem complex_square_root_formula_nonneg_im (w : ℂ) (hv : 0 ≤ w.im) :
    let a := Real.sqrt ((norm w + w.re) / 2)
    let b := Real.sqrt ((norm w - w.re) / 2)
    (a + b * Complex.I) ^ 2 = w := by
  intro a b
  -- Compute (a + b*I)^2 = a^2 - b^2 + 2ab*I
  have hsq : (a + b * Complex.I) ^ 2 = ⟨a^2 - b^2, 2 * a * b⟩ := by
    simp [sq, Complex.ext_iff]
    ring
  rw [hsq]
  -- Prepare helper lemmas
  have hle : -‖w‖ ≤ w.re := (abs_le.mp (Complex.abs_re_le_norm w)).1
  have hle' : w.re ≤ ‖w‖ := (abs_le.mp (Complex.abs_re_le_norm w)).2
  have ha_sq : a ^ 2 = (norm w + w.re) / 2 := by
    apply Real.sq_sqrt; linarith [norm_nonneg w]
  have hb_sq : b ^ 2 = (norm w - w.re) / 2 := by
    apply Real.sq_sqrt; linarith [norm_nonneg w]
  have ha_nonneg : 0 ≤ a := Real.sqrt_nonneg _
  have hb_nonneg : 0 ≤ b := Real.sqrt_nonneg _
  have hnorm_sq : norm w ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq w]
    simp [Complex.normSq_apply]
    ring
  -- Need to show a^2 - b^2 = w.re and 2*a*b = w.im
  apply Complex.ext
  · -- Real part: a^2 - b^2 = w.re
    linarith
  · -- Imaginary part: 2*a*b = w.im
    have hab_sq : (a * b) ^ 2 = w.im ^ 2 / 4 := by
      have h1 : (a * b) ^ 2 = a ^ 2 * b ^ 2 := by ring
      rw [h1, ha_sq, hb_sq]
      linarith [hnorm_sq]
    have hab_nonneg : 0 ≤ a * b := mul_nonneg ha_nonneg hb_nonneg
    have hab_eq : a * b = |w.im| / 2 := by
      have h_sq_eq : (a * b) ^ 2 = (|w.im| / 2) ^ 2 := by
        rw [hab_sq]
        have : w.im ^ 2 = |w.im| ^ 2 := (sq_abs w.im).symm
        rw [this]
        ring
      exact sq_eq_sq₀ hab_nonneg (by positivity) |>.mp h_sq_eq
    rw [abs_of_nonneg hv] at hab_eq
    linarith

/-- Rudin's explicit square-root formula in the lower half-plane. -/
theorem complex_square_root_formula_nonpos_im (w : ℂ) (hv : w.im ≤ 0) :
    let a := Real.sqrt ((norm w + w.re) / 2)
    let b := Real.sqrt ((norm w - w.re) / 2)
    (star (a + b * Complex.I)) ^ 2 = w := by
  have hstar_im : (star w).im ≥ 0 := by simp [hv]
  have hstar_formula := complex_square_root_formula_nonneg_im (star w) hstar_im
  have hnorm : ‖star w‖ = ‖w‖ := Complex.norm_conj w
  have hre : (star w).re = w.re := by simp
  rw [hnorm, hre] at hstar_formula
  simp only at hstar_formula
  have h_eq : (Real.sqrt ((‖w‖ + w.re) / 2) : ℂ) + (Real.sqrt ((‖w‖ - w.re) / 2) : ℂ) * Complex.I =
    (Real.sqrt ((‖w‖ + w.re) / 2) : ℂ) + (Real.sqrt ((‖w‖ - w.re) / 2) : ℂ) * Complex.I := rfl
  have := congr_arg star hstar_formula
  simp only [star_pow] at this
  rw [star_star] at this
  exact this

/-- Every nonzero complex number has exactly two square roots. -/
theorem complex_two_square_roots {z : ℂ} (hz : z ≠ 0) :
    ∃ w : ℂ, w ^ 2 = z ∧ {u : ℂ | u ^ 2 = z} = {w, -w} := by
  -- Choose w based on whether z.im is nonneg or nonpos
  by_cases h : 0 ≤ z.im
  · -- Case: z.im ≥ 0, use the upper half-plane formula
    let a := Real.sqrt ((norm z + z.re) / 2)
    let b := Real.sqrt ((norm z - z.re) / 2)
    use a + b * Complex.I
    refine ⟨complex_square_root_formula_nonneg_im z h, ?_⟩
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hu
      have hw : (a + b * Complex.I) ^ 2 = z := complex_square_root_formula_nonneg_im z h
      have hsq : u ^ 2 = (a + b * Complex.I) ^ 2 := hu.trans hw.symm
      rcases eq_or_eq_neg_of_sq_eq_sq u (a + b * Complex.I) hsq with h | h <;> [left; right] <;> exact h
    · intro hu
      rcases hu with rfl | rfl
      · exact complex_square_root_formula_nonneg_im z h
      · rw [neg_pow, complex_square_root_formula_nonneg_im z h]; norm_num
  · -- Case: z.im < 0, use the lower half-plane formula
    push_neg at h
    let a := Real.sqrt ((norm z + z.re) / 2)
    let b := Real.sqrt ((norm z - z.re) / 2)
    use star (a + b * Complex.I)
    have hstar_formula := complex_square_root_formula_nonpos_im z (le_of_lt h)
    refine ⟨hstar_formula, ?_⟩
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hu
      have hw : (star (a + b * Complex.I)) ^ 2 = z := hstar_formula
      have hsq : u ^ 2 = (star (a + b * Complex.I)) ^ 2 := hu.trans hw.symm
      rcases eq_or_eq_neg_of_sq_eq_sq u (star (a + b * Complex.I)) hsq with h | h <;> [left; right] <;> exact h
    · intro hu
      rcases hu with rfl | rfl
      · exact hstar_formula
      · rw [neg_pow, hstar_formula]; norm_num

/-- Polar decomposition, including uniqueness away from zero. -/
theorem complex_polar_decomposition (z : ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∃ w : ℂ, norm w = 1 ∧ z = r * w ∧
      (z ≠ 0 → ∀ r' : ℝ, 0 ≤ r' → ∀ w' : ℂ,
        norm w' = 1 → z = r' * w' → r' = r ∧ w' = w) := by
  use norm z
  refine ⟨norm_nonneg z, ?_⟩
  by_cases hz : z = 0
  · -- Case z = 0
    refine ⟨1, ?_, ?_, ?_⟩
    · simp
    · simp [hz]
    · intro hz' r' hr' w' hw' hzw'
      exfalso
      exact hz' hz
  · -- Case z ≠ 0
    use z / norm z
    have hnne : norm z ≠ 0 := norm_ne_zero_iff.mpr hz
    have hn_norm : norm (↑(norm z) : ℂ) = norm z := by simp [Complex.norm_def]
    have h1 : norm (z / norm z) = 1 := by
      rw [norm_div, hn_norm, div_self hnne]
    have h2 : z = norm z * (z / norm z) := by field_simp [hnne]
    refine ⟨h1, h2, ?_⟩
    intro hz' r' hr' w' hw' hzw'
    -- From z = r' * w', take norms: norm z = r' * norm w' = r'
    have hnorm : norm z = r' := by
      rw [hzw']
      simp [hw', Real.norm_eq_abs, abs_of_nonneg hr']
    -- So r' = norm z and w' = z / norm z
    refine ⟨hnorm.symm, ?_⟩
    -- From z = r' * w', we get w' = z / r' = z / norm z
    have hr'pos : r' > 0 := by rw [← hnorm]; exact norm_pos_iff.mpr hz
    have hw'_eq : w' = z / norm z := by
      rw [hnorm]
      have hr'_ne : (r' : ℂ) ≠ 0 := by
        simp [hr'pos.ne']
      rw [eq_div_iff hr'_ne]
      rw [mul_comm]
      exact hzw'.symm
    exact hw'_eq

/-- The triangle inequality for a finite family of complex numbers. -/
theorem complex_sum_abs_le {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    norm (∑ i ∈ s, z i) ≤ ∑ i ∈ s, norm (z i) := by
  apply norm_sum_le

/-- The reverse triangle inequality. -/
theorem complex_reverse_triangle (x y : ℂ) :
    |norm x - norm y| ≤ norm (x - y) := by
  exact abs_norm_sub_norm_le x y

/-- The requested computation for a unit complex number. -/
theorem complex_unit_parallelogram {z : ℂ} (hz : norm z = 1) :
    norm (1 + z) ^ 2 + norm (1 - z) ^ 2 = 4 := by
  have hz' : Complex.normSq z = 1 := by
    have := Complex.normSq_eq_norm_sq z
    simp [hz] at this
    exact this
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_add, Complex.normSq_sub, hz']
  norm_num

/-- Equality in finite-dimensional complex Cauchy--Schwarz holds exactly for
linearly dependent vectors. -/
theorem cauchy_schwarz_equality_iff {n : ℕ} (a b : Fin n → ℂ) :
    norm (∑ j, a j * conj (b j)) ^ 2 =
        (∑ j, norm (a j) ^ 2) * (∑ j, norm (b j) ^ 2) ↔
      ((∀ j, b j = 0) ∨ ∃ c : ℂ, ∀ j, a j = c * b j) := by
  constructor
  · intro h
    -- Strategy: check if all b j = 0. If so, done. Otherwise, define c and show a = c * b.
    by_cases hb : ∀ j, b j = 0
    · exact Or.inl hb
    -- Not all b j = 0, so ∑ j, ‖b j‖² > 0
    push_neg at hb
    have hbne : ∑ j, ‖b j‖ ^ 2 ≠ 0 := by
      obtain ⟨j₀, hj₀⟩ := hb
      have hpos : 0 < ‖b j₀‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hj₀)
      exact ne_of_gt (lt_of_lt_of_le hpos (Finset.single_le_sum (fun j _ => sq_nonneg ‖b j‖) (Finset.mem_univ j₀)))
    -- Define c = ⟨a, b⟩ / ‖b‖²
    set s := ∑ j, a j * conj (b j) with hs
    set t := ∑ j, ‖b j‖ ^ 2 with ht
    have htpos : 0 < t := lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Ne.symm hbne)
    set c : ℂ := s / t with hc_def
    -- Goal: show a j = c * b j for all j
    -- Key: show ∑ j, ‖a j - c * b j‖² = 0
    -- We have h: ‖s‖² = (∑ j, ‖a j‖²) * t
    -- Need: conj(s) = ∑ j, conj(a j) * b j (which is ∑ j, b j * conj(a j))
    have hconj_s : ∑ j, (starRingEnd ℂ) (a j) * b j = conj s := by
      have heq : ∀ j, (starRingEnd ℂ) (a j) * b j = (starRingEnd ℂ) (a j * (starRingEnd ℂ) (b j)) := by
        intro j
        simp
      simp_rw [heq, ← map_sum (starRingEnd ℂ), hs]
    -- Compute ∑ j, ‖a j - c * b j‖²
    -- = ∑ j, ‖a j‖² - conj(c) * s - c * conj(s) + |c|² * t
    -- Also need: ∑ j, b j * conj(a j) = conj s (equivalent to hconj_s)
    have hconj_s' : ∑ j, b j * (starRingEnd ℂ) (a j) = conj s := by
      rw [← hconj_s]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hnormSq_b : ∑ j, Complex.normSq (b j) = t := by
      simp only [Complex.normSq_eq_norm_sq, ← ht]
    -- Expand normSq (a j - c * b j)
    have h_expand : ∀ j, Complex.normSq (a j - c * b j) = Complex.normSq (a j) + Complex.normSq c * Complex.normSq (b j) - 2 * ((starRingEnd ℂ) c * (a j * (starRingEnd ℂ) (b j))).re := by
      intro j
      rw [Complex.normSq_sub, Complex.normSq_mul]
      simp [mul_assoc, mul_comm]
    -- Sum the expansion
    have hsum_expand : ∑ j, Complex.normSq (a j - c * b j) = ∑ j, Complex.normSq (a j) + Complex.normSq c * ∑ j, Complex.normSq (b j) - 2 * ((starRingEnd ℂ) c * s).re := by
      simp_rw [h_expand]
      have h1 : ∑ j, (2 : ℝ) * ((starRingEnd ℂ) c * (a j * (starRingEnd ℂ) (b j))).re = 2 * ((starRingEnd ℂ) c * s).re := by
        rw [← Finset.mul_sum]
        congr 1
        rw [hs]
        rw [← Complex.re_sum, Finset.mul_sum]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, h1]
      simp only [Finset.mul_sum]
    -- Show the sum equals 0
    have hsum_zero : ∑ j, Complex.normSq (a j - c * b j) = 0 := by
      rw [hsum_expand, hnormSq_b]
      -- From h: ‖s‖² = (∑ j, ‖a j‖²) * t, so ∑ j, ‖a j‖² = ‖s‖² / t
      have hsum_a : ∑ j, Complex.normSq (a j) = ‖s‖ ^ 2 / t := by
        have := h
        simp only [Complex.normSq_eq_norm_sq] at this ⊢
        field_simp
        linarith
      rw [hsum_a]
      -- normSq c = ‖s‖² / t²
      have hnormSq_c : Complex.normSq c = ‖s‖ ^ 2 / t ^ 2 := by
        simp only [hc_def]
        rw [Complex.normSq_div]
        simp [Complex.normSq_eq_norm_sq]
      rw [hnormSq_c]
      -- (star c) * s = conj(s)/t * s = ‖s‖² / t
      have hconj_c_s : (starRingEnd ℂ) c * s = (‖s‖ ^ 2 / t : ℝ) := by
        simp [hc_def]
        field_simp
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
        norm_cast
      rw [hconj_c_s]
      simp only [pow_two]
      simp [Complex.ofReal_mul, Complex.ofReal_re]
      field_simp
      ring
    -- From sum = 0, all terms are 0
    have hall_eq : ∀ j, a j = c * b j := by
      intro j
      have hz := Finset.sum_eq_zero_iff_of_nonneg (f := fun i => Complex.normSq (a i - c * b i)) (s := Finset.univ)
        (fun i _ => Complex.normSq_nonneg _)
      rw [hz] at hsum_zero
      exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp (hsum_zero j (Finset.mem_univ j)))
    exact Or.inr ⟨c, hall_eq⟩
  · intro h
    rcases h with hab | ⟨c, hc⟩
    · -- case: all b j = 0
      simp [hab]
    · -- case: a = c * b
      simp only [hc]
      have key : ∀ x, (starRingEnd ℂ) (b x) * b x = ‖b x‖ ^ 2 := by
        intro x
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
        simp
      have h1 : ∀ x, (starRingEnd ℂ) (b x) * (c * b x) = c * ‖b x‖ ^ 2 := by
        intro x
        calc (starRingEnd ℂ) (b x) * (c * b x) = c * ((starRingEnd ℂ) (b x) * b x) := by ring
          _ = c * ‖b x‖ ^ 2 := by rw [key x]
      have h2 : ∀ x, c * b x * (starRingEnd ℂ) (b x) = c * ‖b x‖ ^ 2 := by
        intro x; rw [mul_assoc, mul_comm (b x) ((starRingEnd ℂ) (b x)), key x]
      simp_rw [h2]
      simp only [Finset.mul_sum]
      rw [← Finset.mul_sum]
      -- LHS: ‖c * ∑ i, ‖b i‖²‖² = |c|² * (∑ i, ‖b i‖²)²
      -- RHS: (∑ i, ‖c * b i‖²) * ∑ i, ‖b i‖² = |c|² * (∑ i, ‖b i‖²)²
      have hsum_eq : ∑ i : Fin n, (‖b i‖ : ℂ) ^ 2 = (∑ i : Fin n, ‖b i‖ ^ 2 : ℝ) := by
        simp [sq, ← Complex.ofReal_mul]
      rw [hsum_eq]
      rw [Complex.norm_mul, Complex.norm_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      -- LHS: (‖c‖ * ∑ i, ‖b i‖²)² = ‖c‖² * (∑ i, ‖b i‖²)²
      -- RHS: (∑ x, ‖c * b x‖²) * ∑ i, ‖b i‖²
      rw [mul_pow, ← Finset.mul_sum]
      have hsum_c : ∑ x, ‖c * b x‖ ^ 2 = ‖c‖ ^ 2 * ∑ x, ‖b x‖ ^ 2 := by
        simp_rw [norm_mul, mul_pow, Finset.mul_sum]
      rw [hsum_c]
      ring

end Rudin.Chapter1
