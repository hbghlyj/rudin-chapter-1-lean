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
  intro ⟨_, _, _⟩
  have hI : (0 : ℂ) < Complex.I ^ 2 := pow_two_pos_of_ne_zero Complex.I_ne_zero
  simp only [Complex.I_sq] at hI
  linarith [neg_one_lt_zero (R := ℂ)]

/-- The lexicographic order on complex numbers, viewed as pairs of reals. -/
noncomputable def complexLex : LinearOrder ℂ := LinearOrder.lift' (fun z : ℂ => toLex (z.re, z.im)) (by
  intro z w h
  apply Complex.ext <;> simp_all)

/-- In the complex lexicographic order, the imaginary axis is bounded above. -/
theorem imaginaryAxis_bddAbove_lex :
    letI := complexLex
    BddAbove {z : ℂ | z.re = 0} := by
  sorry

/-- The imaginary axis has no least upper bound in the complex lexicographic order. -/
theorem imaginaryAxis_no_sup_lex :
    letI := complexLex
    ¬ ∃ s : ℂ, IsLUB {z : ℂ | z.re = 0} s := by
  sorry

/-- Rudin's explicit square-root formula in the upper half-plane. -/
theorem complex_square_root_formula_nonneg_im (w : ℂ) (hv : 0 ≤ w.im) :
    let a := Real.sqrt ((norm w + w.re) / 2)
    let b := Real.sqrt ((norm w - w.re) / 2)
    (a + b * Complex.I) ^ 2 = w := by
  sorry

/-- Rudin's explicit square-root formula in the lower half-plane. -/
theorem complex_square_root_formula_nonpos_im (w : ℂ) (hv : w.im ≤ 0) :
    let a := Real.sqrt ((norm w + w.re) / 2)
    let b := Real.sqrt ((norm w - w.re) / 2)
    (star (a + b * Complex.I)) ^ 2 = w := by
  sorry

/-- Every nonzero complex number has exactly two square roots. -/
theorem complex_two_square_roots {z : ℂ} (hz : z ≠ 0) :
    ∃ w : ℂ, w ^ 2 = z ∧ {u : ℂ | u ^ 2 = z} = {w, -w} := by
  sorry

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
  sorry

end Rudin.Chapter1
