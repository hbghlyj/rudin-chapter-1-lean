import Mathlib

open scoped BigOperators ComplexConjugate

namespace Rudin.Chapter1

/-- Negation interchanges infimum and supremum for a nonempty, lower-bounded real set. -/
theorem inf_eq_neg_sup_neg {A : Set ℝ} (hne : A.Nonempty) (hbelow : BddBelow A) :
    sInf A = -sSup ((fun x : ℝ => -x) '' A) := by
  sorry

/-- Every positive real has a unique logarithm to a base greater than one. -/
theorem exists_unique_rpow_eq {b y : ℝ} (hb : 1 < b) (hy : 0 < y) :
    ∃! x : ℝ, b ^ x = y := by
  sorry

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
  sorry

/-- The triangle inequality for a finite family of complex numbers. -/
theorem complex_sum_abs_le {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    norm (∑ i ∈ s, z i) ≤ ∑ i ∈ s, norm (z i) := by
  sorry

/-- The reverse triangle inequality. -/
theorem complex_reverse_triangle (x y : ℂ) :
    |norm x - norm y| ≤ norm (x - y) := by
  exact abs_norm_sub_norm_le x y

/-- The requested computation for a unit complex number. -/
theorem complex_unit_parallelogram {z : ℂ} (hz : norm z = 1) :
    norm (1 + z) ^ 2 + norm (1 - z) ^ 2 = 4 := by
  sorry

/-- Equality in finite-dimensional complex Cauchy--Schwarz holds exactly for
linearly dependent vectors. -/
theorem cauchy_schwarz_equality_iff {n : ℕ} (a b : Fin n → ℂ) :
    norm (∑ j, a j * conj (b j)) ^ 2 =
        (∑ j, norm (a j) ^ 2) * (∑ j, norm (b j) ^ 2) ↔
      ((∀ j, b j = 0) ∨ ∃ c : ℂ, ∀ j, a j = c * b j) := by
  sorry

end Rudin.Chapter1
