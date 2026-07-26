import Mathlib

open scoped BigOperators

namespace Rudin.Chapter1

/-- Adding a nonzero rational number to an irrational real number preserves irrationality. -/
theorem irrational_add_rat {r x : ℝ} (hr : r ∈ Set.range ((↑) : ℚ → ℝ))
    (hx : Irrational x) : Irrational (r + x) := by
  obtain ⟨q, rfl⟩ := hr
  intro ⟨y, hy⟩
  have : x = y - q := by simp [hy]
  exact hx ⟨y - q, by simp [this]⟩

/-- Multiplying an irrational real number by a nonzero rational number preserves irrationality. -/
theorem irrational_mul_rat {r x : ℝ} (hrat : r ∈ Set.range ((↑) : ℚ → ℝ))
    (hr : r ≠ 0) (hx : Irrational x) : Irrational (r * x) := by
  obtain ⟨q, rfl⟩ := hrat
  intro ⟨y, hy⟩
  have hxy : x = y / q := by
    field_simp at hy ⊢
    linarith
  exact hx ⟨y / q, hxy.symm ▸ by simp⟩

/-- No rational number has square `12`. -/
theorem no_rational_sq_twelve (x : ℚ) : x ^ 2 ≠ 12 := by
  sorry

/-- Proposition 1.15(a): cancellation of a nonzero factor. -/
theorem prop_1_15_a {F : Type*} [Field F] {x y z : F} (hx : x ≠ 0)
    (h : x * y = x * z) : y = z := by
  sorry

/-- Proposition 1.15(b). -/
theorem prop_1_15_b {F : Type*} [Field F] {x y : F} (hx : x ≠ 0)
    (h : x * y = x) : y = 1 := by
  sorry

/-- Proposition 1.15(c). -/
theorem prop_1_15_c {F : Type*} [Field F] {x y : F} (hx : x ≠ 0)
    (h : x * y = 1) : y = x⁻¹ := by
  sorry

/-- Proposition 1.15(d): the inverse of the inverse. -/
theorem prop_1_15_d {F : Type*} [Field F] {x : F} (hx : x ≠ 0) : (x⁻¹)⁻¹ = x := by
  sorry

/-- A lower bound of a nonempty set is below every upper bound. -/
theorem lowerBound_le_upperBound {α : Type*} [Preorder α] {E : Set α}
    (hne : E.Nonempty) {a b : α} (ha : a ∈ lowerBounds E) (hb : b ∈ upperBounds E) :
    a ≤ b := by
  sorry

end Rudin.Chapter1
