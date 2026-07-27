import Mathlib
open Set Filter Topology MeasureTheory
open scoped BigOperators
namespace RudinChapter6

/-- The elementary `2uv ≤ u²+v²` form of Young's inequality. -/
theorem young_two (u v : ℝ) : 2 * u * v ≤ u ^ 2 + v ^ 2 := by
  nlinarith [sq_nonneg (u - v)]

/-- Cauchy--Schwarz for finite real vectors. -/
theorem finite_schwarz {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    (∑ i, f i * g i) ^ 2 ≤ (∑ i, f i ^ 2) * (∑ i, g i ^ 2) := by
  simpa [mul_comm] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g

/-- The Euclidean triangle inequality. -/
theorem euclidean_triangle {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  exact norm_add_le x y

end RudinChapter6
