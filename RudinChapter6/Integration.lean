import Mathlib
open Set Filter Topology MeasureTheory
open scoped Interval Real
namespace RudinChapter6

/-- Integration by parts on a finite interval. -/
theorem integration_by_parts {u v u' v' : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ x ∈ Set.uIcc a b, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (v' x) x)
    (hiu : IntervalIntegrable u' volume a b) (hiv : IntervalIntegrable v' volume a b) :
    (∫ x in a..b, u x * v' x) = u b * v b - u a * v a - ∫ x in a..b, u' x * v x := by
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hiu hiv

/-- Additivity of the interval integral. -/
theorem integral_add_interval {f : ℝ → ℝ} {a b c : ℝ}
    (hab : IntervalIntegrable f volume a b) (hbc : IntervalIntegrable f volume b c) :
    (∫ x in a..b, f x) + ∫ x in b..c, f x = ∫ x in a..c, f x := by
  exact intervalIntegral.integral_add_adjacent_intervals hab hbc

/-- The interval integral of a constant. -/
theorem integral_const (a b c : ℝ) : (∫ _ in a..b, c) = (b - a) * c := by
  simp

end RudinChapter6
