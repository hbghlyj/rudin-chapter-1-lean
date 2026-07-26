import Mathlib
open Filter Topology
open scoped BigOperators
namespace RudinChapter3

/-- Geometric sequences with ratio of norm less than one tend to zero. -/
theorem geometric_tendsto_zero {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one hx

/-- Absolute summability implies summability. -/
theorem summable_of_abs {f : ℕ → ℝ} (h : Summable (fun n => |f n|)) : Summable f := by
  exact h.of_abs

/-- Every convergent sequence is Cauchy. -/
theorem convergent_cauchy {u : ℕ → ℝ} {a : ℝ} (h : Tendsto u atTop (𝓝 a)) :
    CauchySeq u := by
  exact h.cauchySeq

end RudinChapter3
