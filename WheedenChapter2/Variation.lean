import Mathlib
open Set Filter Topology
namespace WheedenChapter2

noncomputable def oscillatory (x : ℝ) : ℝ := if x = 0 then 0 else x * Real.sin (1 / x)

theorem abs_oscillatory_le (x : ℝ) : |oscillatory x| ≤ |x| := by
  by_cases hx : x = 0
  · simp [oscillatory, hx]
  · rw [oscillatory, if_neg hx, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg x) (Real.abs_sin_le_one (1 / x))

/-- The oscillatory example tends to zero at the origin by squeezing. -/
theorem oscillatory_tendsto_zero : Tendsto oscillatory (𝓝 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with x hx
  rw [Real.dist_eq]
  calc
    |oscillatory x - 0| = |oscillatory x| := by simp
    _ ≤ |x| := abs_oscillatory_le x
    _ = |x - 0| := by simp
    _ < ε := by simpa [Real.dist_eq] using hx

/-- The oscillatory example is continuous at the origin. -/
theorem oscillatory_continuousAt_zero : ContinuousAt oscillatory 0 := by
  have hzero : oscillatory 0 = 0 := by simp [oscillatory]
  rw [ContinuousAt, hzero]
  exact oscillatory_tendsto_zero

/-- The example is bounded on the unit interval. -/
theorem oscillatory_bounded_on_unit : ∀ x ∈ Set.Icc (0 : ℝ) 1, |oscillatory x| ≤ 1 := by
  intro x hx
  calc
    |oscillatory x| ≤ |x| := abs_oscillatory_le x
    _ = x := abs_of_nonneg hx.1
    _ ≤ 1 := hx.2

end WheedenChapter2
