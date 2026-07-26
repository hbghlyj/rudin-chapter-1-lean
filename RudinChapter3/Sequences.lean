import Mathlib
open Filter Topology
namespace RudinChapter3

theorem abs_tendsto {s : ℕ → ℝ} {a : ℝ} (h : Tendsto s atTop (𝓝 a)) :
    Tendsto (fun n => |s n|) atTop (𝓝 |a|) := by
  exact (continuous_abs.tendsto a).comp h

theorem abs_alternating (n : ℕ) : |(-1 : ℝ) ^ n| = 1 := by simp

theorem alternating_square (n : ℕ) : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
  rw [← pow_mul]
  simp

theorem reciprocal_tendsto_zero :
    Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

end RudinChapter3
