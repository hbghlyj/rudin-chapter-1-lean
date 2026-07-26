import Mathlib

open scoped BigOperators

namespace Rudin.Chapter1

/-- Rudin's set `B(x)` of rational powers with exponent at most `x`. -/
def rationalPowerSet (b x : ℝ) : Set ℝ :=
  {y | ∃ t : ℚ, (t : ℝ) ≤ x ∧ y = b ^ (t : ℝ)}

/-- The value of a rational power does not depend on the chosen integer fraction.
This is stated using nonnegative real roots, as in Rudin's construction. -/
theorem rational_power_well_defined {b : ℝ} (hb : 0 < b)
    {m n p q : ℤ} (hn : 0 < n) (hq : 0 < q)
    (hfrac : (m : ℚ) / n = (p : ℚ) / q) :
    (b ^ (m : ℝ)) ^ ((n : ℝ)⁻¹) = (b ^ (p : ℝ)) ^ ((q : ℝ)⁻¹) := by
  sorry

/-- The addition law for rational exponents. -/
theorem rational_rpow_add {b : ℝ} (hb : 0 < b) (r s : ℚ) :
    b ^ ((r + s : ℚ) : ℝ) = b ^ (r : ℝ) * b ^ (s : ℝ) := by
  rw [← Real.rpow_add hb]
  norm_cast

/-- At a rational argument, Rudin's supremum construction gives the rational power. -/
theorem rational_power_is_sup {b : ℝ} (hb : 1 < b) (r : ℚ) :
    IsLUB (rationalPowerSet b (r : ℝ)) (b ^ (r : ℝ)) := by
  sorry

/-- Rudin's supremum definition agrees with real exponentiation. -/
theorem rpow_eq_sup_rationalPowerSet {b x : ℝ} (hb : 1 < b) :
    b ^ x = sSup (rationalPowerSet b x) := by
  sorry

/-- The exponent addition law for all real exponents. -/
theorem real_rpow_add {b : ℝ} (hb : 0 < b) (x y : ℝ) :
    b ^ (x + y) = b ^ x * b ^ y := by
  exact Real.rpow_add hb x y

/-- Exercise 7(a), Bernoulli's inequality for a base greater than one. -/
theorem pow_sub_one_ge {b : ℝ} (hb : 1 < b) {n : ℕ} (hn : 0 < n) :
    n * (b - 1) ≤ b ^ n - 1 := by
  sorry

/-- Exercise 7(b), the corresponding bound for positive `n`th roots. -/
theorem root_sub_one_bound {b : ℝ} (hb : 1 < b) {n : ℕ} (hn : 0 < n) :
    n * (b ^ ((n : ℝ)⁻¹) - 1) ≤ b - 1 := by
  sorry

/-- Exercise 7(c): sufficiently high roots of `b` lie below every `t > 1`. -/
theorem root_lt_of_large_n {b t : ℝ} (hb : 1 < b) (ht : 1 < t) {n : ℕ}
    (hn : (b - 1) / (t - 1) < n) : b ^ ((n : ℝ)⁻¹) < t := by
  sorry

/-- Exercise 7(d). -/
theorem rpow_step_up_below {b y w : ℝ} (hb : 1 < b) (hy : 0 < y)
    (hw : b ^ w < y) : ∃ n : ℕ, 0 < n ∧ b ^ (w + (n : ℝ)⁻¹) < y := by
  sorry

/-- Exercise 7(e). -/
theorem rpow_step_down_above {b y w : ℝ} (hb : 1 < b) (hy : 0 < y)
    (hw : y < b ^ w) : ∃ n : ℕ, 0 < n ∧ y < b ^ (w - (n : ℝ)⁻¹) := by
  sorry

/-- Exercises 7(f,g): existence and uniqueness of a real logarithm. -/
theorem logarithm_exists_unique {b y : ℝ} (hb : 1 < b) (hy : 0 < y) :
    ∃! x : ℝ, b ^ x = y := by
  have hbpos : 0 < b := lt_trans (by norm_num) hb
  have hbne : b ≠ 1 := ne_of_gt hb
  refine ⟨Real.logb b y, Real.rpow_logb hbpos hbne hy, ?_⟩
  intro z hz
  exact (Real.strictMono_rpow_of_base_gt_one hb).injective
    (hz.trans (Real.rpow_logb hbpos hbne hy).symm)

end Rudin.Chapter1
