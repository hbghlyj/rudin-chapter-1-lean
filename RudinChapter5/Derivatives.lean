import Mathlib
open Set Filter Topology
namespace RudinChapter5

/-- Positive derivative implies strict monotonicity. -/
theorem strictMono_of_positive_deriv {f : ℝ → ℝ}
    (hpos : ∀ x, 0 < deriv f x) : StrictMono f := by
  exact strictMono_of_deriv_pos hpos

/-- A function with everywhere positive derivative is injective. -/
theorem injective_of_positive_deriv {f : ℝ → ℝ}
    (hpos : ∀ x, 0 < deriv f x) : Function.Injective f := by
  exact (strictMono_of_positive_deriv hpos).injective

/-- The derivative of the identity is one. -/
theorem deriv_id : deriv (fun x : ℝ => x) = fun _ => 1 := by
  funext x
  simpa using (hasDerivAt_id x).deriv

/-- The derivative of a constant function vanishes. -/
theorem deriv_const (c : ℝ) : deriv (fun _ : ℝ => c) = 0 := by
  funext x
  simpa using (hasDerivAt_const x c).deriv

end RudinChapter5
