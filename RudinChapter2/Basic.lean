import Mathlib

open Set Filter Topology
open scoped Topology

namespace RudinChapter2

/-- The empty set is a subset of every set. -/
theorem empty_subset_every {α : Type*} (s : Set α) : (∅ : Set α) ⊆ s := by
  simp

/-- Rational numbers form a countable subset of the reals. -/
theorem rational_reals_countable : (Set.range ((↑) : ℚ → ℝ)).Countable := by
  exact Set.countable_range _

/-- A concrete bounded set with exactly three candidate accumulation points. -/
def threeLimitPointSet : Set ℝ :=
  {x | ∃ n : ℕ, x = 1 + 1 / (n + 1 : ℝ) ∨ x = 3 + 1 / (n + 1 : ℝ) ∨
    x = 5 + 1 / (n + 1 : ℝ)}

/-- The usual zero-one distance used for the discrete metric. -/
def discreteMetric {α : Type*} [DecidableEq α] (x y : α) : ℝ := if x = y then 0 else 1

theorem discreteMetric_self {α : Type*} [DecidableEq α] (x : α) :
    discreteMetric x x = 0 := by
  simp [discreteMetric]

theorem discreteMetric_comm {α : Type*} [DecidableEq α] (x y : α) :
    discreteMetric x y = discreteMetric y x := by
  simp only [discreteMetric]
  by_cases h : x = y
  · simp [h]
  · simp [h, Ne.symm h]

theorem discreteMetric_triangle {α : Type*} [DecidableEq α] (x y z : α) :
    discreteMetric x z ≤ discreteMetric x y + discreteMetric y z := by
  by_cases hxy : x = y
  · subst y
    simp [discreteMetric]
  · by_cases hyz : y = z
    · subst z
      simp [discreteMetric]
    · by_cases hxz : x = z
      · subst z
        have hyx : y ≠ x := Ne.symm hxy
        simp [discreteMetric, hxy, hyx]
      · simp [discreteMetric, hxy, hyz, hxz]

end RudinChapter2
