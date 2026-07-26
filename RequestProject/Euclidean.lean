import Mathlib

open scoped BigOperators RealInnerProductSpace

namespace Rudin.Chapter1

/-- The trichotomy for intersections of two equal-radius spheres.  For dimensions at
least three, the intersection is infinite exactly when the centers are less than
`2r` apart. -/
theorem equal_radius_spheres {k : ℕ} (hk : 3 ≤ k) (x y : EuclideanSpace ℝ (Fin k))
    (r : ℝ) (hr : 0 < r) (hxy : x ≠ y) :
    let d := dist x y
    (2 * r < d → {z | dist z x = r ∧ dist z y = r} = ∅) ∧
    (2 * r = d → {z | dist z x = r ∧ dist z y = r} = {(2 : ℝ)⁻¹ • (x + y)}) ∧
    (d < 2 * r → Set.Infinite {z | dist z x = r ∧ dist z y = r}) := by
  sorry

/-- In the plane, two equal circles have two intersection points when their
centers are closer than twice the radius. -/
theorem equal_radius_circles_two_points (x y : EuclideanSpace ℝ (Fin 2))
    (r : ℝ) (hr : 0 < r) (hxy : x ≠ y) (hclose : dist x y < 2 * r) :
    ({z | dist z x = r ∧ dist z y = r} : Set (EuclideanSpace ℝ (Fin 2))).ncard = 2 := by
  sorry

/-- On the real line, equal-radius spheres have no common point when their
distinct centers are closer than twice the radius. -/
theorem equal_radius_line_close_empty (x y : ℝ) (r : ℝ) (hr : 0 < r)
    (hxy : x ≠ y) (hclose : dist x y < 2 * r) :
    {z | dist z x = r ∧ dist z y = r} = ∅ := by
  sorry

/-- The parallelogram identity in real Euclidean space. -/
theorem euclidean_parallelogram {k : ℕ} (x y : EuclideanSpace ℝ (Fin k)) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h1 : ‖x + y‖ ^ 2 = inner ℝ (x + y) (x + y) := (real_inner_self_eq_norm_sq (x + y)).symm
  have h2 : ‖x - y‖ ^ 2 = inner ℝ (x - y) (x - y) := (real_inner_self_eq_norm_sq (x - y)).symm
  have h3 : ‖x‖ ^ 2 = inner ℝ x x := (real_inner_self_eq_norm_sq x).symm
  have h4 : ‖y‖ ^ 2 = inner ℝ y y := (real_inner_self_eq_norm_sq y).symm
  rw [h1, h2, h3, h4]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  ring

/-- In dimension at least two, every vector has a nonzero orthogonal vector. -/
theorem exists_nonzero_orthogonal {k : ℕ} (hk : 2 ≤ k)
    (x : EuclideanSpace ℝ (Fin k)) :
    ∃ y : EuclideanSpace ℝ (Fin k), y ≠ 0 ∧ inner ℝ x y = 0 := by
  by_cases h : x ⟨0, by linarith⟩ = 0 ∧ x ⟨1, by omega⟩ = 0
  · -- Case: x₀ = 0 and x₁ = 0, use e₀
    let y := EuclideanSpace.single (𝕜 := ℝ) (ι := Fin k) ⟨0, by linarith⟩ 1
    refine ⟨y, ?_, ?_⟩
    · have : y (⟨0, by linarith⟩ : Fin k) = 1 := by simp [y]
      exact fun hy => by simp [hy] at this
    · simp [inner, PiLp.innerProductSpace]
      rw [Finset.sum_eq_single (⟨0, by linarith⟩ : Fin k)]
      · simp [h.1]
      · intro b _ hb
        simp [y, hb]
      · intro h
        exact absurd (h (Finset.mem_univ _)) (by simp)
  · -- Case: either x₀ ≠ 0 or x₁ ≠ 0, use y = (-x₁, x₀, 0, ..., 0)
    let i0 : Fin k := ⟨0, by linarith⟩
    let i1 : Fin k := ⟨1, by omega⟩
    let y : EuclideanSpace ℝ (Fin k) := WithLp.toLp (p := 2) (V := Fin k → ℝ) (fun j =>
      if j = i0 then -x i1 else if j = i1 then x i0 else 0)
    refine ⟨y, ?_, ?_⟩
    · intro hy
      simp [y] at hy
      by_cases hx0 : x i0 = 0
      · have := congrFun hy i0
        simp [y, i0, i1] at this
        exact h ⟨hx0, this⟩
      · have := congrFun hy i1
        simp [y, i0, i1] at this
        exact hx0 this
    · simp [inner, WithLp.ofLp_toLp, y]
      rw [Finset.sum_ite, Finset.sum_ite]
      simp [Finset.sum_filter]
      simp [i0, i1]
      ring

/-- In one dimension a nonzero vector has no nonzero orthogonal vector. -/
theorem one_dimensional_no_nonzero_orthogonal {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    x * y ≠ 0 := by
  sorry

/-- The Apollonius sphere with distance ratio two.  The positivity condition on
`r` requires distinct foci, which is implicit in the exercise's request `r > 0`. -/
theorem apollonius_sphere {k : ℕ} (a b : EuclideanSpace ℝ (Fin k)) (hab : a ≠ b) :
    let c := ((4 : ℝ) / 3) • b - ((1 : ℝ) / 3) • a
    let r := ((2 : ℝ) / 3) * dist b a
    0 < r ∧ ∀ x, (dist x a = 2 * dist x b ↔ dist x c = r) := by
  sorry

end Rudin.Chapter1
