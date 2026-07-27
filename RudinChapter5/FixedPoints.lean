import Mathlib
open Set Filter Topology
namespace RudinChapter5

/-- A contraction has at most one fixed point. -/
theorem contraction_fixed_unique {f : ℝ → ℝ} {A : ℝ} (hA : A < 1)
    (hA0 : 0 ≤ A) (hf : LipschitzWith ⟨A, hA0⟩ f) {x y : ℝ}
    (hx : f x = x) (hy : f y = y) : x = y := by
  by_contra hxy
  have hpos : 0 < dist x y := dist_pos.mpr hxy
  have hle := hf.dist_le_mul x y
  rw [hx, hy] at hle
  change dist x y ≤ A * dist x y at hle
  nlinarith [mul_lt_mul_of_pos_right hA hpos]

/-- Newton iteration for `x ↦ x³-a`. -/
noncomputable def newtonCube (a x : ℝ) : ℝ := x - (x ^ 3 - a) / (3 * x ^ 2)

/-- At a nonzero root of `x³=a`, the Newton step is fixed. -/
theorem newtonCube_fixed {a x : ℝ} (hx0 : x ≠ 0) (hx : x ^ 3 = a) :
    newtonCube a x = x := by
  simp [newtonCube, hx, hx0]

end RudinChapter5
