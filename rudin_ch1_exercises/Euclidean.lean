import Mathlib

open scoped BigOperators RealInnerProductSpace

namespace Rudin.Chapter1

private lemma equal_radius_spheres_empty {k : ℕ} (x y : EuclideanSpace ℝ (Fin k))
    (r : ℝ) (hfar : 2 * r < dist x y) :
    {z | dist z x = r ∧ dist z y = r} = ∅ := by
  ext z
  simp
  intro hzx hzy
  have : dist x y ≤ dist x z + dist z y := dist_triangle x z y
  rw [dist_comm x z] at this
  rw [hzx, hzy] at this
  linarith

private lemma equal_radius_spheres_singleton {k : ℕ} (x y : EuclideanSpace ℝ (Fin k))
    (r : ℝ) (hr : 0 < r) (htangent : 2 * r = dist x y) :
    {z | dist z x = r ∧ dist z y = r} = {(2 : ℝ)⁻¹ • (x + y)} := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro ⟨hzx, hzy⟩
    -- Use parallelogram identity: ‖(z-x)+(z-y)‖² + ‖(z-x)-(z-y)‖² = 2(‖z-x‖² + ‖z-y‖²)
    -- Since ‖z-x‖ = ‖z-y‖ = r and ‖x-y‖ = 2r, we get ‖2z - x - y‖ = 0
    have h1 : ‖z - x‖ = r := hzx
    have h2 : ‖z - y‖ = r := hzy
    have h3 : ‖x - y‖ = 2 * r := by rw [dist_eq_norm] at htangent; exact htangent.symm
    have h4 : ‖(z - x) - (z - y)‖ = ‖y - x‖ := by simp [sub_sub_sub_cancel_left]
    have h5 : ‖y - x‖ = 2 * r := by rw [norm_sub_rev]; exact h3
    have h6 : ‖(z - x) + (z - y)‖ ^ 2 + ‖(z - x) - (z - y)‖ ^ 2 = 2 * ‖z - x‖ ^ 2 + 2 * ‖z - y‖ ^ 2 := by
      have h1 : ‖(z - x) + (z - y)‖ ^ 2 = inner ℝ ((z - x) + (z - y)) ((z - x) + (z - y)) :=
        (real_inner_self_eq_norm_sq _).symm
      have h2 : ‖(z - x) - (z - y)‖ ^ 2 = inner ℝ ((z - x) - (z - y)) ((z - x) - (z - y)) :=
        (real_inner_self_eq_norm_sq _).symm
      have h3 : ‖z - x‖ ^ 2 = inner ℝ (z - x) (z - x) :=
        (real_inner_self_eq_norm_sq _).symm
      have h4 : ‖z - y‖ ^ 2 = inner ℝ (z - y) (z - y) :=
        (real_inner_self_eq_norm_sq _).symm
      rw [h1, h2, h3, h4]
      simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
      ring
    have h7 : ‖(z - x) + (z - y)‖ ^ 2 = 0 := by
      rw [h4, h5, h1, h2] at h6
      linarith
    have h8 : ‖(z - x) + (z - y)‖ = 0 := by nlinarith [sq_nonneg ‖(z - x) + (z - y)‖]
    have h9 : (z - x) + (z - y) = 0 := norm_eq_zero.mp h8
    have h10 : (2 : ℝ) • z = x + y := by
      have heq : z + z = x + y := by
        calc z + z = (z - x) + (z - y) + (x + y) := by abel
          _ = x + y := by rw [h9]; simp
      convert heq using 1
      rw [show (2 : ℝ) = (1 : ℝ) + 1 by norm_num, add_smul (M := EuclideanSpace ℝ (Fin k)), one_smul]
    have h11 : z = (2 : ℝ)⁻¹ • ((2 : ℝ) • z) := by
      rw [smul_smul]
      norm_num
    rw [h11, h10]
  · intro hz
    rw [hz]
    constructor <;> have : dist x y = 2 * r := htangent.symm
    · rw [dist_eq_norm]
      have : (2 : ℝ)⁻¹ • (x + y) - x = (2 : ℝ)⁻¹ • (y - x) := by
        ext; simp; ring
      rw [this, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
      rw [dist_eq_norm, norm_sub_rev] at htangent
      field_simp
      linarith
    · rw [dist_eq_norm]
      have : (2 : ℝ)⁻¹ • (x + y) - y = (2 : ℝ)⁻¹ • (x - y) := by
        ext; simp; ring
      rw [this, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
      have h1 : ‖x - y‖ = 2 * r := htangent.symm
      rw [h1]
      ring

private lemma equal_radius_spheres_infinite {k : ℕ} (hk : 3 ≤ k)
    (x y : EuclideanSpace ℝ (Fin k)) (r : ℝ) (hr : 0 < r) (hxy : x ≠ y)
    (hclose : dist x y < 2 * r) :
    Set.Infinite {z | dist z x = r ∧ dist z y = r} := by
  sorry

/-- The trichotomy for intersections of two equal-radius spheres.  For dimensions at
least three, the intersection is infinite exactly when the centers are less than
`2r` apart. -/
theorem equal_radius_spheres {k : ℕ} (hk : 3 ≤ k) (x y : EuclideanSpace ℝ (Fin k))
    (r : ℝ) (hr : 0 < r) (hxy : x ≠ y) :
    let d := dist x y
    (2 * r < d → {z | dist z x = r ∧ dist z y = r} = ∅) ∧
    (2 * r = d → {z | dist z x = r ∧ dist z y = r} = {(2 : ℝ)⁻¹ • (x + y)}) ∧
    (d < 2 * r → Set.Infinite {z | dist z x = r ∧ dist z y = r}) := by
  exact ⟨equal_radius_spheres_empty x y r,
    equal_radius_spheres_singleton x y r hr,
    equal_radius_spheres_infinite hk x y r hr hxy⟩

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
  ext z
  simp
  intro hzx hzy
  simp only [Real.dist_eq] at hclose hzx hzy
  rw [abs_eq (le_of_lt hr)] at hzx hzy
  rw [abs_lt] at hclose
  rcases hzx with hzx | hzx <;> rcases hzy with hzy | hzy
  all_goals first | exact hxy (by linarith) | linarith

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
  by_cases hx : x = 0
  · use EuclideanSpace.single ⟨0, by omega⟩ 1
    simp [hx]
  · by_cases hx0 : x ⟨0, by omega⟩ = 0
    · use EuclideanSpace.single ⟨0, by omega⟩ 1
      refine ⟨?_, ?_⟩
      · intro h
        have := congr_arg (fun y : EuclideanSpace ℝ (Fin k) => y ⟨0, by omega⟩) h
        simp at this
      · simp only [inner]
        rw [Finset.sum_eq_single ⟨0, by omega⟩]
        · simp [hx0]
        · intro b _ hb
          simp [EuclideanSpace.single_apply, hb]
        · intro h
          exact absurd (Finset.mem_univ _) h
    · let i0 : Fin k := ⟨0, by omega⟩
      let i1 : Fin k := ⟨1, by omega⟩
      use (x i1) • EuclideanSpace.single i0 1 - (x i0) • EuclideanSpace.single i1 1
      refine ⟨?_, ?_⟩
      · intro h
        have := congr_arg (fun y : EuclideanSpace ℝ (Fin k) => y i1) h
        have hne : i1 ≠ i0 := by simp [i0, i1]
        simp [EuclideanSpace.single_apply, hne] at this
        exact hx0 this
      · rw [inner_sub_right, inner_smul_right, inner_smul_right]
        have h1 : ⟪x, EuclideanSpace.single i0 1⟫ = x i0 := by
          simp only [inner]
          rw [Finset.sum_eq_single i0]
          · simp
          · intro b _ hb
            simp [EuclideanSpace.single_apply, hb]
          · simp
        have h2 : ⟪x, EuclideanSpace.single i1 1⟫ = x i1 := by
          simp only [inner]
          rw [Finset.sum_eq_single i1]
          · simp
          · intro b _ hb
            simp [EuclideanSpace.single_apply, hb]
          · simp
        rw [h1, h2]
        ring

/-- In one dimension a nonzero vector has no nonzero orthogonal vector. -/
theorem one_dimensional_no_nonzero_orthogonal {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    x * y ≠ 0 := by
  exact mul_ne_zero hx hy

/-- The Apollonius sphere with distance ratio two.  The positivity condition on
`r` requires distinct foci, which is implicit in the exercise's request `r > 0`. -/
theorem apollonius_sphere {k : ℕ} (a b : EuclideanSpace ℝ (Fin k)) (hab : a ≠ b) :
    let c := ((4 : ℝ) / 3) • b - ((1 : ℝ) / 3) • a
    let r := ((2 : ℝ) / 3) * dist b a
    0 < r ∧ ∀ x, (dist x a = 2 * dist x b ↔ dist x c = r) := by
  refine ⟨?_, ?_⟩
  · apply mul_pos
    · norm_num
    · exact dist_pos.mpr (Ne.symm hab)
  · intro x
    have h1 : dist x a = 2 * dist x b ↔ (dist x a) ^ 2 = 4 * (dist x b) ^ 2 := by
      exact ⟨fun h => by rw [h]; ring, fun h => by nlinarith [sq_nonneg (dist x a), sq_nonneg (dist x b), sq_nonneg (dist x a - 2 * dist x b), sq_nonneg (dist x a + 2 * dist x b), dist_nonneg (x := x) (y := a), dist_nonneg (x := x) (y := b)]⟩
    have h2 : dist x (((4 : ℝ) / 3) • b - ((1 : ℝ) / 3) • a) = ((2 : ℝ) / 3) * dist b a ↔
               (dist x (((4 : ℝ) / 3) • b - ((1 : ℝ) / 3) • a)) ^ 2 = ((4 : ℝ) / 9) * (dist b a) ^ 2 := by
      have := sq_eq_sq₀ (by positivity : (0:ℝ) ≤ dist x (((4 : ℝ) / 3) • b - ((1 : ℝ) / 3) • a))
                        (by positivity : (0:ℝ) ≤ ((2 : ℝ) / 3) * dist b a)
      simp only [mul_pow] at this
      convert this.symm using 2
      norm_num
    have h3 : (dist x a) ^ 2 = 4 * (dist x b) ^ 2 ↔
              (dist x (((4 : ℝ) / 3) • b - ((1 : ℝ) / 3) • a)) ^ 2 = ((4 : ℝ) / 9) * (dist b a) ^ 2 := by
      simp [dist_eq_norm]
      have eq1 : x - ((4 / 3 : ℝ) • b - (3 : ℝ)⁻¹ • a) = (x - a) - ((4 : ℝ) / 3) • (b - a) := by
        ext i; simp; ring
      rw [eq1]
      suffices hsuff : ∀ (y d : EuclideanSpace ℝ (Fin k)),
          ‖y‖ ^ 2 = 4 * ‖y - d‖ ^ 2 ↔ ‖y - (4 / 3 : ℝ) • d‖ ^ 2 = (4 / 9) * ‖d‖ ^ 2 by
        have eq3 : x - b = (x - a) - (b - a) := by simp
        rw [eq3]
        exact hsuff (x - a) (b - a)
      intro y d
      rw [← real_inner_self_eq_norm_sq y, ← real_inner_self_eq_norm_sq (y - d),
          ← real_inner_self_eq_norm_sq (y - (4/3 : ℝ) • d), ← real_inner_self_eq_norm_sq d]
      simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        real_inner_comm y d]
      simp
      constructor <;> intro h <;> nlinarith [sq_nonneg (inner ℝ y d)]
    exact h1.trans (h3.trans h2.symm)

end Rudin.Chapter1
