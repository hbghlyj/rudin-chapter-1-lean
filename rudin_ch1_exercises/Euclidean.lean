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

private lemma exists_orthonormal_pair_perpendicular {k : ℕ} (hk : 3 ≤ k)
    (d : EuclideanSpace ℝ (Fin k)) (hd : d ≠ 0) :
    ∃ u v : EuclideanSpace ℝ (Fin k),
      ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ inner ℝ d u = 0 ∧ inner ℝ d v = 0 ∧ inner ℝ u v = 0 := by
  -- Find indices 0, 1, 2 since k ≥ 3
  let i0 : Fin k := ⟨0, by omega⟩
  let i1 : Fin k := ⟨1, by omega⟩
  let i2 : Fin k := ⟨2, by omega⟩
  have heq01 : i0 ≠ i1 := by simp [i0, i1]
  have heq02 : i0 ≠ i2 := by simp [i0, i2]
  have heq12 : i1 ≠ i2 := by simp [i1, i2]
  -- First construct w = d_1 * e_0 - d_0 * e_1 (perpendicular to d)
  let w : EuclideanSpace ℝ (Fin k) := d i1 • EuclideanSpace.single i0 1 - d i0 • EuclideanSpace.single i1 1
  by_cases hw : w = 0
  · -- If w = 0, then d_0 = d_1 = 0, so we can use e_0 and e_1
    have hne01 : i0 ≠ i1 := heq01
    have hd0 : d i0 = 0 := by
      have := congr_arg (fun x => x i1) hw
      simp only [w] at this
      simp [EuclideanSpace.single_apply, if_neg hne01.symm] at this
      linarith
    have hd1 : d i1 = 0 := by
      have := congr_arg (fun x => x i0) hw
      simp only [w] at this
      simp [EuclideanSpace.single_apply, if_neg hne01] at this
      linarith
    use EuclideanSpace.single i0 1, EuclideanSpace.single i1 1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [EuclideanSpace.norm_single]
    · simp [EuclideanSpace.norm_single]
    · simp only [inner, PiLp.inner_apply]
      rw [Finset.sum_eq_single i0]
      · simp [hd0]
      · intro b _ hb
        simp [EuclideanSpace.single_apply, hb]
      · simp
    · simp only [inner, PiLp.inner_apply]
      rw [Finset.sum_eq_single i1]
      · simp [hd1]
      · intro b _ hb
        simp [EuclideanSpace.single_apply, hb]
      · simp
    · simp only [inner, PiLp.inner_apply]
      rw [Finset.sum_eq_single i0]
      · simp [heq01]
      · intro b _ hb
        simp [EuclideanSpace.single_apply, hb]
      · simp
  · -- w ≠ 0 case: normalize w to get u
    have hw_norm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hw_inner_d : inner ℝ d w = 0 := by
      simp only [w, inner_sub_right, inner_smul_right, inner_smul_right]
      simp [EuclideanSpace.inner_single_right]
      ring
    let u := (1 / ‖w‖) • w
    have hu_norm : ‖u‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ‖w‖)]
      field_simp
    have hu_ortho_d : inner ℝ d u = 0 := by
      rw [inner_smul_right, hw_inner_d, mul_zero]
    -- Construct w2 = d_2 * e_0 - d_0 * e_2 (perpendicular to d)
    let w2 : EuclideanSpace ℝ (Fin k) := d i2 • EuclideanSpace.single i0 1 - d i0 • EuclideanSpace.single i2 1
    have hw2_inner_d : inner ℝ d w2 = 0 := by
      simp only [w2, inner_sub_right, inner_smul_right, inner_smul_right]
      simp [EuclideanSpace.inner_single_right]
      ring
    -- Orthogonalize w2 against w to get w2'
    let scalar := inner ℝ w2 w / inner ℝ w w
    let w2' : EuclideanSpace ℝ (Fin k) := w2 - scalar • w
    have hw2'_inner_w : inner ℝ (w2 - scalar • w) w = 0 := by
      rw [inner_sub_left, inner_smul_left]
      simp [scalar]
      field_simp
      ring
    have hw2'_inner_d : inner ℝ (w2 - scalar • w) d = 0 := by
      rw [inner_sub_left, inner_smul_left]
      have h1 : inner ℝ w2 d = 0 := hw2_inner_d ▸ inner_conj_symm d w2
      have h2 : inner ℝ w d = 0 := hw_inner_d ▸ inner_conj_symm d w
      simp [h1, h2]
    -- Check w2' ≠ 0
    by_cases hw2'_ne : w2' = 0
    · -- w2' = 0 means w2 is parallel to w, which happens when d i0 = 0
      -- Use w3 = d i2 • e_1 - d i1 • e_2 instead
      let w3 : EuclideanSpace ℝ (Fin k) := d i2 • EuclideanSpace.single i1 1 - d i1 • EuclideanSpace.single i2 1
      have hw3_inner_d : inner ℝ d w3 = 0 := by
        have h1 : inner ℝ d (EuclideanSpace.single i1 1) = d i1 := by
          simp [EuclideanSpace.inner_single_right]
        have h2 : inner ℝ d (EuclideanSpace.single i2 1) = d i2 := by
          simp [EuclideanSpace.inner_single_right]
        simp only [w3, inner_sub_right, inner_smul_right, h1, h2]
        ring
      -- Orthogonalize w3 against w to get w3'
      let scalar3 := inner ℝ w3 w / inner ℝ w w
      let w3' : EuclideanSpace ℝ (Fin k) := w3 - scalar3 • w
      have hw3'_inner_w : inner ℝ w3' w = 0 := by
        rw [inner_sub_left, inner_smul_left]
        simp only [scalar3]
        simp [map_div₀]
        rw [div_mul_cancel₀]
        · simp
        · exact pow_ne_zero 2 hw_norm_pos.ne'
      have hw3'_inner_d : inner ℝ w3' d = 0 := by
        rw [inner_sub_left, inner_smul_left]
        have h1 : inner ℝ w3 d = 0 := hw3_inner_d ▸ inner_conj_symm d w3
        have h2 : inner ℝ w d = 0 := hw_inner_d ▸ inner_conj_symm d w
        simp [h1, h2]
      by_cases hw3'_ne : w3' = 0
      · -- Both w2' = 0 and w3' = 0 means w = 0 (contradiction with hw)
        exfalso
        apply hw
        -- w = d i1 • e_0 - d i0 • e_1
        -- From w2' = 0: w2 = scalar • w. At index 0: w2 i0 = d i2, w i0 = d i1
        --   So d i2 = scalar * d i1
        -- From w3' = 0: w3 = scalar3 • w. At index 2: w3 i2 = -d i1, w i2 = 0
        --   So -d i1 = scalar3 * 0 = 0, hence d i1 = 0
        have hdi1 : d i1 = 0 := by
          have h : w3 = scalar3 • w := sub_eq_zero.mp hw3'_ne
          have eq := congr_arg (fun x => x i2) h
          simp [w3, w, EuclideanSpace.single_apply, smul_eq_mul, heq12.symm, heq01.symm, heq02.symm] at eq
          linarith
        -- At index 1: w3 i1 = d i2, w i1 = -d i0
        -- So d i2 = scalar3 * (-d i0) = -scalar3 * d i0
        -- From w2' = 0: at index 0: w2 i0 = d i2, w i0 = d i1 = 0
        -- So d i2 = scalar * 0 = 0
        have hdi2 : d i2 = 0 := by
          have h2 : w2 = scalar • w := sub_eq_zero.mp hw2'_ne
          have eq := congr_arg (fun x => x i0) h2
          simp [w2, w, EuclideanSpace.single_apply, smul_eq_mul, heq02, heq01, hdi1] at eq
          linarith
        -- Now d i1 = 0 and d i2 = 0
        -- From w2 = scalar • w at index 2: w2 i2 = scalar * w i2
        -- w2 i2 = -d i0, w i2 = 0, so d i0 = 0
        have hdi0 : d i0 = 0 := by
          have h2 : w2 = scalar • w := sub_eq_zero.mp hw2'_ne
          have eq := congr_arg (fun x => x i2) h2
          simp [w2, w, EuclideanSpace.single_apply, smul_eq_mul, heq02.symm, heq12.symm, hdi1] at eq
          linarith
        -- Now w = d i1 • e_0 - d i0 • e_1 = 0 • e_0 - 0 • e_1 = 0
        ext j
        simp [w, hdi1, hdi0]
      · -- Normalize w3' to get v
        have hw3'_norm_pos : 0 < ‖w3'‖ := norm_pos_iff.mpr hw3'_ne
        let v := (1 / ‖w3'‖) • w3'
        have hv_norm : ‖v‖ = 1 := by
          rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ‖w3'‖)]
          field_simp
        have hv_ortho_d : inner ℝ d v = 0 := by
          simp only [v, inner_smul_right]
          rw [real_inner_comm, hw3'_inner_d]
          ring
        have hv_ortho_u : inner ℝ u v = 0 := by
          simp only [v, inner_smul_right]
          have hu_eq : u = (1 / ‖w‖) • w := rfl
          rw [hu_eq, inner_smul_left, real_inner_comm]
          rw [hw3'_inner_w]
          ring
        exact ⟨u, v, hu_norm, hv_norm, hu_ortho_d, hv_ortho_d, hv_ortho_u⟩
    · -- w2' ≠ 0 case: use w2' as v
      have hw2'_norm_pos : 0 < ‖w2'‖ := norm_pos_iff.mpr hw2'_ne
      let v := (1 / ‖w2'‖) • w2'
      have hv_norm : ‖v‖ = 1 := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ‖w2'‖)]
        field_simp
      have hv_ortho_d : inner ℝ d v = 0 := by
        simp only [v, inner_smul_right]
        rw [real_inner_comm, hw2'_inner_d]
        ring
      have hv_ortho_u : inner ℝ u v = 0 := by
        simp only [v, inner_smul_right]
        have hu_eq : u = (1 / ‖w‖) • w := rfl
        rw [hu_eq, inner_smul_left, real_inner_comm]
        rw [hw2'_inner_w]
        ring
      exact ⟨u, v, hu_norm, hv_norm, hu_ortho_d, hv_ortho_d, hv_ortho_u⟩

private noncomputable def circleParam {k : ℕ} (u v : EuclideanSpace ℝ (Fin k)) (t : ℝ) :
    EuclideanSpace ℝ (Fin k) :=
  ((1 - t ^ 2) / (1 + t ^ 2)) • u + ((2 * t) / (1 + t ^ 2)) • v

private lemma circleParam_norm {k : ℕ} {u v : EuclideanSpace ℝ (Fin k)}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0) (t : ℝ) :
    ‖circleParam u v t‖ = 1 := by
  sorry

private lemma circleParam_orthogonal {k : ℕ} {d u v : EuclideanSpace ℝ (Fin k)}
    (hdu : inner ℝ d u = 0) (hdv : inner ℝ d v = 0) (t : ℝ) :
    inner ℝ d (circleParam u v t) = 0 := by
  simp only [circleParam]
  rw [inner_add_right]
  simp [inner_smul_right, hdu, hdv]

private lemma circleParam_injective {k : ℕ} {u v : EuclideanSpace ℝ (Fin k)}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0) :
    Function.Injective (circleParam u v) := by
  sorry

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
