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
  rw [← Real.rpow_mul (le_of_lt hb), ← Real.rpow_mul (le_of_lt hb)]
  congr 1
  rw [div_eq_mul_inv, div_eq_mul_inv] at hfrac
  have : ((m : ℚ) * (n : ℚ)⁻¹ : ℝ) = ((p : ℚ) * (q : ℚ)⁻¹ : ℝ) := by exact_mod_cast hfrac
  simp at this
  exact this

/-- The addition law for rational exponents. -/
theorem rational_rpow_add {b : ℝ} (hb : 0 < b) (r s : ℚ) :
    b ^ ((r + s : ℚ) : ℝ) = b ^ (r : ℝ) * b ^ (s : ℝ) := by
  rw [← Real.rpow_add hb]
  norm_cast

/-- At a rational argument, Rudin's supremum construction gives the rational power. -/
theorem rational_power_is_sup {b : ℝ} (hb : 1 < b) (r : ℚ) :
    IsLUB (rationalPowerSet b (r : ℝ)) (b ^ (r : ℝ)) := by
  constructor
  · -- Show b ^ r is an upper bound
    intro y hy
    obtain ⟨t, ht, rfl⟩ := hy
    exact Real.rpow_le_rpow_of_exponent_le hb.le ht
  · -- Show b ^ r is the least upper bound
    intro M hM
    exact hM ⟨r, le_refl _, rfl⟩

/-- Rudin's supremum definition agrees with real exponentiation. -/
theorem rpow_eq_sup_rationalPowerSet {b x : ℝ} (hb : 1 < b) :
    b ^ x = sSup (rationalPowerSet b x) := by
  apply le_antisymm
  · -- b^x is ≤ the supremum (supremum is ≥ b^x)
    rw [le_csSup_iff]
    · intro c hc
      by_contra h
      push_neg at h
      -- There exists ε > 0 such that c + ε < b^x
      obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, c + ε < b ^ x := ⟨(b ^ x - c) / 2, by linarith, by linarith⟩
      -- Use continuity: there exists δ > 0 such that t ∈ (x-δ, x+δ) implies b^t > c
      have hcont : ContinuousAt (fun t => b ^ t) x := (continuous_const.rpow continuous_id <| by intros; exact Or.inl (ne_of_gt (by linarith : 0 < b))).continuousAt
      rw [Metric.continuousAt_iff] at hcont
      obtain ⟨δ, hδ_pos, hδ⟩ := hcont ((b ^ x - c) / 2) (by linarith)
      -- Find a rational t with x - δ < t ≤ x
      obtain ⟨t, ht₁, ht₂⟩ := exists_rat_btwn (by linarith : x - δ < x)
      -- t satisfies x - δ < t < x, so |t - x| < δ
      have ht_dist : dist (t : ℝ) x < δ := by
        rw [Real.dist_eq]
        rw [abs_lt]
        constructor <;> linarith
      have ht_le : (t : ℝ) ≤ x := by linarith
      -- Apply continuity bound
      have ht_rpow : dist (b ^ (t : ℝ)) (b ^ x) < (b ^ x - c) / 2 := hδ ht_dist
      -- From distance bound, b^t > c
      have ht_gt_c : b ^ (t : ℝ) > c := by
        rw [Real.dist_eq] at ht_rpow
        have : |b ^ (t : ℝ) - b ^ x| < (b ^ x - c) / 2 := ht_rpow
        linarith [abs_lt.mp this]
      -- But c is an upper bound
      have ht_mem : b ^ (t : ℝ) ∈ rationalPowerSet b x := ⟨t, ht_le, rfl⟩
      have hcb : b ^ (t : ℝ) ≤ c := hc ht_mem
      linarith
    · use b ^ x
      intro y hy
      obtain ⟨t, ht, rfl⟩ := hy
      exact Real.rpow_le_rpow_of_exponent_le hb.le ht
    · use b ^ ((⌊x⌋ : ℚ) : ℝ)
      refine ⟨(⌊x⌋ : ℚ), ?_, rfl⟩
      simp [Int.floor_le]
  · -- supremum is ≤ b^x (b^x is an upper bound)
    apply csSup_le
    · use (b ^ ((⌊x⌋ : ℚ) : ℝ))
      refine ⟨(⌊x⌋ : ℚ), ?_, ?_⟩
      · simp [Int.floor_le]
      · norm_cast
    · intro y hy
      obtain ⟨t, ht, rfl⟩ := hy
      exact Real.rpow_le_rpow_of_exponent_le hb.le ht

/-- The exponent addition law for all real exponents. -/
theorem real_rpow_add {b : ℝ} (hb : 0 < b) (x y : ℝ) :
    b ^ (x + y) = b ^ x * b ^ y := by
  exact Real.rpow_add hb x y

/-- Exercise 7(a), Bernoulli's inequality for a base greater than one. -/
theorem pow_sub_one_ge {b : ℝ} (hb : 1 < b) {n : ℕ} (hn : 0 < n) :
    n * (b - 1) ≤ b ^ n - 1 := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    by_cases hz : n = 0
    · simp [hz]
    · have hn' : 0 < n := Nat.pos_of_ne_zero hz
      have ih' := ih hn'
      have hb_pow : 1 ≤ b ^ n := one_le_pow₀ hb.le
      have key : b * (b ^ n - 1) + (b - 1) = b ^ (n + 1) - 1 := by ring
      rw [← key]
      have cast_eq : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_cast
      rw [cast_eq]
      ring_nf
      have h1 : (n : ℝ) * (b - 1) + (b - 1) ≤ b * (b ^ n - 1) + (b - 1) := by
        nlinarith
      linarith

/-- Exercise 7(b), the corresponding bound for positive `n`th roots. -/
theorem root_sub_one_bound {b : ℝ} (hb : 1 < b) {n : ℕ} (hn : 0 < n) :
    n * (b ^ ((n : ℝ)⁻¹) - 1) ≤ b - 1 := by
  set a := b ^ ((n : ℝ)⁻¹) with ha_def
  have ha_pos : 1 < a := Real.one_lt_rpow hb (by positivity : (n : ℝ)⁻¹ > 0)
  have bernoulli := pow_sub_one_ge ha_pos hn
  have haken : a ^ n = b := by
    rw [ha_def, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (lt_trans zero_lt_one hb))]
    simp [hn.ne']
  linarith

/-- Exercise 7(c): sufficiently high roots of `b` lie below every `t > 1`. -/
theorem root_lt_of_large_n {b t : ℝ} (hb : 1 < b) (ht : 1 < t) {n : ℕ}
    (hn : (b - 1) / (t - 1) < n) : b ^ ((n : ℝ)⁻¹) < t := by
  have hn' : 0 < n := by
    by_contra h
    push_neg at h
    interval_cases n
    simp at hn
    linarith [div_nonneg (by linarith : 0 ≤ b - 1) (by linarith : 0 ≤ t - 1)]
  have hn'' : (0 : ℝ) < n := Nat.cast_pos.mpr hn'
  have hdiv : b - 1 < n * (t - 1) := by
    have hsub : 0 < t - 1 := by linarith
    rwa [div_lt_iff₀ hsub] at hn
  have hbound := root_sub_one_bound hb hn'
  have : n * (b ^ ((n : ℝ)⁻¹) - 1) < n * (t - 1) := lt_of_le_of_lt hbound hdiv
  have : b ^ ((n : ℝ)⁻¹) - 1 < t - 1 := by nlinarith
  linarith

/-- Exercise 7(d). -/
theorem rpow_step_up_below {b y w : ℝ} (hb : 1 < b) (hy : 0 < y)
    (hw : b ^ w < y) : ∃ n : ℕ, 0 < n ∧ b ^ (w + (n : ℝ)⁻¹) < y := by
  have hbpos : 0 < b := lt_trans (by norm_num : (0 : ℝ) < 1) hb
  have hbw_pos : 0 < b ^ w := Real.rpow_pos_of_pos hbpos w
  set t := y / b ^ w with ht_def
  have ht_gt_one : 1 < t := by rw [ht_def]; rw [lt_div_iff₀ hbw_pos]; linarith
  -- Find n such that (b - 1) / (t - 1) < n
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - 1) / (t - 1))
  have hn_pos : 0 < n := Nat.pos_of_ne_zero fun h => by
    simp [h] at hn
    have hb1 : 0 < b - 1 := by linarith
    have ht1 : 0 < t - 1 := by linarith
    linarith [div_pos hb1 ht1]
  have hn' := root_lt_of_large_n hb ht_gt_one hn
  use n, hn_pos
  calc b ^ (w + (n : ℝ)⁻¹) = b ^ w * b ^ ((n : ℝ)⁻¹) := by rw [← Real.rpow_add hbpos]
    _ < b ^ w * t := by apply mul_lt_mul_of_pos_left hn' hbw_pos
    _ = y := by rw [mul_div_cancel₀ _ (ne_of_gt hbw_pos)]

/-- Exercise 7(e). -/
theorem rpow_step_down_above {b y w : ℝ} (hb : 1 < b) (hy : 0 < y)
    (hw : y < b ^ w) : ∃ n : ℕ, 0 < n ∧ y < b ^ (w - (n : ℝ)⁻¹) := by
  have hbpos : 0 < b := lt_trans zero_lt_one hb
  have hbwpow : 0 < b ^ w := Real.rpow_pos_of_pos hbpos w
  have ht : 1 < b ^ w / y := one_lt_div hy |>.mpr hw
  have hpos : 0 < b ^ w / y - 1 := by linarith
  set n : ℕ := ⌊(b - 1) / (b ^ w / y - 1)⌋₊ + 1 with hn_def
  have hn_pos : 0 < n := Nat.succ_pos _
  have hdiff : (b - 1) / (b ^ w / y - 1) < (n : ℝ) := by
    simp [hn_def]
    exact Nat.lt_floor_add_one _
  have hroot := root_lt_of_large_n hb ht hdiff
  refine ⟨n, hn_pos, ?_⟩
  rw [Real.rpow_sub hbpos]
  have hb_pow_pos : (0 : ℝ) < b ^ (↑n : ℝ)⁻¹ := Real.rpow_pos_of_pos hbpos _
  rw [lt_div_iff₀ hb_pow_pos]
  calc y * b ^ (↑n : ℝ)⁻¹ < y * (b ^ w / y) := by
        apply mul_lt_mul_of_pos_left hroot hy
    _ = b ^ w := by field_simp

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
