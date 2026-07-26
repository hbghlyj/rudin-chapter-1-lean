import Mathlib

open scoped BigOperators ComplexConjugate

namespace Rudin.Chapter1

/-- Negation interchanges infimum and supremum for a nonempty, lower-bounded real set. -/
theorem inf_eq_neg_sup_neg {A : Set ℝ} (_hne : A.Nonempty) (_hbelow : BddBelow A) :
    sInf A = -sSup ((fun x : ℝ => -x) '' A) := by
  have hi : (fun x : ℝ => -x) '' A = -A := by ext x; simp
  rw [hi, ← Real.sInf_neg]
  simp

/-- Every positive real has a unique logarithm to a base greater than one. -/
theorem exists_unique_rpow_eq {b y : ℝ} (hb : 1 < b) (hy : 0 < y) :
    ∃! x : ℝ, b ^ x = y := by
  have hbpos : 0 < b := lt_trans (by norm_num) hb
  have hbne : b ≠ 1 := ne_of_gt hb
  refine ⟨Real.logb b y, Real.rpow_logb hbpos hbne hy, ?_⟩
  intro z hz
  exact (Real.strictMono_rpow_of_base_gt_one hb).injective
    (hz.trans (Real.rpow_logb hbpos hbne hy).symm)

/-- No linear order compatible with the ring operations can exist on `ℂ`. -/
theorem complex_cannot_be_ordered_field :
    ¬ ∃ (_ : LinearOrder ℂ), ∃ (_ : IsStrictOrderedRing ℂ), True := by
  sorry

/-- The lexicographic order on complex numbers, viewed as pairs of reals. -/
noncomputable def complexLex : LinearOrder ℂ := LinearOrder.lift' (fun z : ℂ => toLex (z.re, z.im)) (by
  intro z w h
  apply Complex.ext <;> simp_all)

/-- In the complex lexicographic order, the imaginary axis is bounded above. -/
theorem imaginaryAxis_bddAbove_lex :
    letI := complexLex
    BddAbove {z : ℂ | z.re = 0} := by
  simp [bddAbove_def]
  use 1
  intro z hz
  have h : ∀ a b : ℂ, letI := complexLex; a ≤ b ↔ toLex (a.re, a.im) ≤ toLex (b.re, b.im) := by
    intro a b
    rfl
  rw [h]
  simp only [hz, Complex.one_re, Complex.one_im]
  have hlt : (0 : ℝ) < 1 := by norm_num
  have h : Prod.Lex (fun a b => a < b) (fun a b => a ≤ b) ((0 : ℝ), z.im) ((1 : ℝ), 0) :=
    Prod.Lex.left (α := ℝ) (β := ℝ) (ra := fun a b => a < b) (rb := fun a b => a ≤ b) (a₁ := 0) (a₂ := 1) (b₁ := z.im) (b₂ := (0 : ℝ)) hlt
  exact h

/-- The imaginary axis has no least upper bound in the complex lexicographic order. -/
theorem imaginaryAxis_no_sup_lex :
    letI := complexLex
    ¬ ∃ s : ℂ, IsLUB {z : ℂ | z.re = 0} s := by
  letI := complexLex
  intro ⟨s, hs⟩
  have hub := hs.1
  have hlu := hs.2
  by_cases hre : s.re > 0
  · -- s.re > 0: construct a smaller upper bound t = (s.re/2, s.im)
    exfalso
    set t : ℂ := ⟨s.re / 2, s.im⟩
    -- t is an upper bound since t.re = s.re/2 > 0
    have ht_upper : t ∈ upperBounds {z : ℂ | z.re = 0} := fun z hz => by
      simp only [Set.mem_setOf_eq] at hz
      change toLex (z.re, z.im) ≤ toLex (t.re, t.im)
      simp [hz, t]
      rw [Prod.Lex.toLex_le_toLex]
      left
      linarith
    -- t < s since s.re/2 < s.re
    have ht_lt_s : t < s := by
      change toLex (t.re, t.im) < toLex (s.re, s.im)
      simp [t]
      rw [Prod.Lex.toLex_lt_toLex]
      left
      linarith
    exact ht_lt_s.not_ge (hlu ht_upper)
  · -- s.re ≤ 0, so s is not an upper bound
    exfalso
    rcases lt_trichotomy s.re 0 with hlt | heq | hgt
    · -- s.re < 0: 0 is in imaginary axis and 0 > s
      have : (0 : ℂ) ∈ {z : ℂ | z.re = 0} := by simp
      have h0_gt_s : (0 : ℂ) > s := by
        rw [show (0 : ℂ) > s ↔ s < (0 : ℂ) from gt_iff_lt]
        change toLex (s.re, s.im) < toLex ((0 : ℂ).re, (0 : ℂ).im)
        simp only [Complex.zero_re, Complex.zero_im]
        left
        exact hlt
      exact not_le_of_gt h0_gt_s (hub this)
    · -- s.re = 0: take z = (0, s.im + 1) which is in imaginary axis and > s
      exfalso
      set z : ℂ := ⟨0, s.im + 1⟩
      have hz : z ∈ {z : ℂ | z.re = 0} := by simp [z]
      have hz_gt_s : z > s := by
        rw [show z > s ↔ s < z from gt_iff_lt]
        change toLex (s.re, s.im) < toLex (z.re, z.im)
        simp [z]
        rw [heq]
        refine Prod.Lex.toLex_lt_toLex.mpr ?_
        right
        constructor
        · rfl
        · linarith
      exact not_le_of_gt hz_gt_s (hub hz)
    · -- s.re > 0 contradicts hre
      exact absurd hgt hre

/-- Rudin's explicit square-root formula in the upper half-plane. -/
theorem complex_square_root_formula_nonneg_im (w : ℂ) (hv : 0 ≤ w.im) :
    let a := Real.sqrt ((norm w + w.re) / 2)
    let b := Real.sqrt ((norm w - w.re) / 2)
    (a + b * Complex.I) ^ 2 = w := by
  apply Complex.ext
  · simp [sq, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    have h1 : 0 ≤ ‖w‖ + w.re := by
      have := Complex.abs_re_le_norm w
      linarith [abs_le.mp this]
    have h2 : 0 ≤ ‖w‖ - w.re := by
      have := Complex.abs_re_le_norm w
      linarith [abs_le.mp this]
    have eq1 : Real.sqrt (‖w‖ + w.re) / Real.sqrt 2 = Real.sqrt ((‖w‖ + w.re) / 2) := by
      rw [Real.sqrt_div h1]
    have eq2 : Real.sqrt (‖w‖ - w.re) / Real.sqrt 2 = Real.sqrt ((‖w‖ - w.re) / 2) := by
      rw [Real.sqrt_div h2]
    rw [eq1, eq2]
    have hr : Real.sqrt ((‖w‖ + w.re) / 2) * Real.sqrt ((‖w‖ + w.re) / 2) = (‖w‖ + w.re) / 2 := Real.mul_self_sqrt (by positivity)
    have hi : Real.sqrt ((‖w‖ - w.re) / 2) * Real.sqrt ((‖w‖ - w.re) / 2) = (‖w‖ - w.re) / 2 := Real.mul_self_sqrt (by positivity)
    linarith
  · simp [sq, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    have h1 : 0 ≤ ‖w‖ + w.re := by
      have := Complex.abs_re_le_norm w
      linarith [abs_le.mp this]
    have h2 : 0 ≤ ‖w‖ - w.re := by
      have := Complex.abs_re_le_norm w
      linarith [abs_le.mp this]
    have eq1 : Real.sqrt (‖w‖ + w.re) / Real.sqrt 2 = Real.sqrt ((‖w‖ + w.re) / 2) := by
      rw [Real.sqrt_div h1]
    have eq2 : Real.sqrt (‖w‖ - w.re) / Real.sqrt 2 = Real.sqrt ((‖w‖ - w.re) / 2) := by
      rw [Real.sqrt_div h2]
    rw [eq1, eq2]
    -- Goal: √((‖w‖ + w.re)/2) * √((‖w‖ - w.re)/2) + √((‖w‖ - w.re)/2) * √((‖w‖ + w.re)/2) = w.im
    -- Simplifies to: 2 * √((‖w‖ + w.re)(‖w‖ - w.re) / 4) = w.im
    have hprod : Real.sqrt ((‖w‖ + w.re) / 2) * Real.sqrt ((‖w‖ - w.re) / 2) = w.im / 2 := by
      rw [← Real.sqrt_mul (by positivity : 0 ≤ (‖w‖ + w.re) / 2)]
      have harg : (‖w‖ + w.re) / 2 * ((‖w‖ - w.re) / 2) = w.im^2 / 4 := by
        have hsq : ‖w‖^2 = w.re^2 + w.im^2 := by
          have := Complex.normSq_eq_norm_sq w
          simp [Complex.normSq_apply] at this
          linarith
        linarith [hsq]
      rw [harg, Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4)]
      rw [Real.sqrt_sq hv]
      norm_num
    have him : Real.sqrt (w.im^2) = w.im := Real.sqrt_sq hv
    rw [hprod]
    linarith

/-- Rudin's explicit square-root formula in the lower half-plane. -/
theorem complex_square_root_formula_nonpos_im (w : ℂ) (hv : w.im ≤ 0) :
    let a := Real.sqrt ((norm w + w.re) / 2)
    let b := Real.sqrt ((norm w - w.re) / 2)
    (star (a + b * Complex.I)) ^ 2 = w := by
  sorry

/-- Every nonzero complex number has exactly two square roots. -/
theorem complex_two_square_roots {z : ℂ} (hz : z ≠ 0) :
    ∃ w : ℂ, w ^ 2 = z ∧ {u : ℂ | u ^ 2 = z} = {w, -w} := by
  sorry

/-- Polar decomposition, including uniqueness away from zero. -/
theorem complex_polar_decomposition (z : ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∃ w : ℂ, norm w = 1 ∧ z = r * w ∧
      (z ≠ 0 → ∀ r' : ℝ, 0 ≤ r' → ∀ w' : ℂ,
        norm w' = 1 → z = r' * w' → r' = r ∧ w' = w) := by
  use norm z
  refine ⟨norm_nonneg z, ?_⟩
  by_cases hz : z = 0
  · -- Case z = 0
    refine ⟨1, ?_, ?_, ?_⟩
    · simp
    · simp [hz]
    · intro hz' r' hr' w' hw' hzw'
      exfalso
      exact hz' hz
  · -- Case z ≠ 0
    use z / norm z
    have hnne : norm z ≠ 0 := norm_ne_zero_iff.mpr hz
    have hn_norm : norm (↑(norm z) : ℂ) = norm z := by simp [Complex.norm_def]
    have h1 : norm (z / norm z) = 1 := by
      rw [norm_div, hn_norm, div_self hnne]
    have h2 : z = norm z * (z / norm z) := by field_simp [hnne]
    refine ⟨h1, h2, ?_⟩
    intro hz' r' hr' w' hw' hzw'
    -- From z = r' * w', take norms: norm z = r' * norm w' = r'
    have hnorm : norm z = r' := by
      rw [hzw']
      simp [hw', Real.norm_eq_abs, abs_of_nonneg hr']
    -- So r' = norm z and w' = z / norm z
    refine ⟨hnorm.symm, ?_⟩
    -- From z = r' * w', we get w' = z / r' = z / norm z
    have hr'pos : r' > 0 := by rw [← hnorm]; exact norm_pos_iff.mpr hz
    have hw'_eq : w' = z / norm z := by
      rw [hnorm]
      have hr'_ne : (r' : ℂ) ≠ 0 := by
        simp [hr'pos.ne']
      rw [eq_div_iff hr'_ne]
      rw [mul_comm]
      exact hzw'.symm
    exact hw'_eq

/-- The triangle inequality for a finite family of complex numbers. -/
theorem complex_sum_abs_le {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    norm (∑ i ∈ s, z i) ≤ ∑ i ∈ s, norm (z i) := by
  apply norm_sum_le

/-- The reverse triangle inequality. -/
theorem complex_reverse_triangle (x y : ℂ) :
    |norm x - norm y| ≤ norm (x - y) := by
  exact abs_norm_sub_norm_le x y

/-- The requested computation for a unit complex number. -/
theorem complex_unit_parallelogram {z : ℂ} (hz : norm z = 1) :
    norm (1 + z) ^ 2 + norm (1 - z) ^ 2 = 4 := by
  have hz' : Complex.normSq z = 1 := by
    have := Complex.normSq_eq_norm_sq z
    simp [hz] at this
    exact this
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_add, Complex.normSq_sub, hz']
  norm_num

/-- Equality in finite-dimensional complex Cauchy--Schwarz holds exactly for
linearly dependent vectors. -/
theorem cauchy_schwarz_equality_iff {n : ℕ} (a b : Fin n → ℂ) :
    norm (∑ j, a j * conj (b j)) ^ 2 =
        (∑ j, norm (a j) ^ 2) * (∑ j, norm (b j) ^ 2) ↔
      ((∀ j, b j = 0) ∨ ∃ c : ℂ, ∀ j, a j = c * b j) := by
  sorry

end Rudin.Chapter1
