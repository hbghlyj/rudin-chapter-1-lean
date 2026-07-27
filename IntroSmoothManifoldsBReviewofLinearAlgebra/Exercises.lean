import Mathlib

/-! Selected exercises from Appendix B, Review of Linear Algebra. -/

namespace IntroSmoothManifoldsBReviewofLinearAlgebra

/-- Exercise B.9. Every subspace of a vector space over a division ring has a complementary
subspace. -/
theorem subspace_has_complement {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (S : Submodule K V) : ∃ T : Submodule K V, IsCompl S T := by
  exact S.exists_isCompl

/-- Exercise B.13 (uniqueness). Two linear maps agreeing on every member of a basis agree
everywhere. -/
theorem linearMap_eq_of_eq_on_basis {R V W ι : Type*} [Semiring R] [AddCommMonoid V]
    [AddCommMonoid W] [Module R V] [Module R W] (b : Module.Basis ι R V)
    (T T' : V →ₗ[R] W) (h : ∀ i, T (b i) = T' (b i)) : T = T' := by
  exact b.ext h

/-- Exercise B.22(c). In equal finite dimensions, injectivity and surjectivity of a linear map
are equivalent. -/
theorem injective_iff_surjective_of_equal_finrank {K V W : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W] (hVW : Module.finrank K V = Module.finrank K W)
    (S : V →ₗ[K] W) : Function.Injective S ↔ Function.Surjective S := by
  exact LinearMap.injective_iff_surjective_of_finrank_eq_finrank hVW

/-- Exercise B.49, expressed without choosing either norm as a global type-class instance.
Two quantitatively equivalent norm functions define exactly the same open subsets. -/
theorem equivalent_norms_same_open_sets {V : Type*} [AddCommGroup V]
    (n₁ n₂ : V → ℝ) (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (h : ∀ v, c * n₁ v ≤ n₂ v ∧ n₂ v ≤ C * n₁ v) (U : Set V) :
    (∀ x ∈ U, ∃ r > 0, ∀ y, n₁ (y - x) < r → y ∈ U) ↔
      (∀ x ∈ U, ∃ r > 0, ∀ y, n₂ (y - x) < r → y ∈ U) := by
  constructor
  · intro hU x hx
    obtain ⟨r, hr, hball⟩ := hU x hx
    refine ⟨c * r, mul_pos hc hr, ?_⟩
    intro y hy
    apply hball y
    have hcompare := (h (y - x)).1
    nlinarith
  · intro hU x hx
    obtain ⟨r, hr, hball⟩ := hU x hx
    refine ⟨r / C, div_pos hr hC, ?_⟩
    intro y hy
    apply hball y
    have hcompare := (h (y - x)).2
    have hmul : C * n₁ (y - x) < r := by
      rw [mul_comm]
      exact (lt_div_iff₀ hC).mp hy
    exact hcompare.trans_lt hmul

end IntroSmoothManifoldsBReviewofLinearAlgebra
