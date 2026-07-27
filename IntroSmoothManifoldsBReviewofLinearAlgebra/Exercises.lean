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

end IntroSmoothManifoldsBReviewofLinearAlgebra
