import Mathlib

/-! Exercise 10.1: the local linear-algebra step showing a vector-bundle projection is a
submersion. -/

namespace IntroSmoothManifoldsChapter10

/-- Exercise 10.1's differential argument: composing a linear equivalence with the surjective
projection from a product gives a surjective linear map. -/
theorem projection_comp_linearEquiv_surjective {R E B F : Type*} [Semiring R]
    [AddCommMonoid E] [Module R E] [AddCommMonoid B] [Module R B]
    [AddCommMonoid F] [Module R F] (e : E ≃ₗ[R] B × F) :
    Function.Surjective ((LinearMap.fst R B F).comp e.toLinearMap) := by
  intro b
  exact ⟨e.symm (b, 0), by simp⟩

end IntroSmoothManifoldsChapter10
