import Mathlib

/-! Exercise 11.2: coordinate covectors form the dual basis. -/

namespace IntroSmoothManifoldsChapter11

open Module

variable {ι R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]

/-- Exercise 11.2. Every linear functional is the linear combination of the coordinate
covectors whose coefficients are its values on the original basis. This is the coordinate
identity underlying the assertion that the coordinate covectors form a basis of `Dual R V`. -/
theorem dual_basis_expansion [Fintype ι] (b : Basis ι R V) (ω : Dual R V) :
    ∑ i, ω (b i) • b.coord i = ω := by
  exact b.sum_dual_apply_smul_coord ω

/-- The coordinate covectors associated to a finite basis form a basis of the dual module. -/
theorem coordinate_covectors_are_basis [DecidableEq ι] [Finite ι] (b : Basis ι R V) :
    Function.Bijective b.dualBasis.repr := by
  exact b.dualBasis.repr.bijective

end IntroSmoothManifoldsChapter11
