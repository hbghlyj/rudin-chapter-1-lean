import Mathlib

/-! Proposition A.16: second-countable spaces are Lindelöf. -/

namespace IntroSmoothManifoldsAReviewofTopology

open Set

/-- Proposition A.16. Every open cover of a second-countable space has a countable subcover. -/
theorem secondCountable_countable_subcover {X ι : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] (U : ι → Set X) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) :
    ∃ T : Set ι, T.Countable ∧ (⋃ i ∈ T, U i) = Set.univ := by
  obtain ⟨T, hT, hUnion⟩ := TopologicalSpace.isOpen_iUnion_countable U hopen
  exact ⟨T, hT, hUnion.trans hcover⟩

end IntroSmoothManifoldsAReviewofTopology
