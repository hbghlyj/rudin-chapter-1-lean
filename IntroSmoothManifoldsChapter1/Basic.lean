import Mathlib

/-! Elementary topological facts used in Chapter 1's manifold exercises. -/

namespace IntroSmoothManifoldsChapter1

open Set

/-- A homeomorphism carries intersections to intersections. -/
theorem image_inter_eq {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : α ≃ₜ β) (s t : Set α) : e '' (s ∩ t) = e '' s ∩ e '' t := by
  exact Set.image_inter e.injective

/-- A homeomorphism carries unions to unions. -/
theorem image_union_eq {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : α ≃ₜ β) (s t : Set α) : e '' (s ∪ t) = e '' s ∪ e '' t := by
  exact Set.image_union e s t

/-- Local Euclidean coordinates separate distinct points in their domain. -/
theorem chart_coordinates_ne {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : α ≃ₜ β) {x y : α} (h : x ≠ y) : e x ≠ e y := by
  exact e.injective.ne h

end IntroSmoothManifoldsChapter1
