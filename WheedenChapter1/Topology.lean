import Mathlib
open Set Filter Topology
namespace WheedenChapter1

theorem closed_subset_compact {X : Type*} [TopologicalSpace X] {f k : Set X}
    (hk : IsCompact k) (hf : IsClosed f) (hsub : f ⊆ k) : IsCompact f := by
  exact hk.of_isClosed_subset hf hsub

theorem euclidean_complete (n : ℕ) : CompleteSpace (EuclideanSpace ℝ (Fin n)) := by
  infer_instance

theorem arbitrary_union_open {X ι : Type*} [TopologicalSpace X] {s : ι → Set X}
    (hs : ∀ i, IsOpen (s i)) : IsOpen (⋃ i, s i) := by
  exact isOpen_iUnion hs

theorem finite_inter_closed {X : Type*} [TopologicalSpace X] {s t : Set X}
    (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s ∩ t) := by
  exact hs.inter ht

end WheedenChapter1
