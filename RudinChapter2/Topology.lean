import Mathlib

open Set Filter Topology
open scoped Topology

namespace RudinChapter2

variable {α : Type*} [TopologicalSpace α]

/-- The derived set is closed in a metric space. -/
theorem derivedSet_closed {X : Type*} [PseudoMetricSpace X] [T1Space X] (s : Set X) :
    IsClosed (derivedSet s) := by
  exact isClosed_derivedSet (X := X) s

/-- A set and its closure have the same accumulation points. -/
theorem derivedSet_of_closure {X : Type*} [PseudoMetricSpace X] [T1Space X] (s : Set X) :
    derivedSet (closure s) = derivedSet s := by
  exact derivedSet_closure (X := X) s

/-- The interior of a set is open. -/
theorem interior_isOpen (s : Set α) : IsOpen (interior s) := by
  exact isOpen_interior

/-- A set is open exactly when it equals its interior. -/
theorem open_iff_interior_eq (s : Set α) : IsOpen s ↔ interior s = s := by
  exact interior_eq_iff_isOpen.symm

/-- The interior is the largest open subset. -/
theorem open_subset_interior {g s : Set α} (hg : IsOpen g) (hgs : g ⊆ s) :
    g ⊆ interior s := by
  exact interior_maximal hgs hg

/-- Complementing the interior gives the closure of the complement. -/
theorem compl_interior_eq_closure_compl (s : Set α) :
    (interior s)ᶜ = closure (sᶜ) := by
  exact (closure_compl (s := s)).symm

/-- The closure of a connected set is connected. -/
theorem connected_closure {s : Set α} (hs : IsConnected s) : IsConnected (closure s) := by
  exact hs.closure

end RudinChapter2
