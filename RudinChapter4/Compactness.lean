import Mathlib
open Set Filter Topology
namespace RudinChapter4

/-- A continuous function on a compact set is uniformly continuous. -/
theorem compact_uniformContinuous {X Y : Type*} [PseudoMetricSpace X] [UniformSpace Y]
    {s : Set X} (hs : IsCompact s) {f : X → Y} (hf : ContinuousOn f s) :
    UniformContinuousOn f s := by exact hs.uniformContinuousOn_of_continuous hf

/-- The continuous image of a compact set is compact. -/
theorem compact_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} (hs : IsCompact s) {f : X → Y} (hf : ContinuousOn f s) :
    IsCompact (f '' s) := by exact hs.image_of_continuousOn hf

/-- Continuous real functions attain maxima on nonempty compact sets. -/
theorem exists_max {s : Set ℝ} (hs : IsCompact s) (hne : s.Nonempty) {f : ℝ → ℝ}
    (hf : ContinuousOn f s) : ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x := by
  exact hs.exists_isMaxOn hne hf

end RudinChapter4
