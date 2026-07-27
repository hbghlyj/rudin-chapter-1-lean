import Mathlib
open Set Filter Topology
namespace RudinChapter4

/-- Continuous maps send closures into closures of images. -/
theorem image_closure_subset {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) (s : Set X) : f '' closure s ⊆ closure (f '' s) := by
  exact image_closure_subset_closure_image hf

/-- Composition preserves continuity. -/
theorem continuous_comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {f : X → Y} {g : Y → Z} (hg : Continuous g) (hf : Continuous f) :
    Continuous (g ∘ f) := by exact hg.comp hf

/-- The reciprocal function is continuous away from zero. -/
theorem continuous_reciprocal : ContinuousOn (fun x : ℝ => x⁻¹) ({0}ᶜ) := by
  exact continuousOn_inv₀

end RudinChapter4
