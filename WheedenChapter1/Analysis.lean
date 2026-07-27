import Mathlib
open Set Filter Topology
namespace WheedenChapter1

theorem uniformContinuous_cauchy {X Y : Type*} [UniformSpace X] [UniformSpace Y]
    {f : X → Y} (hf : UniformContinuous f) {u : ℕ → X} (hu : CauchySeq u) :
    CauchySeq (f ∘ u) := by exact hf.comp_cauchySeq hu

theorem uniformlyContinuous_bounded {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X]
    [PseudoMetricSpace Y] {f : X → Y} (hf : UniformContinuous f) :
    Bornology.IsBounded (Set.range f) := by
  simpa [Set.image_univ] using (isCompact_univ.image hf.continuous).isBounded

/-- A uniformly continuous real function maps convergent sequences to convergent sequences. -/
theorem uniformContinuous_tendsto {f : ℝ → ℝ} (hf : UniformContinuous f)
    {u : ℕ → ℝ} {a : ℝ} (hu : Tendsto u atTop (𝓝 a)) :
    Tendsto (fun n => f (u n)) atTop (𝓝 (f a)) := by
  exact (hf.continuous.tendsto a).comp hu

end WheedenChapter1
