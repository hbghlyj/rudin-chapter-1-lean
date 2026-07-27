import Mathlib

open Set Filter Topology
open scoped Topology

namespace RudinChapter2

/-- The classical set consisting of zero and the reciprocal sequence. -/
def reciprocalCompactSet : Set ℝ := {0} ∪ Set.range (fun n : ℕ => 1 / (n + 1 : ℝ))

theorem tendsto_reciprocal_sequence :
    Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The reciprocal set is bounded. -/
theorem reciprocalCompactSet_bounded : Bornology.IsBounded reciprocalCompactSet := by
  refine Bornology.IsBounded.subset (Metric.isBounded_Icc (0 : ℝ) 1) ?_
  rintro x (hx | ⟨n, rfl⟩)
  · subst x
    norm_num
  · constructor
    · positivity
    · have h : (1 : ℝ) ≤ n + 1 := by norm_num
      exact (div_le_iff₀' (by positivity)).mpr (by simpa using h)

/-- The reciprocal set is compact. -/
theorem reciprocalCompactSet_compact : IsCompact reciprocalCompactSet := by
  have h := tendsto_reciprocal_sequence.isCompact_insert_range
  simpa [reciprocalCompactSet] using h

/-- The reciprocal set is closed. -/
theorem reciprocalCompactSet_closed : IsClosed reciprocalCompactSet := by
  exact reciprocalCompactSet_compact.isClosed

/-- A closed subset of a compact set is compact. -/
theorem closed_subset_compact {X : Type*} [TopologicalSpace X] {s k : Set X}
    (hk : IsCompact k) (hs : IsClosed s) (hsk : s ⊆ k) : IsCompact s := by
  exact hk.of_isClosed_subset hs hsk

/-- The open interval `(0,1)` is not compact. -/
theorem open_unit_interval_not_compact : ¬ IsCompact (Set.Ioo (0 : ℝ) 1) := by
  rw [isCompact_Ioo_iff]
  norm_num

/-- Euclidean space is separable. -/
theorem euclidean_separable (n : ℕ) : TopologicalSpace.SeparableSpace (EuclideanSpace ℝ (Fin n)) := by
  infer_instance

/-- Every compact metric space is separable. -/
theorem compact_metric_separable {X : Type*} [PseudoMetricSpace X] [CompactSpace X] :
    TopologicalSpace.SeparableSpace X := by
  infer_instance

end RudinChapter2
