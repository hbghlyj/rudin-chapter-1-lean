import Mathlib

/-! Reusable elementary mathematics supporting this chapter's subject. -/

namespace IntroSmoothManifoldsChapter9

/-- Composition of the maps occurring in local constructions is associative. -/
theorem map_composition_assoc {α β γ δ : Type*} (f : α → β) (g : β → γ) (h : γ → δ) :
    (h ∘ g) ∘ f = h ∘ (g ∘ f) := by
  rfl

/-- A composite of injective maps is injective. -/
theorem injective_composition {α β γ : Type*} {f : α → β} {g : β → γ}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (g ∘ f) := by
  exact hg.comp hf

/-- Images preserve unions, a basic local-to-global identity. -/
theorem image_union {α β : Type*} (f : α → β) (s t : Set α) :
    f '' (s ∪ t) = f '' s ∪ f '' t := by
  exact Set.image_union f s t

end IntroSmoothManifoldsChapter9
