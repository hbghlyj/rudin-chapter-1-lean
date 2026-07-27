import Mathlib

/-! Propositions C.3 and C.4 from the review of calculus. -/

namespace IntroSmoothManifoldsCReviewofCalculus

/-- Proposition C.3, the chain rule for total (Fréchet) derivatives. -/
theorem chain_rule_total_derivative {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : E → F} {g : F → G}
    {f' : E →L[𝕜] F} {g' : F →L[𝕜] G} {a : E}
    (hf : HasFDerivAt f f' a) (hg : HasFDerivAt g g' (f a)) :
    HasFDerivAt (g ∘ f) (g'.comp f') a := by
  exact hg.comp a hf

/-- Proposition C.4's inverse-derivative formula for a continuous linear equivalence. -/
theorem derivative_inverse_continuousLinearEquiv {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (e : E ≃L[𝕜] F) (a : E) :
    HasFDerivAt (fun y => e.symm y) (e.symm : F →L[𝕜] E) (e a) := by
  exact e.symm.hasFDerivAt

end IntroSmoothManifoldsCReviewofCalculus
