module

public import LeanShared.Analysis.InvariantFiniteRegularTransfer

/-!
# Compatibility with the constructed completed analytic transfer

The invariant regular operator and the anisotropic transfer are both lifted
from the same literal weighted function. Injectivity of the regular function
representation identifies their smooth-core outputs. The proved
analytic extension identity then yields whole regular-space compatibility by
density. No completed invariant-core law is supplied.
-/

@[expose] public noncomputable section

namespace LeanShared.InvariantFiniteRegularCompatibility

open DyadicCompletion FiniteRegularTransferRealization

variable {X Ω Core V R : Type*} [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup R] [NormedSpace ℂ R]
  (q : Core →ₗ[ℂ] V) (raw : Core →ₗ[ℂ] (X → ℂ))
  (smooth : Core →ₗ[ℂ] R) (dense : DenseRange smooth)
  (view : R →ₗ[ℂ] (X → ℂ)) (hview : Function.Injective view)
  (hsmooth : ∀ c, view (smooth c) = raw c)
  (realize : R →L[ℂ] closedCore q)
  (hrealize : ∀ c, realize (smooth c) = coreLift q c)
  (F : Ω → X → X) (g : X → ℝ)
  (hregular : ∀ a f, weightedComposition (F a) g (view f) ∈ view.range)
  (hcoreRegular : ∀ a c, weightedComposition (F a) g (raw c) ∈ view.range)

include hsmooth in
/-- Both constructions represent the same actual finite-regular function. -/
theorem core_action_eq (a : Ω) (c : Core) :
    InvariantFiniteRegularTransfer.action view hview F g hregular a (smooth c) =
      regularAction raw R view hview F g hcoreRegular a c := by
  apply hview
  funext x
  rw [InvariantFiniteRegularTransfer.action_apply, regularAction_apply, hsmooth]

variable (C : ℝ)
  (hregularBound : ∀ a f,
    ‖InvariantFiniteRegularTransfer.action view hview F g hregular a f‖ ≤ C * ‖f‖)
  (L : ℝ)
  (hanalyticBound : ∀ a c,
    ‖targetCore q raw R view hview realize F g hcoreRegular a c‖ ≤ L * ‖q c‖)

include dense hsmooth hrealize hanalyticBound in
/-- The literal completed anisotropic operator constructed from the
finite-regular core intertwines the constructed invariant regular action. -/
theorem analytic_intertwining (a : Ω) :
    realize.comp (InvariantFiniteRegularTransfer.operator view hview F g hregular C hregularBound a) =
      (operator q raw R view hview realize F g hcoreRegular a).comp realize := by
  apply InvariantFiniteRegularTransfer.intertwining view hview F g hregular C hregularBound
    smooth dense realize (operator q raw R view hview realize F g hcoreRegular)
  intro b c
  rw [core_action_eq raw smooth view hview hsmooth F g hregular hcoreRegular,
    hrealize, operator_core q raw R view hview realize F g hcoreRegular L hanalyticBound]

end LeanShared.InvariantFiniteRegularCompatibility
