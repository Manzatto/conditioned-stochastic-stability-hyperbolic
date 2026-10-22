module

public import ConditionedStochasticStabilityHyperbolic.Spectral.CoreConjugation
public import LeanShared.Analysis.FiniteRegularTransferRealization

/-! Literal real weighted composition commutes with the ordinary conjugation.
The action identity used by the completion producer is proved pointwise. -/

public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.CoreConjugation
open LeanShared.FiniteRegularTransferRealization

variable {X Ω C R : Type*} [AddCommGroup C] [Module ℂ C]
  [NormedAddCommGroup R] [NormedSpace ℂ R]

theorem regular_action_commutes
    (smooth : C →ₗ[ℂ] (X → ℂ)) (view : R →ₗ[ℂ] (X → ℂ))
    (injective : Function.Injective view) (F : Ω → X → X) (g : X → ℝ)
    (regular : ∀ a c, weightedComposition (F a) g (smooth c) ∈ view.range)
    (starCore : C → C) (J : R → R)
    (hcore : ∀ c x, smooth (starCore c) x = star (smooth c x))
    (hJ : ∀ v x, view (J v) x = star (view v x)) (a : Ω) (c : C) :
    regularAction smooth R view injective F g regular a (starCore c) =
      J (regularAction smooth R view injective F g regular a c) := by
  apply injective
  funext x
  simp only [hJ, regularAction_apply, hcore, star_mul, Complex.star_def, Complex.conj_ofReal, mul_comm]

end ConditionedStochasticStabilityHyperbolic.CoreConjugation
