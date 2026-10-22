module

public import ConditionedStochasticStabilityHyperbolic.Spectral.HomeomorphicGapTransport
public import ConditionedStochasticStabilityHyperbolic.Spectral.PositiveEigenmeasure
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! The Riesz construction commutes with actual compact state-coordinate
changes. This identifies the transported probability product, not just its
operator eigenrelations. -/

@[expose] public noncomputable section
open MeasureTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.HomeomorphicGapTransport
open LeanShared

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [CompactSpace X] [CompactSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
  [BorelSpace X] [BorelSpace Y]
  (e : X ≃ₜ Y)
  (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)) (Q : (Y →ᵇ ℝ) →L[ℝ] (Y →ᵇ ℝ))
  (d : RankOneSpectralData Q (1 : Y →ᵇ ℝ))
  (h : Q.comp (pull ⟨e.symm, e.symm.continuous⟩) =
    (pull ⟨e.symm, e.symm.continuous⟩).comp P)
  (posP : ∀ f : X →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ P f x)
  (posQ : ∀ f : Y →ᵇ ℝ, (∀ y, 0 ≤ f y) → ∀ y, 0 ≤ Q f y)

/-- No separately chosen compatible eigenmeasure is required. -/
theorem transport_eigenmeasure :
    (transport e P Q d h).eigenmeasure posP = (d.eigenmeasure posQ).map e.symm := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [← (transport e P Q d h).eigenmeasure_represents posP]
  exact transport_mean_represents e P Q d h (d.eigenmeasure posQ)
    (d.eigenmeasure_represents posQ) f

/-- Both constructed eigenproducts correspond under the literal state map. -/
theorem transport_eigenproduct :
    eigenvectorMeasure ((transport e P Q d h).eigenmeasure posP)
      (transport e P Q d h).eigenvector =
    (eigenvectorMeasure (d.eigenmeasure posQ) d.eigenvector).map e.symm := by
  rw [transport_eigenmeasure e P Q d h posP posQ]
  exact transport_product e P Q d h _

end ConditionedStochasticStabilityHyperbolic.HomeomorphicGapTransport
