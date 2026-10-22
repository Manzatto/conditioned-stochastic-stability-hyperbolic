module

public import LeanShared.Geometry.SupportedCorePhysicalRealization
public import ConditionedStochasticStabilityHyperbolic.Spectral.RegularCoreApproximation

/-! The shared analytic/physical realization is constructed from the literal
supported smooth manifold core. The physical map is extended using the ordinary
uniform estimate; its pointwise and exit-killing laws follow from density. -/

@[expose] public noncomputable section
open Set
open scoped Manifold ContDiff BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.ManifoldRegularCoreRealization
open LeanShared.SmoothSupportedManifoldCore

variable {E M Reg H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg] [CompleteSpace Reg]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  (V K : Set M) [CompactSpace K]
  (q : core (E := E) V →ₗ[ℂ] Reg) (dense : DenseRange q)
  (C : ℝ) (hbound : ∀ c, ‖physicalCore V K c‖ ≤ C * ‖q c‖)
  (realize : Reg →L[ℂ] H)

/-- Both maps have the same actual little-regular domain, built from supported
smooth functions. No simultaneous approximation is postulated. -/
def realization : RegularCoreApproximation.Realization
    (Reg := Reg) (A := H) (Core := core (E := E) V) (X := K) where
  smooth := q
  dense := dense
  analytic := realize
  physical := physicalRealization V K q

include dense hbound in
omit [CompleteSpace Reg] in
theorem physical_smooth (c : core (E := E) V) (x : K) :
    (realization V K q dense realize).physical
      ((realization V K q dense realize).smooth c) x = functions V c x.val := by
  exact congrArg (fun f : K →ᵇ ℂ => f x) (physicalRealization_core V K q dense C hbound c)

variable (evaluate : M → Reg →L[ℂ] ℂ)
  (hevaluate : ∀ x c, evaluate x (q c) = functions V c x)

include dense hbound hevaluate in
omit [CompleteSpace Reg] in
theorem physical_value (v : Reg) (x : K) :
    (realization V K q dense realize).physical v x = evaluate x.val v :=
  physicalRealization_value V K q dense C hbound evaluate hevaluate v x

include dense hevaluate in
omit [CompleteSpace Reg] [CompactSpace K] in
theorem zero_outside (hVK : V ⊆ K) (v : Reg) (x : M) (hx : x ∉ K) :
    evaluate x v = 0 :=
  evaluate_zero_outside_live V K q dense evaluate hevaluate hVK v x hx

end ConditionedStochasticStabilityHyperbolic.ManifoldRegularCoreRealization
