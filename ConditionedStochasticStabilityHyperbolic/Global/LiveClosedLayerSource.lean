module

public import ConditionedStochasticStabilityHyperbolic.Global.NestedLeadingData
public import ConditionedStochasticStabilityHyperbolic.Global.EqualStratumLeadingData

/-! # Closed ambient analytic layers realize the actual live-space layer

Closure is taken in the actual live subtype. The proved closure identity and
nested-kernel identification transport the produced ambient closed-local
spectral data to that literal live-space closed layer without assuming a new
gap or changing the fixed absorbing set.
-/
@[expose] public noncomputable section
open MeasureTheory Set Topology
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.LiveClosedLayerSource
open ComplexStrongFeller RestrictedLayerChain NestedLayerKernel NestedLeadingData EqualStratumLeadingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
/-- Relative closed-layer closure is the preimage of its ambient closure. -/
theorem closure_live_stratum (U V : Set X) (hUV : U ⊆ V) :
    closure (innerLevel U V) = innerLevel (closure U) V := by
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have himage : (Subtype.val : V → X) '' innerLevel U V = U := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hUV hx⟩, hx, rfl⟩
  rw [himage]
  rfl

variable (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (U V : Set X) (hU : MeasurableSet U) (hV : MeasurableSet V)
  (hKV : closure U ⊆ V)
  (d : RankOneSpectralData (transferOperator (𝕜 := ℝ)
    (chain C (closure U) isClosed_closure.measurableSet)
    (strongFeller C hSF (closure U) isClosed_closure.measurableSet))
    (1 : (closure U : Set X) →ᵇ ℝ))

def liveClosedData : RankOneSpectralData (transferOperator (𝕜 := ℝ)
    (chain (chain C V hV) (closure (innerLevel U V)) isClosed_closure.measurableSet)
    (strongFeller (chain C V hV) (strongFeller C hSF V hV)
      (closure (innerLevel U V)) isClosed_closure.measurableSet))
    (1 : (closure (innerLevel U V)) →ᵇ ℝ) :=
  setData (chain C V hV) (strongFeller C hSF V hV)
    (innerLevel (closure U) V) (closure (innerLevel U V))
    (isClosed_closure.measurableSet.preimage measurable_subtype_coe) isClosed_closure.measurableSet
    (closure_live_stratum U V (subset_closure.trans hKV)).symm
    (nestedData (closure U) V hKV C hSF isClosed_closure.measurableSet hV d)

theorem liveClosedData_rate : (liveClosedData C hSF U V hV hKV d).rate = d.rate := by
  unfold liveClosedData
  exact (setData_rate (chain C V hV) (strongFeller C hSF V hV)
    (innerLevel (closure U) V) (closure (innerLevel U V))
    (isClosed_closure.measurableSet.preimage measurable_subtype_coe) isClosed_closure.measurableSet
    (closure_live_stratum U V (subset_closure.trans hKV)).symm
    (nestedData (closure U) V hKV C hSF isClosed_closure.measurableSet hV d)).trans
      (nestedData_rate (closure U) V hKV C hSF isClosed_closure.measurableSet hV d)

end ConditionedStochasticStabilityHyperbolic.Global.LiveClosedLayerSource
