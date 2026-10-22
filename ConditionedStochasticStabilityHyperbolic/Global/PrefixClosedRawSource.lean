module

public import ConditionedStochasticStabilityHyperbolic.Global.LiveClosedLayerMeasure
public import ConditionedStochasticStabilityHyperbolic.Spectral.CanonicalChainGap

/-! # Produced ambient raw closed-local data inside an actual selected prefix

The actual relative closure, leading data, representing measure and physical
product are constructed. This is the source adapter for an HG2 prefix; the
ambient map need not restrict to a homeomorphism of that prefix.
-/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.PrefixClosedRawSource
open ComplexStrongFeller RestrictedLayerChain NestedLayerKernel
open LiveClosedLayerSource LiveClosedLayerMeasure
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (S V : Set X) (hV : MeasurableSet V) (hKV : closure S ⊆ V)
  (R : ℝ) (hR : 0 < R)
  (d : RankOneSpectralData (R • transferOperator (𝕜 := ℝ)
    (chain C (closure S) isClosed_closure.measurableSet)
    (strongFeller C hSF (closure S) isClosed_closure.measurableSet))
    (1 : (closure S : Set X) →ᵇ ℝ))

def normalizedSource : RankOneSpectralData (transferOperator (𝕜 := ℝ)
    (chain C (closure S) isClosed_closure.measurableSet)
    (strongFeller C hSF (closure S) isClosed_closure.measurableSet))
    (1 : (closure S : Set X) →ᵇ ℝ) := d.ofRawNormalization R hR (by
  rw [smul_smul, inv_mul_cancel₀ hR.ne', one_smul])

theorem normalizedSource_rate : (normalizedSource C hSF S R hR d).rate = R⁻¹ * d.rate :=
  d.ofRawNormalization_rate R hR _

theorem normalizedSource_vector : (normalizedSource C hSF S R hR d).eigenvector = d.eigenvector :=
  d.ofRawNormalization_eigenvector R hR _

theorem normalizedSource_mean : (normalizedSource C hSF S R hR d).mean = d.mean :=
  d.ofRawNormalization_mean R hR _

def actualPrefixData : RankOneSpectralData (R • transferOperator (𝕜 := ℝ)
    (chain (chain C V hV) (closure (innerLevel S V)) isClosed_closure.measurableSet)
    (strongFeller (chain C V hV) (strongFeller C hSF V hV)
      (closure (innerLevel S V)) isClosed_closure.measurableSet))
    (1 : closure (innerLevel S V) →ᵇ ℝ) :=
  (liveClosedData C hSF S V hV hKV (normalizedSource C hSF S R hR d)).rescale R hR

theorem actualPrefixData_rate : (actualPrefixData C hSF S V hV hKV R hR d).rate = d.rate := by
  change R * (liveClosedData C hSF S V hV hKV (normalizedSource C hSF S R hR d)).rate = _
  rw [liveClosedData_rate]
  rw [normalizedSource_rate]
  rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]

variable (μ : Measure (closure S : Set X)) [IsFiniteMeasure μ]
  (hmean : ∀ f : (closure S : Set X) →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ)

omit [IsFiniteMeasure μ] in
include hmean in
theorem actualPrefixData_represents : ∀ f : closure (innerLevel S V) →ᵇ ℝ,
    (actualPrefixData C hSF S V hV hKV R hR d).mean f =
      ∫ y, f y ∂liveClosedMeasure S V hKV μ :=
  liveClosedMeasure_represents C hSF S V hV hKV (normalizedSource C hSF S R hR d) μ
    (by intro f; rw [normalizedSource_mean]; exact hmean f)

theorem actualPrefixData_vector (p : (closure S : Set X)) :
    (actualPrefixData C hSF S V hV hKV R hR d).eigenvector (liveClosedPoint S V hKV p) =
      d.eigenvector p := by
  change (liveClosedData C hSF S V hV hKV (normalizedSource C hSF S R hR d)).eigenvector _ = _
  rw [liveClosedData_vector, normalizedSource_vector]

omit [IsFiniteMeasure μ] in
theorem actualPrefixData_core_support (p : (closure S : Set X))
    (hp : p ∈ (LeanShared.eigenvectorMeasure μ d.eigenvector).support) :
    liveClosedPoint S V hKV p ∈ (LeanShared.eigenvectorMeasure (liveClosedMeasure S V hKV μ)
      (actualPrefixData C hSF S V hV hKV R hR d).eigenvector).support := by
  apply liveClosedProduct_core_support C hSF S V hV hKV (normalizedSource C hSF S R hR d) μ p
  rw [normalizedSource_vector]
  exact hp

omit [IsFiniteMeasure μ] in
theorem actualPrefixData_product_map :
    (LeanShared.eigenvectorMeasure (liveClosedMeasure S V hKV μ)
      (actualPrefixData C hSF S V hV hKV R hR d).eigenvector).map
        (fun y : closure (innerLevel S V) => y.val.val) =
      (LeanShared.eigenvectorMeasure μ d.eigenvector).map Subtype.val := by
  have he := liveClosedProduct_map_eq_ambient C hSF S V hV hKV (normalizedSource C hSF S R hR d) μ
  rw [normalizedSource_vector] at he
  exact he

end ConditionedStochasticStabilityHyperbolic.Global.PrefixClosedRawSource
