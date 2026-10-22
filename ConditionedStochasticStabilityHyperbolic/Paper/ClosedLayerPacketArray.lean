module

public import ConditionedStochasticStabilityHyperbolic.Paper.ClosedLayerAnalyticPacket

/-! Apply the produced closed-layer packets to the actual global killed
kernel. The analytic Banach carriers may differ across strata; subordinate
mixing, rank-one projections and physical spectral-radius bounds are not inputs. -/
public noncomputable section
open Set MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.ClosedLayerAnalyticPacket
open LeanShared Global RestrictedLayerChain ComplexStrongFeller

set_option linter.defProp false in
def spectralComparisons
    {X Ω Ξ I : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (ρ : ℝ≥0 → Measure Ω) [∀ ε, IsProbabilityMeasure (ρ ε)]
    (F : I → ℝ≥0 → X × Ω → X) (hF : ∀ i ε, Measurable (F i ε))
    (Live : Set X) (hLive : MeasurableSet Live)
    (K : I → Set X) [∀ i, CompactSpace (K i)]
    (hK : ∀ i, MeasurableSet (K i)) (hKL : ∀ i, K i ⊆ Live)
    (w : X → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (scale pressure : I → ℝ) (positive : ∀ i, 0 < scale i) (bound : ∀ i x, w x ≤ scale i)
    (law : ℝ≥0 → Measure Ξ) (probability : ∀ ε, IsProbabilityMeasure (law ε))
    (packets : ∀ i, Data (K i)
      (fun ε => RestrictedNoise.chain (ρ ε) (F i ε) (hF i ε) (K i) (hK i)
        (fun x => w x.val) (hw.comp measurable_subtype_coe)
        (scale i) (positive i) (fun x => bound i x.val)) law probability (scale i) (pressure i))
    (C : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain X)
    (actual : ∀ i, ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      C ε = NoiseKernel.chain (ρ ε) (F i ε) (hF i ε) Live hLive w hw R hR hwR) := by
  letI : ∀ i, NormedAddCommGroup (packets i).Strong := fun i => (packets i).strongNormed
  letI : ∀ i, NormedSpace ℂ (packets i).Strong := fun i => (packets i).strongScalar
  letI : ∀ i, CompleteSpace (packets i).Strong := fun i => (packets i).strongComplete
  exact PhysicalClassicalGlobalApplication.eventual_layer_spectrum_with_individual_scales
    (fun i => (packets i).Strong)
    (fun i ε => (scale i : ℂ) • (packets i).model.inputs.operator ε)
    (fun i => (packets i).model.inputs.principal)
    ρ F hF Live hLive K hK hKL w hw R hR hwR scale positive bound C actual
    (fun i => (packets i).eigenvectors)

end ConditionedStochasticStabilityHyperbolic.Paper.ClosedLayerAnalyticPacket
