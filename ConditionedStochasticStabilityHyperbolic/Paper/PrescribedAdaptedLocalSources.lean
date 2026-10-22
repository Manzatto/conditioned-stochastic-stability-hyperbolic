module
public import ConditionedStochasticStabilityHyperbolic.Paper.HLBTPrescribedNoiseSources
public import ConditionedStochasticStabilityHyperbolic.Paper.CanonicalAdaptedLocalSources
import all ConditionedStochasticStabilityHyperbolic.Paper.CanonicalAdaptedLocalSources
public import ConditionedStochasticStabilityHyperbolic.Paper.AdaptedLocalWeightSupportedProduct
public import ConditionedStochasticStabilityHyperbolic.Paper.CanonicalLocalSourceParameters

/-! Ordinary sources with the actual perturbations and law prescribed. The
cutoff setup is a parameter produced by the checked supported-product
constructor; its geometric conclusions are not repeated as source fields. -/
public noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 20000
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff NNReal Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.PrescribedAdaptedLocalSources
open LeanShared RegularNoise PhysicalHolderClassicalSources.SourceData
universe uX

structure Data
  {M : Type uX} {E U AtlasIndex A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)] [MetricSpace Ω]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  {V V0 S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  {T : M ≃ₜ M} {g g0 : M → ℝ} {Λ : Set M}
  (h : HL (E := E) T g Λ V) (outer : HL (E := E) T g0 Λ V0) (ambient : M → ℝ)
  (setup : AdaptedLocalWeightSetup.Data outer ambient V)
  {ι Order : Type*} [Fintype ι] [Fintype Order]
  (P : Maps (E := E) (ι := ι) T h.r) (L : Laws (ι := ι))
  [CompactSpace (closure V0)] (hΛK : Λ ⊆ closure V0)
  (σ : Measure M) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure] where
  order : ℝ
  smoothHolder : ∀ c : SmoothSupportedManifoldCore.core (E := E) (univ : Set M),
    ∃ C : ℝ, ∀ x y, ‖c.val x - c.val y‖ ≤ C * dist x y ^ order
  model : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex)
    (Reg := SmoothHolderTestSpaces.space order smoothHolder V)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ
  bt : HLBTPrescribedNoiseSources.Data model h
    (HLBTBoundedSelectedSources.strongModel h model)
    (HLBTBoundedSelectedSources.intermediateModel h model)
    (SmoothHolderTestSpaces.view order smoothHolder V) P L (Order := Order)
  static : Nonempty (HLCanonicalAdaptedPhysicalInputs.StaticInputs h order smoothHolder model
    (bt.ordinary model h
      (HLBTBoundedSelectedSources.strongModel h model)
      (HLBTBoundedSelectedSources.intermediateModel h model)
      (SmoothHolderTestSpaces.view order smoothHolder V))
    outer ambient hΛK σ)
  floor : ∀ x : M, ambient x ≤ bt.normalizationFloor
  weight : ∀ x : closure V0, model.weight x.val = setup.liveCutoff outer ambient V x
  classical : RegularLayerClassicalInputs.ClassicalInputs bt.representation σ V (closure V0)
    setup.collar isClosed_closure.isCompact (fun x => ambient x.val)
    (setup.liveCutoff outer ambient V)
    (HLBoundedSelectedAnalyticPair.Data.scale h
      (SmoothHolderTestSpaces.view order smoothHolder V) model
      (HLBTBoundedSelectedSources.Data.classical h
        (SmoothHolderTestSpaces.view order smoothHolder V) model
        (bt.ordinary model h
          (HLBTBoundedSelectedSources.strongModel h model)
          (HLBTBoundedSelectedSources.intermediateModel h model)
          (SmoothHolderTestSpaces.view order smoothHolder V))))
    (fullView order smoothHolder) (fullView_injective order smoothHolder)
    (fullCore order smoothHolder)

end ConditionedStochasticStabilityHyperbolic.Paper.PrescribedAdaptedLocalSources
