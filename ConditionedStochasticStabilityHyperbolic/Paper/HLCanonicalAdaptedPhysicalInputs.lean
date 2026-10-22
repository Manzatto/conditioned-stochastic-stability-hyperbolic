module
public import ConditionedStochasticStabilityHyperbolic.Paper.HLAdaptedPhysicalInputs
import all ConditionedStochasticStabilityHyperbolic.Paper.HLAdaptedPhysicalInputs
public import ConditionedStochasticStabilityHyperbolic.Paper.HLCanonicalPhysicalFamily
import all ConditionedStochasticStabilityHyperbolic.Paper.HLCanonicalPhysicalFamily
import all ConditionedStochasticStabilityHyperbolic.Paper.HLCanonicalPhysicalApplication
public import ConditionedStochasticStabilityHyperbolic.Paper.HLSelectedPhysicalInputs
public import ConditionedStochasticStabilityHyperbolic.Paper.HLBTBoundedSelectedSources
public import ConditionedStochasticStabilityHyperbolic.Paper.HLBoundedSelectedAnalyticPair
import all ConditionedStochasticStabilityHyperbolic.Paper.HLBoundedSelectedAnalyticPair

/-! The actual pair and its exact third carrier are constructed from ordinary
BT sources. The input below contains only the ordinary physical facts. -/
public noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 20000
open Set IsManifold MeasureTheory Filter Bundle
open scoped Manifold ContDiff BoundedContinuousFunction Topology NNReal ComplexConjugate
namespace ConditionedStochasticStabilityHyperbolic.Paper.HLCanonicalAdaptedPhysicalInputs
open LeanShared DyadicCompletion SmoothSupportedManifoldCore KellerLiverani1999
open PhysicalHolderClassicalSources.SourceData
universe uX

def StaticInputs
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
  {V S V0 : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  {T : M ≃ₜ M} {g g0 : M → ℝ} {Λ : Set M}
  (h : Paper.HL (E := E) T g Λ V)
  (u : ℝ)
  (holder : ∀ c : SmoothSupportedManifoldCore.core (E := E) (univ : Set M),
    ∃ C : ℝ, ∀ x y, ‖c.val x - c.val y‖ ≤ C * dist x y ^ u)
  (n : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex)
    (Reg := SmoothHolderTestSpaces.space u holder V)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
  {ι Order : Type*} [Fintype ι] [Fintype Order]
  (d : HLBTBoundedSelectedSources.Data h (SmoothHolderTestSpaces.view u holder V) n
    (ι := ι) (Order := Order))
  (hOuter : Paper.HL (E := E) T g0 Λ V0)
  (ambient : M → ℝ) [CompactSpace (closure V0)]
  (hΛK : Λ ⊆ closure V0)
  (σ : Measure M) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
    : Type _ :=
  let classical := HLBTBoundedSelectedSources.Data.classical h
    (SmoothHolderTestSpaces.view u holder V) n d
  let pair := (HLBoundedSelectedAnalyticPair.Data.produced h
    (SmoothHolderTestSpaces.view u holder V) n classical).pair
  letI := ProducedAnnealedPair.weakNormed pair
  letI := ProducedAnnealedPair.weakSemi pair
  letI := ProducedAnnealedPair.weakScalar pair
  letI := ProducedAnnealedPair.weakUniform pair
  letI := ProducedAnnealedPair.weakComplete pair
  HLAdaptedPhysicalInputs.Static
      (Carrier := (HLBoundedSelectedAnalyticPair.intermediateModel h n).StrongSpace)
      (W := ProducedAnnealedPair.weakSpace pair)
      h u holder (HLBoundedSelectedAnalyticPair.strongModel h n)
      (HLBoundedSelectedAnalyticPair.intermediateModel h n) (closure V0)
      isClosed_closure.isCompact hOuter.actual_isolated_core.symm hΛK
      d.maps d.laws d.representation (fun x => ambient x.val)
      (HLBoundedSelectedAnalyticPair.Data.scale h
        (SmoothHolderTestSpaces.view u holder V) n classical)
      (HLBoundedSelectedAnalyticPair.Data.scale_positive h
        (SmoothHolderTestSpaces.view u holder V) n classical) σ

private def of_adapted
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
  {V S V0 : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  {T : M ≃ₜ M} {g g0 : M → ℝ} {Λ : Set M}
  (h : Paper.HL (E := E) T g Λ V)
  (u : ℝ)
  (holder : ∀ c : SmoothSupportedManifoldCore.core (E := E) (univ : Set M),
    ∃ C : ℝ, ∀ x y, ‖c.val x - c.val y‖ ≤ C * dist x y ^ u)
  (n : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex)
    (Reg := SmoothHolderTestSpaces.space u holder V)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
  {ι Order : Type*} [Fintype ι] [Fintype Order]
  (d : HLBTBoundedSelectedSources.Data h (SmoothHolderTestSpaces.view u holder V) n
    (ι := ι) (Order := Order))
  (hOuter : Paper.HL (E := E) T g0 Λ V0)
  (ambient : M → ℝ) [CompactSpace (closure V0)]
  (hΛK : Λ ⊆ closure V0)
  (σ : Measure M) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]

  (setup : AdaptedLocalWeightSetup.Data hOuter ambient V)
  (φ : M → ℝ) (hφ : ∀ x ∈ Λ, g x = Real.exp (φ x))
  (s : StaticInputs h u holder n d hOuter ambient hΛK σ)
  (hVV0 : V ⊆ V0) (hw : Continuous ambient)
  (hwn : ∀ x ∈ closure V0, 0 ≤ ambient x)
  (floor : ∀ x : closure V0, ambient x.val ≤ d.normalizationFloor)
  (weight : ∀ x : closure V0, n.weight x.val = setup.liveCutoff hOuter ambient V x)
  (ordinary : RegularLayerClassicalInputs.ClassicalInputs d.representation σ V (closure V0)
    setup.collar isClosed_closure.isCompact (fun x => ambient x.val)
    (setup.liveCutoff hOuter ambient V) (HLBoundedSelectedAnalyticPair.Data.scale h (SmoothHolderTestSpaces.view u holder V) n
      (HLBTBoundedSelectedSources.Data.classical h (SmoothHolderTestSpaces.view u holder V) n d))
    (fullView u holder) (fullView_injective u holder) (fullCore u holder)) :
  HLCanonicalPhysicalApplication.Inputs h u holder n d (closure V0)
    isClosed_closure.isCompact hOuter.actual_isolated_core.symm hΛK
    (fun x => ambient x.val) φ σ := by
  let classical := HLBTBoundedSelectedSources.Data.classical h
    (SmoothHolderTestSpaces.view u holder V) n d
  let pair := (HLBoundedSelectedAnalyticPair.Data.produced h
    (SmoothHolderTestSpaces.view u holder V) n classical).pair
  letI := ProducedAnnealedPair.weakNormed pair
  letI := ProducedAnnealedPair.weakSemi pair
  letI := ProducedAnnealedPair.weakScalar pair
  letI := ProducedAnnealedPair.weakUniform pair
  letI := ProducedAnnealedPair.weakComplete pair
  have hwR (x : closure V0) := (floor x).trans
    (HLBoundedSelectedAnalyticPair.Data.scale_ge_floor h
      (SmoothHolderTestSpaces.view u holder V) n classical)
  have hwcR (x : closure V0) := (weight x).symm.trans_le
    (HLBoundedSelectedAnalyticPair.Data.weight_le_scale h
      (SmoothHolderTestSpaces.view u holder V) n classical x.val)
  let selected := HLAdaptedPhysicalInputs.of_adapted h hOuter ambient setup u holder
    (HLBoundedSelectedAnalyticPair.strongModel h n)
    (HLBoundedSelectedAnalyticPair.intermediateModel h n)
    hΛK d.maps d.laws d.representation
    (HLBoundedSelectedAnalyticPair.Data.scale h (SmoothHolderTestSpaces.view u holder V) n classical)
    (HLBoundedSelectedAnalyticPair.Data.scale_positive h (SmoothHolderTestSpaces.view u holder V) n classical)
    σ φ hφ s h.basic.open_neighborhood hVV0 hw hwn hwR hwcR weight ordinary
  exact ⟨selected, rfl⟩

end ConditionedStochasticStabilityHyperbolic.Paper.HLCanonicalAdaptedPhysicalInputs
