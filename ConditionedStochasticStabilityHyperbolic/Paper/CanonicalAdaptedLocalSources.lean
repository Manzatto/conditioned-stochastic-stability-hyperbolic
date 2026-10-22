module
public import ConditionedStochasticStabilityHyperbolic.Paper.CanonicalLocalSources
public import ConditionedStochasticStabilityHyperbolic.Paper.HLCanonicalAdaptedPhysicalInputs
import all ConditionedStochasticStabilityHyperbolic.Paper.HLCanonicalAdaptedPhysicalInputs

/-! Construct the canonical ordinary-source record from static classical facts
and the checked adapted-collar initializer. No no-return, retention, positivity
or noisy spectral conclusion is assumed in the physical packet. -/
public noncomputable section
open Set IsManifold MeasureTheory Bundle Filter
open scoped Manifold ContDiff NNReal Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.CanonicalLocalSources
open LeanShared PhysicalHolderClassicalSources.SourceData
universe uX
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
  (s : HLCanonicalAdaptedPhysicalInputs.StaticInputs h u holder n d hOuter ambient hΛK σ)
  (hVV0 : V ⊆ V0) (hw : Continuous ambient)
  (hwn : ∀ x ∈ closure V0, 0 ≤ ambient x)
  (floor : ∀ x : closure V0, ambient x.val ≤ d.normalizationFloor)
  (weight : ∀ x : closure V0, n.weight x.val = setup.liveCutoff hOuter ambient V x)
  (ordinary : RegularLayerClassicalInputs.ClassicalInputs d.representation σ V (closure V0)
    setup.collar isClosed_closure.isCompact (fun x => ambient x.val)
    (setup.liveCutoff hOuter ambient V) (HLBoundedSelectedAnalyticPair.Data.scale h (SmoothHolderTestSpaces.view u holder V) n
      (HLBTBoundedSelectedSources.Data.classical h (SmoothHolderTestSpaces.view u holder V) n d))
    (fullView u holder) (fullView_injective u holder) (fullCore u holder)) :
  CanonicalLocalSources (U := U) (AtlasIndex := AtlasIndex) (A := A) (Ω := Ω)
    (LocalReg := LocalReg) (S := S) (μ := μ) (ι := ι) (Order := Order)
    h (closure V0) isClosed_closure.isCompact hOuter.actual_isolated_core.symm hΛK
    (fun x => ambient x.val) φ σ where
  order := u
  smoothHolder := holder
  model := n
  classical := d
  physical := HLCanonicalAdaptedPhysicalInputs.of_adapted h u holder n d hOuter ambient
    hΛK σ setup φ hφ s hVV0 hw hwn floor weight ordinary

end ConditionedStochasticStabilityHyperbolic.Paper.CanonicalLocalSources
