module

public import ConditionedStochasticStabilityHyperbolic.Paper.HLCanonicalPhysicalApplication

/-! Ordinary sources for one literal local application. The analytic pair,
compact inclusions, perturbed spectral gap and probability family are not
fields. The canonical application constructs them. The auxiliary and its
stabilizing product can therefore be instantiated independently. -/
public noncomputable section
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper
open LeanShared
universe uX

structure CanonicalLocalSources
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
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ : Set M}
  (h : HL (E := E) T g Λ V)
  {ι Order : Type*} [Fintype ι] [Fintype Order]
  (K : Set M) [CompactSpace K] (hK : IsCompact K)
  (hΛ : isolatedCore T K = Λ) (hΛK : Λ ⊆ K)
  (w : K → ℝ) (φ : M → ℝ)
  (σ : Measure M) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure] where
  order : ℝ
  smoothHolder : ∀ c : SmoothSupportedManifoldCore.core (E := E) (univ : Set M),
    ∃ C : ℝ, ∀ x y, ‖c.val x - c.val y‖ ≤ C * dist x y ^ order
  model : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex)
    (Reg := SmoothHolderTestSpaces.space order smoothHolder V)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ
  classical : HLBTBoundedSelectedSources.Data h
    (SmoothHolderTestSpaces.view order smoothHolder V) model (ι := ι) (Order := Order)
  physical : HLCanonicalPhysicalApplication.Inputs h order smoothHolder model classical
    K hK hΛ hΛK w φ σ

end ConditionedStochasticStabilityHyperbolic.Paper
