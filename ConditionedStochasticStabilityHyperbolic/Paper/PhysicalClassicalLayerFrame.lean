module

public import ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalLayerEigen
public import ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalLayerScale
public import ConditionedStochasticStabilityHyperbolic.Spectral.RadiusNontrivial

/-! Heterogeneous ordinary source frames for the finite global construction.
A frame contains actual chart/leaf geometry and ordinary primitive sources;
its analytic spaces and operators are constructed. In particular leaf and
parameter dimensions can differ between strata. Matching these ordinary
sources to literal tangent differentials and Bowen pressure remains an
explicit geometric source gate, rather than a claimed consequence of HG. -/
public noncomputable section
open Set MeasureTheory IsManifold
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalLayer
open LeanShared
/-- The ordinary radius is evaluated through the generic operator-ring
structure, before specializing the concrete finite chart carrier. -/
@[expose] def operatorRadius {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (P : H →L[ℂ] H) : ENNReal := spectralRadius ℂ P

universe uM uE uU uAtlas uLocal uLeaf uParameters uFiber uParams uIndex uOrder
variable {M : Type uM} {E : Type uE}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  {ι : Type*} [Fintype ι] {T : M ≃ₜ M} {r : ℝ}
  (F : RegularNoise.Maps (E := E) (ι := ι) T r)
  (σ : Measure M) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
  (K : Set M) [CompactSpace K] (hK : IsCompact K) (w : M → ℝ) (R pressure : ℝ)

structure Frame where
  U : Type uU
  [normedU : NormedAddCommGroup U]
  [spaceU : NormedSpace ℝ U]
  [finiteU : FiniteDimensional ℝ U]
  [measurableU : MeasurableSpace U]
  [borelU : BorelSpace U]
  leafMeasure : Measure U
  [haar : leafMeasure.IsAddHaarMeasure]
  Atlas : Type uAtlas
  LocalReg : Atlas → Type uLocal
  [normedLocal : ∀ i, NormedAddCommGroup (LocalReg i)]
  [spaceLocal : ∀ i, NormedSpace ℂ (LocalReg i)]
  [completeLocal : ∀ i, CompleteSpace (LocalReg i)]
  Leaf : Type uLeaf
  Parameters : Type uParameters
  [metricParameters : MetricSpace Parameters]
  Fiber : M → Type uFiber
  [normedFiber : ∀ x, NormedAddCommGroup (Fiber x)]
  [innerFiber : ∀ x, InnerProductSpace ℝ (Fiber x)]
  [finiteFiber : ∀ x, FiniteDimensional ℝ (Fiber x)]
  Auxiliary : Type uParams
  CoverIndex : ℕ → Type uIndex
  Order : Type uOrder
  [finiteOrder : Fintype Order]
  exponent : ℝ
  holder : ∀ c : SmoothSupportedManifoldCore.core (E := E) (univ : Set M), ∃ C : ℝ,
    ∀ x y, ‖c.val x - c.val y‖ ≤ C * dist x y ^ exponent
  V : Set M
  S : Set M
  G : Set M
  B : Set M
  model : PhysicalManifoldModel.Data (E := E) (U := U) (M := M)
    (AtlasIndex := Atlas) (Reg := PhysicalHolderClassicalSources.Regular exponent holder V)
    (LocalReg := LocalReg) (A := Leaf) (Ω := Parameters) V S leafMeasure
  representation : RegularNoise.Representation F Parameters model.maps
  cutoff : K → ℝ
  source : Data exponent holder model K σ F representation
    (Fiber := Fiber) (Params := Auxiliary) (I := CoverIndex) (Order := Order)
    G B hK (fun x : K => w x.val) cutoff R
  principal_below_pressure : source.primitive.pressure.ρ < Real.exp pressure

attribute [instance] Frame.normedU Frame.spaceU Frame.finiteU Frame.measurableU Frame.borelU
  Frame.haar Frame.normedLocal Frame.spaceLocal Frame.completeLocal Frame.metricParameters
  Frame.normedFiber Frame.innerFiber Frame.finiteFiber Frame.finiteOrder

end ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalLayer
