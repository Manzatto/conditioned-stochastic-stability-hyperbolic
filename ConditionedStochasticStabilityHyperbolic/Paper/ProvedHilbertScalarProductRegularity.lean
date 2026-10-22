module
public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductHL
public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductHG
public import LeanShared.Geometry.FractionalHilbertProjection
public import LeanShared.Geometry.FractionalScalarMultiplication

/-! Every real-order scalar product and first-projection regularity contract
used by actual auxiliary stabilization is derived from local Holder jets. -/
public noncomputable section
open Set Function
open scoped Manifold ContDiff Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper
open LeanShared
variable {E F X Y:Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ,E)) ∞ X]
  [MetricSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ,F)) ∞ Y]
local instance scalarProductCharts : ChartedSpace (WithLp 2 (E×F)) (X×Y) :=
  LinearRechartedManifold.productCharts
local instance scalarProductManifold : IsManifold (𝓘(ℝ,WithLp 2 (E×F))) ∞ (X×Y) :=
  LinearRechartedManifold.product_manifold

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold (𝓘(ℝ,E)) ∞ X] [IsManifold (𝓘(ℝ,F)) ∞ Y] in
theorem proved_hilbertFirstProjectionRegularity (q:ℝ) :
    HilbertFirstProjectionRegularity (E:=E) (F:=F) (X:=X) (Y:=Y) q :=
  fun _ hf=>hf.hilbert_fst

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem proved_hilbertScalarProductRegularity (q:ℝ) :
    HilbertScalarProductRegularity (E:=E) (F:=F) (X:=X) (Y:=Y) q :=
  fun _ _ hf hk=>hf.hilbert_fst.mul hk.hilbert_snd

end ConditionedStochasticStabilityHyperbolic.Paper
