module
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeRegularWeightExtension
public import LeanShared.Geometry.FractionalHilbertProjection
public import LeanShared.Geometry.FractionalScalarMultiplication
public import LeanShared.Geometry.LinearRechartedIdentity

/-! Local regularity of a weight near a compact set of `X` gives local regularity of its first
projection near the corresponding product set of `X × Y` in the Hilbert product charts: a regular
extension equal to the weight near the set is lifted by the first projection and multiplied by the
smooth product cutoff. -/

public noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.NativeProductLocalWeight
open LeanShared FractionalManifoldRegularity

variable {E F X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X] [CompactSpace X]
  [TopologicalSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y]
local instance productLocalOrdinaryCharts : ChartedSpace (E × F) (X × Y) := prodChartedSpace E X F Y
local instance productLocalHilbertCharts : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance productLocalHilbertManifold : IsManifold (𝓘(ℝ, WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold

omit [FiniteDimensional ℝ F] in
theorem product_local_weight (q : ℝ) (hq : 0 ≤ q) (Λ W : Set X) (hΛ : IsCompact Λ)
    (hW : IsOpen W) (hΛW : Λ ⊆ W) (w : X → ℝ) (hw0 : ∀ x, 0 ≤ w x)
    (smooth : ∀ ζ : X → ℝ, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ ζ → tsupport ζ ⊆ W →
      Regular (E := E) (F := ℝ) q (ζ * w)) :
    ∃ Wp : Set (X × Y), IsOpen Wp ∧ Λ ×ˢ (univ : Set Y) ⊆ Wp ∧
      ∀ ζ : X × Y → ℝ, ContMDiff (𝓘(ℝ, WithLp 2 (E × F))) (𝓘(ℝ)) ∞ ζ → tsupport ζ ⊆ Wp →
        Regular (E := WithLp 2 (E × F)) (F := ℝ) q (ζ * fun z : X × Y => w z.1) := by
  obtain ⟨O, hO, coreO, gX, hgX, -, -, agree, -⟩ :=
    NativeRegularWeightExtension.exists_regular_extension q Λ W hΛ hW hΛW w hw0 smooth
  refine ⟨O ×ˢ univ, hO.prod isOpen_univ, prod_mono coreO subset_rfl, fun ζ hζ hs => ?_⟩
  have regular := (regular_of_smooth hζ hq).mul (hgX.hilbert_fst (F := F) (Y := Y))
  convert regular using 1
  funext z
  change ζ z * w z.1 = ζ z * gX z.1
  by_cases hz : ζ z = 0
  · rw [hz, zero_mul, zero_mul]
  · rw [agree z.1 (hs (subset_tsupport ζ hz)).1]

end ConditionedStochasticStabilityHyperbolic.Paper.NativeProductLocalWeight
