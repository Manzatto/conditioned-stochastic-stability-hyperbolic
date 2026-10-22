module
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedProductDecomposition
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualAnosovGlobalStabilization
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedHyperbolicEquilibrium
public import LeanShared.Geometry.FractionalLinearRechartRegularity

/-! Global auxiliary product geometry and deterministic equilibrium are
constructed from the original HG data. Only the ordinary fractional
product calculus contracts remain explicit. -/
public noncomputable section
open Set Function Bundle
open scoped Manifold ContDiff Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.ActualAnosovGlobalStabilization
open LeanShared HyperbolicBasicSet RegularNoise
variable {E F X Y ι κ : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [CompactSpace X] [SecondCountableTopology X] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [MetricSpace Y] [CompactSpace Y] [SecondCountableTopology Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [RiemannianBundle (fun y : Y => TangentSpace (𝓘(ℝ, F)) y)]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [Fintype ι] [Fintype κ]
local instance provedAnosovGlobalOrdinaryCharts : ChartedSpace (E × F) (X × Y) := productCharts
local instance provedAnosovGlobalOrdinaryManifold : IsManifold (𝓘(ℝ, E × F)) ∞ (X × Y) := productManifold
local instance provedAnosovGlobalHilbertCharts : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance provedAnosovGlobalHilbertManifold : IsManifold (𝓘(ℝ, WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)]
  {T : X ≃ₜ X} (D : SpectralDecomposition (E := E) T) {g : X → ℝ} {A : Set X}
  (h : HG1 D g A) (a : AuxiliaryAnosov (F := F) (Y := Y) (ι := κ) h.r)


variable
  [IsContinuousRiemannianBundle E (fun x:X=>TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle F (fun y:Y=>TangentSpace (𝓘(ℝ,F)) y)]
  [IsContinuousRiemannianBundle (WithLp 2 (E×F))
    (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)]

/-- Actual global product data, with tangent dynamics, dense core orbits,
nonwandering equality, periodic density and equilibrium all proved. -/
@[expose] def provedData
    (productCalculus:FractionalProductCalculus (E:=E) (F:=F) (X:=X) (Y:=Y) h.r)
    (weightCalculus:HilbertFirstProjectionRegularity (E:=E) (F:=F) (X:=X) (Y:=Y) (h.r-1)) :
    Data D h a := by
  let mapCalculus : HilbertMapProductRegularity (E:=E) (F:=F) (X:=X) (Y:=Y) h.r :=
    fun f k hf hk => (productCalculus.regular f k hf hk).linearRechart
      (LinearRechartedManifold.hilbertProductEquiv (A:=E) (B:=F))
  let forwardT := h.map_regular.mdifferentiable h.regularity_gt_one.le
  let inverseT := h.inverse_regular.mdifferentiable h.regularity_gt_one.le
  let forwardS := a.hl.map_regular.mdifferentiable a.hl.regularity_gt_one.le
  let inverseS := a.hl.inverse_regular.mdifferentiable a.hl.regularity_gt_one.le
  let geometry := ProductDecompositionSources.proved D a.hl.basic h.axiomA
    forwardT inverseT forwardS inverseS a.periodic_dense a.hl.mixing
  have regularS : FractionalManifoldRegularity.Regular (E:=F) (F:=F) h.r a.map := by
    simpa only [a.regularity] using a.hl.map_regular
  have regularInverseS : FractionalManifoldRegularity.Regular (E:=F) (F:=F) h.r a.map.symm := by
    simpa only [a.regularity] using a.hl.inverse_regular
  refine {
    geometry := geometry
    map_calculus := mapCalculus
    weight_calculus := weightCalculus
    nonwandering_tangent := AxiomAData.proved_product_hyperbolic a.hl.basic h.axiomA
      forwardT inverseT forwardS inverseS a.periodic_dense
    periodic_dense := ProductNonwandering.periodic_dense_product T a.map
      h.axiomA.periodic_dense a.periodic_dense
    equilibrium := ?_ }
  apply Classical.choice
  apply ((geometry.decomposition D a.hl.basic).basic h.dominant).exists_proved_equilibriumPackage
    h.regularity_gt_one (by linarith [h.regularity_gt_one])
    (mapCalculus T a.map h.map_regular regularS)
    (mapCalculus T.symm a.map.symm h.inverse_regular regularInverseS)
    (h.dominant_mixing.product a.hl.mixing) (fun z:X×Y=>g z.1)
    (weightCalculus g h.weight_regular)
  intro z hz
  exact h.weight_positive h.dominant h.dominant_live z.1 hz.1

end ConditionedStochasticStabilityHyperbolic.Paper.ActualAnosovGlobalStabilization
