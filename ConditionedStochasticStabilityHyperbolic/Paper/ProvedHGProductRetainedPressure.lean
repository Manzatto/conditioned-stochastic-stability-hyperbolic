module

public import ConditionedStochasticStabilityHyperbolic.Paper.AuxiliaryAnosov
public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductHG
public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductSplitting
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedBasicProductPressure

/-! Actual pressure preservation under auxiliary Anosov stabilization is
proved on every retained basic set. Positivity is used only there; no
absorbed-core logarithm or pressure assertion is introduced. -/
public noncomputable section
open Set Function Bundle
open scoped Manifold ContDiff Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper
open LeanShared HyperbolicBasicSet RegularNoise
variable {E F X Y κ : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [CompactSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [MetricSpace Y] [CompactSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [RiemannianBundle (fun y : Y => TangentSpace (𝓘(ℝ, F)) y)]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [Fintype κ]
local instance provedHGProductRetainedOrdinaryCharts : ChartedSpace (E × F) (X × Y) := productCharts
local instance provedHGProductRetainedOrdinaryManifold : IsManifold (𝓘(ℝ, E × F)) ∞ (X × Y) := productManifold
local instance provedHGProductRetainedHilbertCharts : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance provedHGProductRetainedHilbertManifold : IsManifold (𝓘(ℝ, WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)]
  [IsContinuousRiemannianBundle E (TangentSpace (𝓘(ℝ,E)) : X → Type _)]
  [IsContinuousRiemannianBundle F (TangentSpace (𝓘(ℝ,F)) : Y → Type _)]
  [IsContinuousRiemannianBundle (WithLp 2 (E × F))
    (TangentSpace (𝓘(ℝ,WithLp 2 (E × F))) : X × Y → Type _)]
  {T : X ≃ₜ X} (D : SpectralDecomposition (E := E) T) {g : X → ℝ} {A : Set X}
  (h : HG1 D g A) (a : AuxiliaryAnosov (F := F) (Y := Y) (ι := κ) h.r)


omit [BorelSpace X] [BorelSpace Y] in
theorem HG1.retained_product_pressure
    (geometry : ProductDecompositionSources (E := E) (F := F) (S := a.map) D)
    (splitting : ∀ i, ProductSplittingIdentification (D.basic i).hyperbolic
      a.hl.basic.hyperbolic (geometry.tangent i))
    (map_calculus : HilbertMapProductRegularity (E := E) (F := F) (X := X) (Y := Y) h.r)
    (i : Fin D.count) (live : D.core i ⊆ Aᶜ) :
    (geometry.decomposition D a.hl.basic).pressure (fun z : X × Y => g z.1) i = D.pressure g i := by
  have hn : (1 : ℕ) ≤ ⌊h.r⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using h.regularity_gt_one.le)
  have hy : (1 : ℕ) ≤ ⌊a.hl.r⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using a.hl.regularity_gt_one.le)
  have forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T :=
    h.map_regular.differentiable.of_le (by exact_mod_cast hn)
  have inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm :=
    h.inverse_regular.differentiable.of_le (by exact_mod_cast hn)
  have auxForward : ContMDiff (𝓘(ℝ,F)) (𝓘(ℝ,F)) 1 a.map :=
    a.hl.map_regular.differentiable.of_le (by exact_mod_cast hy)
  have auxInverse : ContMDiff (𝓘(ℝ,F)) (𝓘(ℝ,F)) 1 a.map.symm :=
    a.hl.inverse_regular.differentiable.of_le (by exact_mod_cast hy)
  have productForward : ContMDiff (𝓘(ℝ,WithLp 2 (E × F))) (𝓘(ℝ,WithLp 2 (E × F))) 1 (T.prodCongr a.map) :=
    (map_calculus T a.map h.map_regular (by simpa only [a.regularity] using a.hl.map_regular)).differentiable.of_le
      (by exact_mod_cast hn)
  have productInverse : ContMDiff (𝓘(ℝ,WithLp 2 (E × F))) (𝓘(ℝ,WithLp 2 (E × F))) 1 (T.prodCongr a.map).symm :=
    (map_calculus T.symm a.map.symm h.inverse_regular
      (by simpa only [a.regularity] using a.hl.inverse_regular)).differentiable.of_le (by exact_mod_cast hn)
  have made := BasicData.product_pressure_actual_potential (D.basic i) a.hl.basic
    forward inverse auxForward auxInverse h.weight_regular.differentiable.continuous.continuousOn
    continuousOn_const (h.weight_positive i live) (fun _ _ => zero_lt_one)
    (geometry.tangent i) (splitting i) (productForward.mdifferentiable (by norm_num))
    (productInverse.mdifferentiable (by norm_num))
  have weightSame : (fun z : X × Y => g z.1*(1 : ℝ))=(fun z => g z.1) := by funext z; exact mul_one _
  rw [weightSame,a.pressure_identity,add_zero] at made
  exact made

end ConditionedStochasticStabilityHyperbolic.Paper
