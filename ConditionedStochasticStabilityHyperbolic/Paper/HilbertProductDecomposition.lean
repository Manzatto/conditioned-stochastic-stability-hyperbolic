module

public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductHL
public import ConditionedStochasticStabilityHyperbolic.Paper.ProductGlobalGeometry

/-! The same-index basic decomposition after stabilization by a full
auxiliary manifold. Actual product tangent hyperbolicity, Birkhoff dense
orbits and the nonwandering-set product identity are ordinary deterministic
sources; disjointness, covering, isolation and the graph are constructed. -/
@[expose] public noncomputable section
open Set Function Bundle
open scoped Manifold ContDiff Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper
open LeanShared HyperbolicBasicSet RegularNoise
variable {E F X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [MetricSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [RiemannianBundle (fun y : Y => TangentSpace (𝓘(ℝ, F)) y)]
local instance hilbertProductDecompositionLocal1 : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance hilbertProductDecompositionLocal2 : IsManifold (𝓘(ℝ, WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)]
  {T : X ≃ₜ X} {S : Y ≃ₜ Y} (D : SpectralDecomposition (E := E) T)
  (auxiliary : BasicData (E := F) S univ univ)

/-- Precisely deterministic product geometry, without a supplied decomposition
or any graph, order, pressure or stochastic conclusion. -/
structure ProductDecompositionSources where
  tangent : ∀ i, HyperbolicData (E := WithLp 2 (E × F)) (T.prodCongr S) (D.core i ×ˢ univ)
  denseOrbit : ∀ i, ∃ z ∈ D.core i ×ˢ (univ : Set Y),
    D.core i ×ˢ (univ : Set Y) ⊆ closure (range (orbit (T.prodCongr S) z))
  nonwandering : nonwanderingSet (T.prodCongr S) = nonwanderingSet T ×ˢ (univ : Set Y)

namespace ProductDecompositionSources
variable (p : ProductDecompositionSources (E := E) (F := F) (S := S) D)

/-- No extra or duplicate auxiliary basic index is introduced. -/
def decomposition : SpectralDecomposition (E := WithLp 2 (E × F)) (T.prodCongr S) where
  count := D.count
  core i := D.core i ×ˢ univ
  collar i := D.collar i ×ˢ univ
  basic i := {
    hyperbolic := p.tangent i
    nonempty := (D.basic i).nonempty.prod auxiliary.nonempty
    open_neighborhood := (D.basic i).open_neighborhood.prod isOpen_univ
    subset_neighborhood := prod_mono (D.basic i).subset_neighborhood (Subset.refl _)
    isolated := by
      rw [closure_prod_eq, isolatedCore_product, ← (D.basic i).isolated,
        ← auxiliary.isolated]
    dense_orbit := p.denseOrbit i }
  disjoint := by
    intro i j hij
    apply disjoint_left.mpr
    intro z hz hw
    exact disjoint_left.mp (D.disjoint hij) hz.1 hw.1
  covering := by
    rw [p.nonwandering]
    ext z
    simp only [mem_iUnion, mem_prod, mem_univ, and_true]
    rw [← D.covering]
    simp

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
 theorem edge_iff (i j : Fin D.count) :
    (p.decomposition D auxiliary).edge i j ↔ D.edge i j := by
  have : Nonempty Y := auxiliary.nonempty.to_subtype.map Subtype.val
  exact ProductGlobalGeometry.heteroclinic_product_univ T S D.core
    (fun i => (D.basic i).nonempty) i j

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
 theorem live_iff (A : Set X) (i : Fin D.count) :
    (p.decomposition D auxiliary).core i ⊆ (A ×ˢ (univ : Set Y))ᶜ ↔ D.core i ⊆ Aᶜ := by
  have : Nonempty Y := auxiliary.nonempty.to_subtype.map Subtype.val
  exact ProductGlobalGeometry.live_product_univ _ _

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
 theorem transGen_edge_iff (i j : Fin D.count) :
    Relation.TransGen (p.decomposition D auxiliary).edge i j ↔ Relation.TransGen D.edge i j := by
  have heq : (p.decomposition D auxiliary).edge = D.edge := by
    funext i j
    exact propext (p.edge_iff D auxiliary i j)
  exact heq ▸ Iff.rfl

end ProductDecompositionSources
end ConditionedStochasticStabilityHyperbolic.Paper
