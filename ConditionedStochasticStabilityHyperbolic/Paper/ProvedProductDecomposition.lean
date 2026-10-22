module
public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductGlobalSources
public import LeanShared.Dynamics.HyperbolicHilbertProduct
public import LeanShared.Dynamics.PeriodicDenseProductTransitivity

/-! Actual global product geometry from the original finite decomposition,
Axiom A periodic density, and a full mixing auxiliary basic set. Original
basic sets need not be mixing. -/
public noncomputable section
open Set Function Bundle
open scoped Manifold ContDiff Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper
open LeanShared HyperbolicBasicSet
variable {E F X Y:Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ,E)) ∞ X]
  [MetricSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ,F)) ∞ Y]
  [RiemannianBundle (fun x:X=>TangentSpace (𝓘(ℝ,E)) x)]
  [RiemannianBundle (fun y:Y=>TangentSpace (𝓘(ℝ,F)) y)]
  {T:X≃ₜX} {S:Y≃ₜY} (D:SpectralDecomposition (E:=E) T)

omit [FiniteDimensional ℝ E] in
/-- Finite disjoint compact cores isolate periodic approximants in their
actual core, rather than merely in the whole nonwandering set. -/
theorem SpectralDecomposition.periodic_dense_on_core
    (density:closure (periodicPts (T:X→X))=nonwanderingSet T) (i:Fin D.count) :
    D.core i ⊆ closure (D.core i∩periodicPts (T:X→X)) := by
  classical
  let others : Set X := ⋃ j : {j:Fin D.count // j≠i},D.core j.val
  have closedOthers : IsClosed others := isClosed_iUnion_of_finite fun j=>(D.basic j.val).hyperbolic.compact.isClosed
  intro x hx
  have outside : x∉others := by
    intro h
    obtain ⟨j,hj⟩ := mem_iUnion.mp h
    exact Set.disjoint_left.mp (D.disjoint (Ne.symm j.property)) hx hj
  have dense : x∈closure (periodicPts (T:X→X)) := by
    rw [density,←D.covering]
    exact mem_iUnion.mpr ⟨i,hx⟩
  apply mem_closure_iff.mpr
  intro U openU inU
  obtain ⟨p,hp,periodic⟩ := mem_closure_iff.mp dense (U∩othersᶜ)
    (openU.inter closedOthers.isOpen_compl) ⟨inU,outside⟩
  have nw := ProductNonwandering.periodic_subset T periodic
  rw [←D.covering] at nw
  obtain ⟨j,hj⟩ := mem_iUnion.mp nw
  have same : j=i := by
    by_contra different
    exact hp.2 (mem_iUnion.mpr ⟨⟨j,different⟩,hj⟩)
  exact ⟨p,hp.1,⟨same ▸ hj,periodic⟩⟩

local instance provedProductCharts : ChartedSpace (WithLp 2 (E×F)) (X×Y) :=
  LinearRechartedManifold.productCharts
local instance provedProductManifold : IsManifold (𝓘(ℝ,WithLp 2 (E×F))) ∞ (X×Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)]
  [IsContinuousRiemannianBundle E (fun x:X=>TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle F (fun y:Y=>TangentSpace (𝓘(ℝ,F)) y)]
  [IsContinuousRiemannianBundle (WithLp 2 (E×F))
    (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)]
  [SecondCountableTopology X] [SecondCountableTopology Y]
  (auxiliary:BasicData (E:=F) S univ univ) (h:AxiomAData (E:=E) T)
  (forwardT:MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
  (inverseT:MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
  (forwardS:MDifferentiable (𝓘(ℝ,F)) (𝓘(ℝ,F)) S)
  (inverseS:MDifferentiable (𝓘(ℝ,F)) (𝓘(ℝ,F)) S.symm)
  (auxiliaryPeriodic:closure (periodicPts (S:Y→Y))=univ)
  (auxiliaryMixing:MixingOn S univ)

/-- No product hyperbolicity, product dense orbit, or nonwandering identity
is supplied to this producer. -/
@[expose] def ProductDecompositionSources.proved :
    ProductDecompositionSources (E:=E) (F:=F) (S:=S) D where
  tangent i := HilbertProduct.of_factors (D.basic i).hyperbolic auxiliary.hyperbolic
    forwardT inverseT forwardS inverseS
  denseOrbit i := exists_product_dense_orbit_of_periodic_dense
    (D.basic i).hyperbolic.compact auxiliary.hyperbolic.compact
    (D.basic i).nonempty auxiliary.nonempty
    (D.basic i).hyperbolic.invariant auxiliary.hyperbolic.invariant
    (D.basic i).dense_orbit (D.periodic_dense_on_core h.periodic_dense i) auxiliaryMixing
  nonwandering := ProductNonwandering.nonwandering_product T S h.periodic_dense auxiliaryPeriodic

/-- The actual product nonwandering tangent certificate is also produced. -/
@[expose] def AxiomAData.proved_product_hyperbolic :
    HyperbolicData (E:=WithLp 2 (E×F)) (T.prodCongr S) (nonwanderingSet (T.prodCongr S)) := by
  have identity : nonwanderingSet (T.prodCongr S)=nonwanderingSet T×ˢ(univ:Set Y) :=
    ProductNonwandering.nonwandering_product T S h.periodic_dense auxiliaryPeriodic
  rw [identity]
  exact HilbertProduct.of_factors h.hyperbolic auxiliary.hyperbolic forwardT inverseT forwardS inverseS

end ConditionedStochasticStabilityHyperbolic.Paper
