module
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedHilbertProductSplitting
public import ConditionedStochasticStabilityHyperbolic.Paper.AuxiliaryAnosov
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedHGProductRetainedPressure
public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductHG
public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductSplitting
public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductRegularNoise
public import ConditionedStochasticStabilityHyperbolic.Global.ProductAdaptedFiltration

/-! Whole-system saddle stabilization with the actual independent control
cubes. The ordinary source contains only deterministic product tangent,
nonwandering and thermodynamic facts. Product HG clauses, saddle dimensions,
noise family/laws, strict trapping and every shifted filtration layer are
constructed. In particular no original basic set must have two nonzero
hyperbolic dimensions. -/
@[expose] public noncomputable section
open Set Function Bundle
open scoped Manifold ContDiff Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.ActualAnosovGlobalStabilization
open LeanShared HyperbolicBasicSet RegularNoise
variable {E F X Y ι κ : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [MetricSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [RiemannianBundle (fun y : Y => TangentSpace (𝓘(ℝ, F)) y)]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [Fintype ι] [Fintype κ]
local instance actualAnosovGlobalOrdinaryCharts : ChartedSpace (E × F) (X × Y) := productCharts
local instance actualAnosovGlobalOrdinaryManifold : IsManifold (𝓘(ℝ, E × F)) ∞ (X × Y) := productManifold
local instance actualAnosovGlobalHilbertCharts : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance actualAnosovGlobalHilbertManifold : IsManifold (𝓘(ℝ, WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)]
  {T : X ≃ₜ X} (D : SpectralDecomposition (E := E) T) {g : X → ℝ} {A : Set X}
  (h : HG1 D g A) (a : AuxiliaryAnosov (F := F) (Y := Y) (ι := κ) h.r)

/-- Ordinary fixed-map product facts. Retained pressure preservation is
proved below from the actual factor and product tangent dynamics.
The splitting is identified through both genuine projection derivatives. -/
structure Data where
  geometry : ProductDecompositionSources (E := E) (F := F) (S := a.map) D
  map_calculus : HilbertMapProductRegularity (E := E) (F := F) (X := X) (Y := Y) h.r
  weight_calculus : HilbertFirstProjectionRegularity (E := E) (F := F) (X := X) (Y := Y) (h.r - 1)
  nonwandering_tangent : HyperbolicData (E := WithLp 2 (E × F))
    (T.prodCongr a.map) (nonwanderingSet (T.prodCongr a.map))
  periodic_dense : closure (periodicPts (T.prodCongr a.map : X × Y → X × Y)) =
    nonwanderingSet (T.prodCongr a.map)
  equilibrium : EquilibriumPackage
    ((geometry.decomposition D a.hl.basic).basic h.dominant).hyperbolic
    (fun z : X × Y => g z.1)

namespace Data
variable (d : Data D h a)

def decomposition : SpectralDecomposition (E := WithLp 2 (E × F)) (T.prodCongr a.map) :=
  d.geometry.decomposition D a.hl.basic

/-- The genuine canonical product splitting is derived from actual tangent dynamics. -/
def splitting [IsContinuousRiemannianBundle E (TangentSpace (𝓘(ℝ,E)) : X → Type _)]
  [IsContinuousRiemannianBundle F (TangentSpace (𝓘(ℝ,F)) : Y → Type _)]
  [IsContinuousRiemannianBundle (WithLp 2 (E × F))
    (TangentSpace (𝓘(ℝ,WithLp 2 (E × F))) : X × Y → Type _)] (i:Fin D.count) :
    ProductSplittingIdentification (D.basic i).hyperbolic a.hl.basic.hyperbolic (d.geometry.tangent i) :=
  ProductSplittingIdentification.of_actual_product _ _ _
    (h.map_regular.mdifferentiable h.regularity_gt_one.le)
    (h.inverse_regular.mdifferentiable h.regularity_gt_one.le)
    (a.hl.map_regular.mdifferentiable a.hl.regularity_gt_one.le)
    (a.hl.inverse_regular.mdifferentiable a.hl.regularity_gt_one.le)
    ((d.map_calculus T a.map h.map_regular (by simpa only [a.regularity] using a.hl.map_regular)).mdifferentiable h.regularity_gt_one.le)
    ((d.map_calculus T.symm a.map.symm h.inverse_regular (by simpa only [a.regularity] using a.hl.inverse_regular)).mdifferentiable h.regularity_gt_one.le)

section ProvedThermodynamics
variable [CompactSpace X] [CompactSpace Y]
  [IsContinuousRiemannianBundle E (TangentSpace (𝓘(ℝ,E)) : X → Type _)]
  [IsContinuousRiemannianBundle F (TangentSpace (𝓘(ℝ,F)) : Y → Type _)]
  [IsContinuousRiemannianBundle (WithLp 2 (E × F))
    (TangentSpace (𝓘(ℝ,WithLp 2 (E × F))) : X × Y → Type _)]

omit [BorelSpace X] [BorelSpace Y] in
/-- Actual retained pressure equality, derived without a pressure source. -/
theorem pressure (i : Fin D.count) (live : D.core i ⊆ Aᶜ) :
    (d.geometry.decomposition D a.hl.basic).pressure (fun z : X × Y => g z.1) i = D.pressure g i :=
  h.retained_product_pressure D a d.geometry (splitting D h a d) d.map_calculus i live

/-- The auxiliary regularity fields are produced from the same auxiliary
map used by the actual independent noise constructor. -/
def hgSources : ProductHGSources D a.hl.basic d.geometry h where
  auxiliary_regular := by simpa only [a.regularity] using a.hl.map_regular
  auxiliary_inverse_regular := by simpa only [a.regularity] using a.hl.inverse_regular
  map_calculus := d.map_calculus
  weight_calculus := d.weight_calculus
  nonwandering_tangent := d.nonwandering_tangent
  periodic_dense := d.periodic_dense
  pressure := d.pressure
  equilibrium := d.equilibrium

def hg1 : HG1 d.decomposition (fun z : X × Y => g z.1) (A ×ˢ (univ : Set Y)) :=
  h.hilbertStabilize D a.hl.basic d.geometry d.hgSources a.hl.mixing

end ProvedThermodynamics

omit [BorelSpace X] [BorelSpace Y] in
/-- Nonmixing subordinate basic sets remain allowed: positivity of both
product dimensions comes entirely from the full auxiliary factor. -/
theorem stable_positive [IsContinuousRiemannianBundle E (TangentSpace (𝓘(ℝ,E)) : X → Type _)]
  [IsContinuousRiemannianBundle F (TangentSpace (𝓘(ℝ,F)) : Y → Type _)]
  [IsContinuousRiemannianBundle (WithLp 2 (E × F))
    (TangentSpace (𝓘(ℝ,WithLp 2 (E × F))) : X × Y → Type _)] (i : Fin D.count) :
    ∀ z ∈ d.decomposition.core i,
      0 < Module.finrank ℝ ((d.decomposition.basic i).hyperbolic.stable z) :=
  (splitting D h a d i).stable_positive _ _ _ (fun y _ => a.stable_positive y)

omit [BorelSpace X] [BorelSpace Y] in
theorem unstable_positive [IsContinuousRiemannianBundle E (TangentSpace (𝓘(ℝ,E)) : X → Type _)]
  [IsContinuousRiemannianBundle F (TangentSpace (𝓘(ℝ,F)) : Y → Type _)]
  [IsContinuousRiemannianBundle (WithLp 2 (E × F))
    (TangentSpace (𝓘(ℝ,WithLp 2 (E × F))) : X × Y → Type _)] (i : Fin D.count) :
    ∀ z ∈ d.decomposition.core i,
      0 < Module.finrank ℝ ((d.decomposition.basic i).hyperbolic.unstable z) :=
  (splitting D h a d i).unstable_positive _ _ _ (fun y _ => a.unstable_positive y)

variable (P : Maps (E := E) (ι := ι) T h.r)
  (productCalculus : FractionalProductCalculus (E := E) (F := F) (X := X) (Y := Y) h.r)
  (linearCalculus : LinearFractionalCalculus (T := T.prodCongr a.map)
    (LinearRechartedManifold.hilbertProductEquiv (A := E) (B := F)) h.r)

/-- The actual family is constructed on the sum of the original control
indices, in the Hilbert product charts used by the anisotropic model. -/
def maps : Maps (E := WithLp 2 (E × F)) (ι := ι ⊕ κ) (T.prodCongr a.map) h.r :=
  productHilbertMaps P a.noise h.map_regular
    (by simpa only [a.regularity] using a.hl.map_regular) productCalculus linearCalculus

omit [BorelSpace X] [BorelSpace Y]
  [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)] in
theorem maps_family (ε : ℝ≥0) (control : Control (ι := ι ⊕ κ)) (z : X × Y) :
    (maps D h a P productCalculus linearCalculus).family ε control z =
      independentFamily P a.noise ε control z := rfl

/-- The actual varying laws are independent at each scale; no continuity of
those laws in the noise scale is requested. -/
def laws (L : Laws (ι := ι)) : Laws (ι := ι ⊕ κ) := productLaws L a.laws

variable {I : Type*} (Λ : I → Set X) (ℓ : ℕ)
  (filtration : Global.ShiftedFiltrationGeometry.AdaptedSource T A Λ ℓ)

def adapted [CompactSpace Y] : Global.ShiftedFiltrationGeometry.AdaptedSource
    (T.prodCongr a.map) (A ×ˢ (univ : Set Y)) (fun i => Λ i ×ˢ univ) ℓ :=
  Global.ProductAdaptedFiltration.source T a.map A Λ ℓ filtration

omit [BorelSpace X] [BorelSpace Y]
  [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)] in
/-- Strict trapping, needed for positive survival, is preserved literally. -/
theorem strict_trapping (trap : MapsTo T (closure A) A) :
    MapsTo (T.prodCongr a.map) (closure (A ×ˢ (univ : Set Y))) (A ×ˢ univ) :=
  Global.ProductAdaptedFiltration.strict_trapping T a.map A trap

omit [BorelSpace X] [BorelSpace Y]
  [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)] in
theorem closed_layer [CompactSpace Y] (N : ℕ) (i : Fin ℓ) :
    Global.FiltrationPressureConfinement.closedLayer (T.prodCongr a.map) (A ×ˢ (univ : Set Y))
      (fun j => Λ j ×ˢ univ) ℓ N (adapted D h a Λ ℓ filtration) i =
      Global.FiltrationPressureConfinement.closedLayer T A Λ ℓ N filtration i ×ˢ univ :=
  Global.ProductAdaptedFiltration.closedLayer_product T a.map A Λ ℓ filtration N i

end Data

section ProvedThermodynamics
variable [CompactSpace X] [CompactSpace Y]
  [IsContinuousRiemannianBundle E (TangentSpace (𝓘(ℝ,E)) : X → Type _)]
  [IsContinuousRiemannianBundle F (TangentSpace (𝓘(ℝ,F)) : Y → Type _)]
  [IsContinuousRiemannianBundle (WithLp 2 (E × F))
    (TangentSpace (𝓘(ℝ,WithLp 2 (E × F))) : X × Y → Type _)]

/-- HG2 uses exactly the same product decomposition/noise/filtration; its
extra mixing and pressure-distinctness clauses are transported internally. -/
def hg2 (h2 : HG2 D g A) (a2 : AuxiliaryAnosov (F := F) (Y := Y) (ι := κ) h2.r)
    (d : Data D h2.toHG1 a2) :
    HG2 d.decomposition (fun z : X × Y => g z.1) (A ×ˢ (univ : Set Y)) :=
  h2.hilbertStabilize D a2.hl.basic d.geometry d.hgSources a2.hl.mixing

end ProvedThermodynamics
end ConditionedStochasticStabilityHyperbolic.Paper.ActualAnosovGlobalStabilization
