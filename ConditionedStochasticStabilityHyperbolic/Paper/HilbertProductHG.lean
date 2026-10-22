module

public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductDecomposition

/-! Literal HG transport by a full auxiliary factor. The source pressure
identity concerns the actual unstable-Jacobian potential on every retained
basic set. It is the ordinary pressure addition theorem with zero auxiliary
pressure, not an assumed pressure ordering or noisy spectral conclusion.
Strict trapping remains a separate proved geometric transport. -/
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
local instance hilbertProductHGLocal1 : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance hilbertProductHGLocal2 : IsManifold (𝓘(ℝ, WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)]
  {T : X ≃ₜ X} {S : Y ≃ₜ Y} (D : SpectralDecomposition (E := E) T)
  (auxiliary : BasicData (E := F) S univ univ)
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]


variable {g : X → ℝ} {A : Set X}
  (p : ProductDecompositionSources (E := E) (F := F) (S := S) D)

/-- Ordinary deterministic calculus in the actual Hilbert product charts. -/
def HilbertMapProductRegularity (r : ℝ) : Prop :=
  ∀ (f : X → X) (k : Y → Y),
    FractionalManifoldRegularity.Regular (E := E) (F := E) r f →
    FractionalManifoldRegularity.Regular (E := F) (F := F) r k →
    FractionalManifoldRegularity.Regular (E := WithLp 2 (E × F))
      (F := WithLp 2 (E × F)) r (Prod.map f k)

/-- Ordinary scalar pullback along the Cartesian projection. -/
def HilbertFirstProjectionRegularity (q : ℝ) : Prop :=
  ∀ f : X → ℝ, FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q f →
    FractionalManifoldRegularity.Regular (E := WithLp 2 (E × F)) (F := ℝ) q
      (fun z : X × Y => f z.1)

/-- Classical deterministic product dynamics/thermodynamics, precisely
separated from the HG ordering and graph clauses constructed below. The
auxiliary factor is full, with weight one and pressure zero. -/
structure ProductHGSources (h : HG1 D g A) where
  auxiliary_regular : FractionalManifoldRegularity.Regular (E := F) (F := F) h.r S
  auxiliary_inverse_regular : FractionalManifoldRegularity.Regular (E := F) (F := F) h.r S.symm
  map_calculus : HilbertMapProductRegularity (E := E) (F := F) (X := X) (Y := Y) h.r
  weight_calculus : HilbertFirstProjectionRegularity (E := E) (F := F) (X := X) (Y := Y) (h.r - 1)
  nonwandering_tangent : HyperbolicData (E := WithLp 2 (E × F))
    (T.prodCongr S) (nonwanderingSet (T.prodCongr S))
  periodic_dense : closure (periodicPts (T.prodCongr S : X × Y → X × Y)) =
    nonwanderingSet (T.prodCongr S)
  pressure : ∀ i, D.core i ⊆ Aᶜ → (p.decomposition D auxiliary).pressure (fun z : X × Y => g z.1) i = D.pressure g i
  equilibrium : EquilibriumPackage ((p.decomposition D auxiliary).basic h.dominant).hyperbolic
    (fun z : X × Y => g z.1)

/-- All HG1 set, graph and pressure-order bookkeeping is derived. -/
def HG1.hilbertStabilize (h : HG1 D g A) (s : ProductHGSources D auxiliary p h)
    (mixingAuxiliary : MixingOn S (univ : Set Y)) :
    HG1 (p.decomposition D auxiliary) (fun z : X × Y => g z.1) (A ×ˢ (univ : Set Y)) where
  r := h.r
  regularity_gt_one := h.regularity_gt_one
  map_regular := s.map_calculus T S h.map_regular s.auxiliary_regular
  inverse_regular := s.map_calculus T.symm S.symm h.inverse_regular s.auxiliary_inverse_regular
  axiomA := ⟨s.nonwandering_tangent, s.periodic_dense⟩
  absorbing_open := h.absorbing_open.prod isOpen_univ
  absorbing_forward := ProductGlobalGeometry.absorbing_forward T S A h.absorbing_forward
  weight_regular := s.weight_calculus g h.weight_regular
  weight_nonnegative z := h.weight_nonnegative z.1
  weight_positive i hi z hz := h.weight_positive i ((p.live_iff D auxiliary A i).mp hi) z.1 hz.1
  no_cycles i hi := h.no_cycles i ((p.transGen_edge_iff D auxiliary i i).mp hi)
  dominant := h.dominant
  dominant_live := (p.live_iff D auxiliary A h.dominant).mpr h.dominant_live
  pressure_dominant i hi hine := by
    have live := (p.live_iff D auxiliary A i).mp hi
    rw [s.pressure i live, s.pressure h.dominant h.dominant_live]
    exact h.pressure_dominant i live hine
  deterministic_equilibrium := s.equilibrium
  dominant_mixing := h.dominant_mixing.product mixingAuxiliary

/-- HG2's extra mixing and distinct-pressure clauses are likewise derived. -/
def HG2.hilbertStabilize (h : HG2 D g A) (s : ProductHGSources D auxiliary p h.toHG1)
    (mixingAuxiliary : MixingOn S (univ : Set Y)) :
    HG2 (p.decomposition D auxiliary) (fun z : X × Y => g z.1) (A ×ˢ (univ : Set Y)) where
  toHG1 := h.toHG1.hilbertStabilize D auxiliary p s mixingAuxiliary
  pressures_distinct i j hi hj heq := h.pressures_distinct i j
    ((p.live_iff D auxiliary A i).mp hi) ((p.live_iff D auxiliary A j).mp hj)
    ((s.pressure i ((p.live_iff D auxiliary A i).mp hi)).symm.trans
      (heq.trans (s.pressure j ((p.live_iff D auxiliary A j).mp hj))))
  retained_mixing i hi :=
    (h.retained_mixing i ((p.live_iff D auxiliary A i).mp hi)).product mixingAuxiliary

end ConditionedStochasticStabilityHyperbolic.Paper
