module
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedActualAnosovGlobalStabilization
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedLinearFractionalCalculus
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeProductLocalWeight
public import ConditionedStochasticStabilityHyperbolic.Global.ConstructedOrderedFiltration
public import LeanShared.MeasureTheory.ForwardNullReference
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedHGActualProductEquilibrium
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedRegularNoiseSmoothing
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedRetainedEquilibria
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeHG1Application
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedHG1FiltrationData
public import ConditionedStochasticStabilityHyperbolic.Paper.HG1OrdinaryProductBoundary
/-! Native HG1 main conclusions (thm:global-existence, thm:global) with the constructed fixed-A
filtration, whose shifted boundaries are null for the canonical analytic reference. Besides the
deterministic, noise and weight data of the manuscript, only the local regularity of the physical
weight near the retained basic sets is used; every analytic, spectral and local source is
constructed. -/
public noncomputable section
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 20000
open Set Function Bundle MeasureTheory Filter IsManifold
open scoped Manifold ContDiff Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.NativeProvedHG1
open ProvedHG1Filtration
open LeanShared HyperbolicBasicSet RegularNoise Global ShiftedFiltrationGeometry
open FiltrationPressureConfinement ActualFiltrationGrowth DerivedHG2Application AssembleShiftedPrefixFamilies
open PhysicalClassicalLayer PhysicalClassicalPrefixSources ActualProductRestrictedChain
open ComplexStrongFeller LayerQuasiErgodic
variable {E ι : Type*} {F κ X Y : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [CompactSpace X] [SecondCountableTopology X] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [MetricSpace Y] [CompactSpace Y] [SecondCountableTopology Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [RiemannianBundle (fun y : Y => TangentSpace (𝓘(ℝ, F)) y)]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  [MeasurableSpace (WithLp 2 (E × F))] [BorelSpace (WithLp 2 (E × F))] [MeasurableSpace Y] [BorelSpace Y]
  [Fintype ι] [Fintype κ]
local instance hg1ActualSourceOrdinaryCharts : ChartedSpace (E × F) (X × Y) := productCharts
local instance hg1ActualSourceOrdinaryManifold : IsManifold (𝓘(ℝ, E × F)) ∞ (X × Y) := productManifold
local instance hg1ActualSourceHilbertCharts : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance hg1ActualSourceHilbertManifold : IsManifold (𝓘(ℝ, WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)]
  {T : X ≃ₜ X} (D : SpectralDecomposition (E := E) T) {g : X → ℝ} {A : Set X}
  (h : HG1 D g A) (a : AuxiliaryAnosov (F := F) (Y := Y) (ι := κ) h.r)


variable (P : Maps (E := E) (ι := ι) T h.r) (L : Laws (ι := ι))
  (productCalculus : FractionalProductCalculus (E := E) (F := F) (X := X) (Y := Y) h.r)

variable (φ : X → ℝ) (hw : Continuous (fun x => Real.exp (φ x)))
  (R : ℝ) (hR : 0 < R) (bound : ∀ x, Real.exp (φ x) ≤ R)
  (strict : MapsTo T (closure A) A)

set_option quotPrecheck false in
local notation "σ" => (FiniteSmoothReferenceCharts.referenceMeasure (M := X × Y)
  (volume : Measure (WithLp 2 (E × F))))

set_option quotPrecheck false in
local notation "chosen" => filtration D h σ strict
set_option quotPrecheck false in
local notation "order" => (chosen).order
set_option quotPrecheck false in
local notation "ℓ" => (chosen).order.length
set_option quotPrecheck false in
local notation "Dret" => (chosen).source
set_option quotPrecheck false in
local notation "jsel" => (chosen).selected
set_option quotPrecheck false in
local notation "selEq" => (chosen).selected_dominant
set_option quotPrecheck false in
local notation "realPressure" => (fun i : Fin D.count => (D.pressure g i).toReal)
local notation "PF" => ActualAnosovGlobalStabilization.Data.maps D h a P productCalculus (proved_linearFractionalCalculus (T := T.prodCongr a.map)
    (LinearRechartedManifold.hilbertProductEquiv (A := E) (B := F)) h.r)
local notation "PL" => productLaws L a.laws
set_option quotPrecheck false in
local notation "AP" => (A ×ˢ (univ : Set Y))
local notation "hAP" => h.absorbing_open.prod isOpen_univ
set_option quotPrecheck false in
local notation "LP" => (fun i => D.core i ×ˢ (univ : Set Y))
local notation "DP" => ProductAdaptedFiltration.source T a.map A D.core ℓ Dret
set_option quotPrecheck false in
local notation "wP" => (fun z : X × Y => Real.exp (φ z.1))
local notation "hwP" => hw.comp continuous_fst
local notation "Q" i:max => closedLayer (T.prodCongr a.map) AP LP ℓ 0 DP i
local notation "hcQ" i:max => layerCompact AP LP ℓ 0 DP i
local notation "K" => closedLayer T A D.core ℓ 0 Dret jsel
local instance productLayerCompact (i : Fin ℓ) : CompactSpace (Q i) :=
  isCompact_iff_compactSpace.mp (hcQ i)
local instance originalLayerCompact : CompactSpace (K) :=
  isCompact_iff_compactSpace.mp (layerCompact A D.core ℓ 0 Dret jsel)
local instance auxiliaryUnivCompact : CompactSpace (univ : Set Y) :=
  isCompact_iff_compactSpace.mp isCompact_univ

local notation "C" => ActualAnosovGlobalChains.original D h P L
  (fun x => Real.exp (φ x)) hw.measurable R hR bound
local notation "CP" => ActualAnosovGlobalChains.stabilized D h a P L productCalculus (proved_linearFractionalCalculus (T := T.prodCongr a.map)
    (LinearRechartedManifold.hilbertProductEquiv (A := E) (B := F)) h.r)
  (fun x => Real.exp (φ x)) hw.measurable R hR bound

variable
  [IsContinuousRiemannianBundle E (fun x:X=>TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle F (fun y:Y=>TangentSpace (𝓘(ℝ,F)) y)]
  [IsContinuousRiemannianBundle (WithLp 2 (E×F))
    (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)]

include a productCalculus strict in
omit [MeasurableSpace E] [BorelSpace E] in
theorem conclusions_native
    (weightCalculus : HilbertFirstProjectionRegularity (E := E) (F := F) (X := X) (Y := Y) (h.r - 1))
    (coreAgreement : ∀ i, D.core i ⊆ Aᶜ → EqOn (fun x => Real.exp (φ x)) g (D.core i))
    (localWeightX : ∀ i, D.core i ⊆ Aᶜ → ∃ W : Set X, IsOpen W ∧ D.core i ⊆ W ∧
      ∀ ζ : X → ℝ, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ ζ → tsupport ζ ⊆ W →
        FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (h.r - 1)
          (ζ * fun x => Real.exp (φ x))) :
    letI : CompactSpace ↥(Aᶜ) := isCompact_iff_compactSpace.mp h.absorbing_open.isClosed_compl.isCompact
    ∃ initial : ProbabilityMeasure ↥(Aᶜ), ∃ ν : ℝ≥0 → ProbabilityMeasure ↥(Aᶜ),
      (initial : Measure ↥(Aᶜ)).map Subtype.val = (h.deterministic_equilibrium.state : Measure X) ∧
      ThermodynamicDefinitions.IsEquilibriumState T
        (fun x => φ x - Real.log ((D.basic h.dominant).hyperbolic.unstableJacobian x))
        (D.core h.dominant) h.deterministic_equilibrium.state ∧
      (∀ ζ : ProbabilityMeasure X, ThermodynamicDefinitions.IsEquilibriumState T
        (fun x => φ x - Real.log ((D.basic h.dominant).hyperbolic.unstableJacobian x))
        (D.core h.dominant) ζ → ζ = h.deterministic_equilibrium.state) ∧
      Tendsto ν (𝓝[>] (0 : ℝ≥0)) (𝓝 initial) ∧
      ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ (hε : 0 < ε) (hwindow : ε ≤ P.window),
        let CL := RestrictedNoise.chain (L.law ε)
          (fun z : X × cube (ι := ι) ε => P.family ε z.2.val z.1)
          (P.raw_measurable ε hε hwindow) Aᶜ h.absorbing_open.measurableSet.compl
          (fun x => Real.exp (φ x.val)) (hw.comp continuous_subtype_val).measurable R hR
          (fun x => bound x.val)
        let core := {x : ↥(Aᶜ) | x.val ∈ D.core h.dominant}
        LocalConclusions.NormalizedGap CL core (ν ε) ∧
        CL.IsQuasiErgodic (ν ε : Measure _) ∧ core ⊆ (ν ε : Measure _).support ∧
        (∀ ζ : Measure _, CL.IsQuasiErgodic ζ → core ⊆ ζ.support → ζ = (ν ε : Measure _)) ∧
        Nonempty (LocalConclusions.SimpleSpectralWitness CL R (ν ε)) := by
  have localWeight : ∀ i, D.core i ⊆ Aᶜ → ∃ W : Set (X × Y), IsOpen W ∧
      D.core i ×ˢ (univ : Set Y) ⊆ W ∧
      ∀ ζ : X × Y → ℝ, ContMDiff (𝓘(ℝ, WithLp 2 (E × F))) (𝓘(ℝ)) ∞ ζ → tsupport ζ ⊆ W →
        FractionalManifoldRegularity.Regular (E := WithLp 2 (E × F)) (F := ℝ) (h.r - 1)
          (ζ * fun z : X × Y => Real.exp (φ z.1)) := fun i hi => by
    obtain ⟨W, hW, coreW, smooth⟩ := localWeightX i hi
    exact NativeProductLocalWeight.product_local_weight (F := F) (Y := Y) (h.r - 1)
      (by linarith [h.regularity_gt_one]) (D.core i) W
      (D.basic i).hyperbolic.compact hW coreW (fun x => Real.exp (φ x))
      (fun x => (Real.exp_pos _).le) smooth
  have smoothOriginal : SmoothCubeSubmersionContract (E := E) (M := X) (ι := ι) :=
    proved_smoothCubeSubmersionContract
  have live (i : Fin ℓ) : D.core ((Dret).index i) ⊆ Aᶜ := by
    have index : (Dret).index = PressureFiltrationSource.reversedVertex order :=
      (chosen).index
    rw [index]
    exact ((chosen).cover _).mp (List.get_mem _ _)
  have pressure_identity (i : Fin ℓ) : D.pressure g ((Dret).index i) =
      (realPressure ((Dret).index i) : EReal) :=
    h.retained_real_pressure_identity _ (live i)
  have selectedState : ThermodynamicDefinitions.IsEquilibriumState T
      (fun x=>φ x-Real.log ((D.basic ((Dret).index jsel)).hyperbolic.unstableJacobian x))
      (D.core ((Dret).index jsel)) h.deterministic_equilibrium.state := by
    have same : ((Dret).index jsel) = h.dominant := selEq
    exact same.symm ▸ HG1EquilibriumIdentification.equilibrium D h φ
      (fun x hx=>(coreAgreement h.dominant h.dominant_live hx).symm)
  have product_equilibrium := h.exponential_product_equilibrium D a ((Dret).index jsel)
    φ hw h.deterministic_equilibrium.state selectedState ((ActualAnosovGlobalStabilization.provedData D h a productCalculus weightCalculus).geometry.tangent ((Dret).index jsel))
  obtain ⟨initial, ν, mapped, equilibrium, limit, spectral⟩ :=
    NativeHG1Application.conclusions_native
    (D := D) (h := h) (a := a) (P := P) (L := L)
    (productCalculus := productCalculus) (linearCalculus := (proved_linearFractionalCalculus (T := T.prodCongr a.map)
    (LinearRechartedManifold.hilbertProductEquiv (A := E) (B := F)) h.r))
    (φ := φ) (hw := hw) (R := R) (hR := hR) (bound := bound)
    (retained := Dret) (j := jsel) (selected := selEq)
    (pressure := realPressure) (geometry := (ActualAnosovGlobalStabilization.provedData D h a productCalculus weightCalculus)) (pressure_identity := pressure_identity)
    (coreWeight := fun i x hx => (coreAgreement _ (live i) hx).symm)
    (localWeight := fun i => localWeight _ (live i))
    (strict := strict)
    (shifted_boundary_null := by
      intro N i positive bound
      rw [ProductAdaptedFiltration.shifted_levels]
      exact (chosen).shifted_boundary N i positive bound)
    (smoothOriginal := smoothOriginal)
    (product_equilibrium := product_equilibrium)
  exact ⟨initial, ν, mapped, equilibrium,
    HG1EquilibriumIdentification.unique D h φ
      (fun x hx => (coreAgreement h.dominant h.dominant_live hx).symm), limit, spectral⟩

end ConditionedStochasticStabilityHyperbolic.Paper.NativeProvedHG1
