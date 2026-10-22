module
public import ConditionedStochasticStabilityHyperbolic.Global.ConstructedRetainedFiltration
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedLinearFractionalCalculus
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeProductLocalWeight
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedLinearFractionalCalculus
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedHGActualProductEquilibrium
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedRegularNoiseSmoothing
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedRetainedEquilibria
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedHG2FiltrationData
public import ConditionedStochasticStabilityHyperbolic.Paper.ProductLocalMarginalGap
public import ConditionedStochasticStabilityHyperbolic.Global.StabilizedShiftedPrefixApplication
public import ConditionedStochasticStabilityHyperbolic.Global.WindowedHG2Application
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualAnosovGlobalChains
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualHG2NoiseGeometry
public import ConditionedStochasticStabilityHyperbolic.Paper.HG2ClassicalRegularity
public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedGlobalCubeChain
public import ConditionedStochasticStabilityHyperbolic.Paper.CompactMarginalEquilibrium
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeFiltrationShiftedPrefixes
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeFiltrationLocal
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeAuxiliaryGapFamily
public import ConditionedStochasticStabilityHyperbolic.Paper.ChainNormalizationTransport
public import ConditionedStochasticStabilityHyperbolic.Global.FamiliesRescale
public import ConditionedStochasticStabilityHyperbolic.Paper.CanonicalControlSubmersionSources
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedActualAnosovGlobalStabilization
public import LeanShared.Dynamics.ProvedHyperbolicEquilibriumPackage
public import ConditionedStochasticStabilityHyperbolic.Paper.ProductSelectedStratumQuasiErgodic
public import ConditionedStochasticStabilityHyperbolic.Global.ProductSelectedBoundary
public import ConditionedStochasticStabilityHyperbolic.Spectral.ComparedLocalQuasiErgodic
import all ConditionedStochasticStabilityHyperbolic.Paper.ActualAnosovGlobalChains
import all ConditionedStochasticStabilityHyperbolic.Paper.ActualHG2NoiseGeometry
public import ConditionedStochasticStabilityHyperbolic.Global.CompleteHG2Conclusion
public import ConditionedStochasticStabilityHyperbolic.Paper.HG2FirstFullPrefix
public import ConditionedStochasticStabilityHyperbolic.Paper.HG2LabelledIndexReachability

/-! Native HG2 conclusions (thm:global-global) with the prescribed greedy filtration, whose shifted
product boundaries are null for the canonical analytic reference. Every shifted prefix packet, the
selected local outcomes and the auxiliary gap are constructed natively; no source record, spectral
radius, leading record or auxiliary layer record is assumed. This file works with a normalizer
above every retained pressure; the physical weight `exp φ` equals `g` on the retained basic sets and
is locally regular near them. -/
public noncomputable section
set_option maxHeartbeats 3200000
open Set MeasureTheory IsManifold Bundle Filter Function
open scoped Manifold ContDiff NNReal Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.NativeProvedHG2
open HG2ClassicalGlobalStability ProvedHG2Filtration
open LeanShared HyperbolicBasicSet Global ShiftedFiltrationGeometry ActualFiltrationGrowth
open DerivedHG2Application AssembleShiftedPrefixFamilies FiltrationPressureConfinement
open PhysicalClassicalLayer PhysicalClassicalPrefixSources RegularNoise ActualProductRestrictedChain
open LeanShared.ControlledPlaqueClosure ActualHG2BasinGeometry
attribute [local instance] Classical.propDecidable
variable {E ι : Type*} {H κ X Y : Type} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace H] [BorelSpace H]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [ChartedSpace H Y] [IsManifold (𝓘(ℝ, H)) ∞ Y]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [RiemannianBundle (fun y : Y => TangentSpace (𝓘(ℝ, H)) y)]
local instance actualOrdinaryCharts : ChartedSpace (E × H) (X × Y) := productCharts
local instance actualOrdinaryManifold : IsManifold (𝓘(ℝ, E × H)) ∞ (X × Y) := productManifold
local instance actualHilbertCharts : ChartedSpace (WithLp 2 (E × H)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance actualHilbertManifold : IsManifold (𝓘(ℝ, WithLp 2 (E × H))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × H))) z)]
  {T : X ≃ₜ X} (D0 : SpectralDecomposition (E := E) T) (g φ : X → ℝ) (A : Set X)
  (h : HG2 D0 g A)
set_option quotPrecheck false in
local notation "σP" => (FiniteSmoothReferenceCharts.referenceMeasure (M := X × Y)
  (volume : Measure (WithLp 2 (E × H))))

set_option quotPrecheck false in
local notation "Λ" => retainedCore D0 A
set_option quotPrecheck false in
local notation "G" => greedy D0 g A h (HG2.proved_retained_pressure_finiteness h)
set_option quotPrecheck false in
local notation "ell" => (G).order.length

variable (strict : MapsTo T (closure A) A)
set_option quotPrecheck false in
local notation "chosen" => filtration D0 g A h σP strict
set_option quotPrecheck false in
local notation "D" => (chosen).source
set_option quotPrecheck false in
local notation "t" => (G).number
set_option quotPrecheck false in
local notation "terminal" => (G).terminal
set_option quotPrecheck false in
local notation "root" => (G).selectedRoot
set_option quotPrecheck false in
local notation "j" s:max => selectedIndex ell t terminal root s
set_option quotPrecheck false in
local notation "K" s:max => closedLayer T A Λ ell 0 D (j s)

variable (a : AuxiliaryAnosov (F := H) (Y := Y) (ι := κ) h.r)
  (P : Maps (E := E) (ι := ι) T h.r) (L : Laws (ι := ι))
  (productCalculus : FractionalProductCalculus (E := E) (F := H) (X := X) (Y := Y) h.r)
  (hw : Continuous (fun x => Real.exp (φ x)))
  (R : ℝ) (hR : 0 < R) (bound : ∀ x, Real.exp (φ x) ≤ R)
set_option quotPrecheck false in
local notation "FP" => ActualAnosovGlobalStabilization.Data.maps D0 h.toHG1 a P productCalculus (proved_linearFractionalCalculus (T := T.prodCongr a.map) (LinearRechartedManifold.hilbertProductEquiv (A := E) (B := H)) h.r)
set_option quotPrecheck false in
local notation "C" => ActualAnosovGlobalChains.original D0 h.toHG1 P L
  (fun x => Real.exp (φ x)) hw.measurable R hR bound
set_option quotPrecheck false in
local notation "CP" => ActualAnosovGlobalChains.stabilized D0 h.toHG1 a P L productCalculus (proved_linearFractionalCalculus (T := T.prodCongr a.map) (LinearRechartedManifold.hilbertProductEquiv (A := E) (B := H)) h.r)
  (fun x => Real.exp (φ x)) hw.measurable R hR bound
set_option quotPrecheck false in
local notation "DP" => ProductAdaptedFiltration.source T a.map A Λ ell D
set_option quotPrecheck false in
local notation "AP" => (A ×ˢ (univ : Set Y))
set_option quotPrecheck false in
local notation "LP" => (fun i => Λ i ×ˢ (univ : Set Y))
set_option quotPrecheck false in
local notation "hAP" => h.absorbing_open.prod isOpen_univ
set_option quotPrecheck false in
local notation "wP" => (fun z : X × Y => Real.exp (φ z.1))
set_option quotPrecheck false in
local notation "hwP" => hw.comp continuous_fst
set_option quotPrecheck false in
local notation "Q" N:max i:max => closedLayer (T.prodCongr a.map) AP LP ell N DP i
set_option quotPrecheck false in
local notation "hcQ" N:max i:max => layerCompact AP LP ell N DP i
set_option quotPrecheck false in
local notation "pressure" => PaperHG2GreedySelection.pressure D0 g A
local instance compactOriginalLayer (s : Fin t) : CompactSpace (K s) :=
  isCompact_iff_compactSpace.mp (layerCompact A Λ ell 0 D (j s))
local instance compactProductLayer (N : ℕ) (i : Fin ell) : CompactSpace (Q N i) :=
  isCompact_iff_compactSpace.mp (hcQ N i)
set_option quotPrecheck false in
local notation "U" s:max => stratum T A Λ ell 0 D (j s)
set_option quotPrecheck false in
local notation "hU" s:max => stratum_measurable T A Λ ell 0 D h.absorbing_open (j s)
local instance auxCompact : CompactSpace (univ : Set Y) := isCompact_iff_compactSpace.mp isCompact_univ


local notation "openEndpoint" => (proved_openCubeEndpointContract (E := E) (M := X) (ι := ι))
variable (hφ : Measurable φ)
set_option quotPrecheck false in
local notation "WG" => ActualHG2BasinGeometry.windowed D0 g A h (HG2.proved_retained_pressure_finiteness h) D
  (chosen).index
  strict P L openEndpoint φ hφ R hR bound
set_option quotPrecheck false in
local notation "firstSelected" => (⟨0, ActualHG2BasinGeometry.family_number_positive D0 g A h (HG2.proved_retained_pressure_finiteness h)⟩ : Fin t)

variable
  [IsContinuousRiemannianBundle H (fun y:Y=>TangentSpace (𝓘(ℝ,H)) y)]
  [IsContinuousRiemannianBundle (WithLp 2 (E×H))
    (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×H))) z)]


include a productCalculus hφ in
set_option maxHeartbeats 6400000 in
/-- Native HG2 families at a normalizer above every retained pressure. -/
theorem families_large
    (weightCalculus : HilbertFirstProjectionRegularity (E := E) (F := H) (X := X) (Y := Y) (h.r - 1))
    (coreAgreement : ∀ i, D0.core i ⊆ Aᶜ →
      EqOn (fun x => Real.exp (φ x)) g (D0.core i))
    (localWeight : ∀ i, D0.core i ⊆ Aᶜ → ∃ W : Set (X × Y), IsOpen W ∧
      D0.core i ×ˢ (univ : Set Y) ⊆ W ∧
      ∀ ζ : X × Y → ℝ, ContMDiff (𝓘(ℝ, WithLp 2 (E × H))) (𝓘(ℝ)) ∞ ζ → tsupport ζ ⊆ W →
        FractionalManifoldRegularity.Regular (E := WithLp 2 (E × H)) (F := ℝ) (h.r - 1)
          (ζ * fun z : X × Y => Real.exp (φ z.1)))
    (hR1 : 1 ≤ R)
    (hRP : ∀ i : PaperHG2GreedySelection.Retained D0 A, Real.exp (pressure i) + 1 ≤ R) :
    letI : CompactSpace ↥(Aᶜ) := isCompact_iff_compactSpace.mp h.absorbing_open.isClosed_compl.isCompact
    ∃ sf : ∀ ε, 0 < ε → HasStrongFellerKernel (C ε),
      ∃ family : Families T A h.absorbing_open Λ ell D t terminal root C sf,
        (∀ s, ThermodynamicDefinitions.IsEquilibriumState T
          (fun x => φ x - Real.log ((D0.basic ((D).index (j s)).val).hyperbolic.unstableJacobian x))
          (Λ ((D).index (j s))) ((family.equilibrium s).map (Subtype.val : ↥(Aᶜ) → X))) ∧
        (∀ s (ζ : ProbabilityMeasure X), ThermodynamicDefinitions.IsEquilibriumState T
          (fun x => φ x - Real.log ((D0.basic ((D).index (j s)).val).hyperbolic.unstableJacobian x))
          (Λ ((D).index (j s))) ζ →
          ζ = (family.equilibrium s).map (Subtype.val : ↥(Aᶜ) → X)) ∧
        (∀ s, ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, LocalConclusions.NormalizedGapAt P L (K s)
          (Λ ((D).index (j s))) (layerCompact A Λ ell 0 D (j s)).measurableSet
          (fun x => Real.exp (φ x.val)) (hw.measurable.comp measurable_subtype_coe)
          R hR (fun x => bound x.val)
          (⟨family.closedProduct s ε, family.closedProduct_probability s ε⟩ : ProbabilityMeasure (K s)) ε) := by
  classical
  have rank : SmoothCubeSubmersionContract (E := E) (M := X) (ι := ι) :=
    proved_smoothCubeSubmersionContract
  have source : ControlSubmersionSources (E := WithLp 2 (E × H)) (ι := ι ⊕ κ) σP :=
    canonical_controlSubmersionSources (volume : Measure (WithLp 2 (E × H)))
  let : CompactSpace ↥(Aᶜ) := isCompact_iff_compactSpace.mp h.absorbing_open.isClosed_compl.isCompact
  let linearCalculus := proved_linearFractionalCalculus (T := T.prodCongr a.map)
    (LinearRechartedManifold.hilbertProductEquiv (A := E) (B := H)) h.r
  -- Original equilibrium states of the selected basic sets.
  let packages (s : Fin t) : HyperbolicBasicSet.EquilibriumPackage
      (D0.basic ((D).index (j s)).val).hyperbolic g :=
    h.proved_retained_equilibriumPackage ((D).index (j s)).val ((D).index (j s)).property
  let state (s : Fin t) : ProbabilityMeasure X := (packages s).state
  have state_equilibrium (s : Fin t) : ThermodynamicDefinitions.IsEquilibriumState T
      (fun x => φ x - Real.log ((D0.basic ((D).index (j s)).val).hyperbolic.unstableJacobian x))
      (Λ ((D).index (j s))) (state s) :=
    (packages s).equilibrium_actual_phi φ
      (fun x hx => (coreAgreement ((D).index (j s)).val ((D).index (j s)).property hx).symm)
  have state_unique (s : Fin t) (ζ : ProbabilityMeasure X)
      (equilibrium : ThermodynamicDefinitions.IsEquilibriumState T
        (fun x => φ x - Real.log ((D0.basic ((D).index (j s)).val).hyperbolic.unstableJacobian x))
        (Λ ((D).index (j s))) ζ) : ζ = state s :=
    (packages s).unique_actual_phi φ
      (fun x hx => (coreAgreement ((D).index (j s)).val ((D).index (j s)).property hx).symm) ζ
      equilibrium
  -- Global chains and their strong Feller kernels.
  let sf := originalRegularity D0 g φ A h P L hw R hR bound rank
  let sfP := productRegularity D0 g φ A h a P L productCalculus linearCalculus hw R hR bound
    source.smooth_density
  let geometry := (ActualHG2BasinGeometry.windowed D0 g A h
    (HG2.proved_retained_pressure_finiteness h) D (chosen).index
    strict P L openEndpoint φ hφ R hR bound).continued P.window_positive
  have invariant : ∀ s N, ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ _hε : 0 < ε,
      ∀ x ∈ actualPrefix T A Λ ell D (terminal s) N,
        (C ε).killedTransition x (actualPrefix T A Λ ell D (terminal s) N)ᶜ = 0 := by
    intro s N
    filter_upwards [ActualOriginalGlobalChain.eventually_all_levels P L N A h.absorbing_open
      strict (D).levels ell (D).compact_positive (D).adapted_positive
      (fun x => Real.exp (φ x)) hw.measurable R hR bound] with ε good
    intro _hε x hx
    exact good ((terminal s).val + 1) (by omega) x hx
  have product_maps : ∀ ε, (fun z : (X × Y) × cube (ι := ι ⊕ κ) ε => (FP).family ε z.2.val z.1) =
      joint ε (actualMap P ε) (actualMap a.noise ε) := by
    intro ε
    funext z
    rw [ActualAnosovGlobalStabilization.Data.maps_family]
    rfl
  -- Product geometry.
  let dataP := ActualAnosovGlobalStabilization.provedData D0 h.toHG1 a productCalculus weightCalculus
  let Dd := ActualAnosovGlobalStabilization.Data.decomposition D0 h.toHG1 a dataP
  have r1 : 1 < h.r := h.regularity_gt_one
  have auxRegular : FractionalManifoldRegularity.Regular (E := H) (F := H) h.r (a.map : Y → Y) := by
    simpa only [a.regularity] using a.hl.map_regular
  have auxInverse : FractionalManifoldRegularity.Regular (E := H) (F := H) h.r
      (a.map.symm : Y → Y) := by
    simpa only [a.regularity] using a.hl.inverse_regular
  have regP : FractionalManifoldRegularity.Regular (E := WithLp 2 (E × H)) (F := WithLp 2 (E × H))
      h.r (T.prodCongr a.map) :=
    dataP.map_calculus T a.map h.map_regular auxRegular
  have invP : FractionalManifoldRegularity.Regular (E := WithLp 2 (E × H)) (F := WithLp 2 (E × H))
      h.r (T.prodCongr a.map).symm :=
    dataP.map_calculus T.symm a.map.symm h.inverse_regular auxInverse
  let basicP : ∀ i : Fin ell, BasicData (E := WithLp 2 (E × H)) (T.prodCongr a.map)
      (LP ((DP).index i)) (Dd.collar ((D).index i).val) := fun i => Dd.basic ((D).index i).val
  have liveP : ∀ i : Fin ell, LP ((DP).index i) ⊆ APᶜ := fun i z hz hzA =>
    ((D).index i).property hz.1 hzA.1
  have coreWeightP : ∀ i : Fin ell, EqOn (fun z : X × Y => g z.1) wP (LP ((DP).index i)) :=
    fun i z hz => (coreAgreement ((D).index i).val ((D).index i).property hz.1).symm
  have localWeightP := fun i : Fin ell => localWeight ((D).index i).val ((D).index i).property
  have stableP : ∀ i : Fin ell, ∀ z ∈ LP ((DP).index i),
      0 < Module.finrank ℝ ((basicP i).hyperbolic.stable z) := fun i =>
    ActualAnosovGlobalStabilization.Data.stable_positive D0 h.toHG1 a dataP ((D).index i).val
  have pressureP : ∀ i : Fin ell, ThermodynamicDefinitions.pressure (T.prodCongr a.map)
      ((basicP i).hyperbolic.potential (fun z : X × Y => g z.1)) (LP ((DP).index i)) =
      (pressure ((DP).index i) : EReal) := fun i =>
    (dataP.pressure D0 h.toHG1 a ((D).index i).val ((D).index i).property).trans
      (h.toHG1.retained_real_pressure_identity ((D).index i).val ((D).index i).property)
  have mixingP : ∀ s, HyperbolicBasicSet.MixingOn (T.prodCongr a.map) (LP ((D).index (j s))) :=
    fun s => (h.retained_mixing ((D).index (j s)).val ((D).index (j s)).property).product
      a.hl.mixing
  have weightP : FractionalManifoldRegularity.Regular (E := WithLp 2 (E × H)) (F := ℝ) (h.r - 1)
      (fun z : X × Y => g z.1) := weightCalculus g h.weight_regular
  let equilibriumP : ∀ s, EquilibriumPackage (basicP (j s)).hyperbolic (fun z : X × Y => g z.1) :=
    fun s => Classical.choice ((basicP (j s)).exists_proved_equilibriumPackage r1
      (sub_pos.mpr r1) regP invP (mixingP s) _ weightP
      (fun z hz => h.weight_positive ((D).index (j s)).val ((D).index (j s)).property z.1 hz.1))
  -- One representation of the product noise and the global chain identity.
  let pG := MapImage.representation (FP) h.regularity_gt_one.le (FP).window le_rfl
    (FP).window_positive
  have same : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, CP ε =
      NoiseKernel.chain ((productLaws L a.laws).fixedLaw ε)
        (fun z : (X × Y) × RegularNoise.FixedControl (ι := ι ⊕ κ) =>
          MapImage.maps (FP) h.regularity_gt_one.le (FP).window le_rfl (pG.fixedParameters ε z.2) z.1)
        (pG.allScale_measurable ε) APᶜ (hAP).measurableSet.compl wP (hwP).measurable R
        (zero_lt_one.trans_le hR1) (fun z => bound z.1) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds pG.window_positive)] with ε hε window
    have exactRaw := ActualOriginalGlobalChain.chain_eq (FP) (productLaws L a.laws) APᶜ
      (hAP).measurableSet.compl wP (hwP).measurable R hR (fun z => bound z.1) ε hε
      (window.le.trans pG.window_le)
    exact exactRaw.trans (pG.global_chain_literal_cube (productLaws L a.laws) ε hε window.le
      APᶜ (hAP).measurableSet.compl wP (hwP).measurable R hR (fun z => bound z.1)).symm
  -- Native local outcomes on the selected product layers.
  have hφc : Continuous φ := by
    simpa only [Real.log_exp] using hw.log (fun x => (Real.exp_pos _).ne')
  have outcomes := fun s : Fin t => NativeFiltrationLocal.exists_local_outcome LP AP hAP
    (ProductAdaptedFiltration.strict_trapping T a.map A strict) 0 DP basicP liveP r1 regP invP
    (fun z : X × Y => φ z.1) (hφc.comp continuous_fst) (j s)
    (localWeightP (j s)) (stableP (j s)) (mixingP s) (FP) (productLaws L a.laws) 0
  choose g' V' h' hyperbolic dl mapsEq windowEq lawsEq _floor using outcomes
  let fd := fun s => (dl s).family
  have marginals := fun s => CompactMarginalEquilibrium.from_generated_family (K s) (Q 0 (j s))
    (ProductAdaptedFiltration.closedLayer_product T a.map A Λ ell D 0 (j s)) T a.map
    (fun z => φ z.1 - Real.log ((h' s).basic.hyperbolic.unstableJacobian z))
    (LP ((D).index (j s))) (fd s).probability (fd s).initialLimit (fd s).equilibrium
    (fd s).limit (fd s).map_limit (fd s).equilibrium_unique (state s) a.equilibrium.state
    (h.toHG1.exponential_product_equilibrium D0 a ((D).index (j s)).val φ hw (state s)
      (state_equilibrium s) (h' s).basic.hyperbolic)
  choose ν₀ ν limit mapped marginal using marginals
  let liveMap := fun s (x : K s) =>
    (⟨x.val, closedLayer_subset_live T A h.absorbing_open Λ ell D (j s) x.property⟩ : ↥(Aᶜ))
  have continuousLive : ∀ s, Continuous (liveMap s) := fun s => continuous_subtype_val.subtype_mk _
  let equilibrium := fun s => (ν₀ s).map (liveMap s)
  have equilibriumMap : ∀ s, (equilibrium s).map (Subtype.val : ↥(Aᶜ) → X) = state s := by
    intro s
    apply ProbabilityMeasure.toMeasure_injective
    change ((ν₀ s : Measure (K s)).map (liveMap s)).map Subtype.val = _
    rw [Measure.map_map measurable_subtype_coe (continuousLive s).measurable]
    exact mapped s
  have localWeak : ∀ s, Tendsto (fun ε => (ν s ε).map (Subtype.val : K s → X))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 ((equilibrium s).map (Subtype.val : ↥(Aᶜ) → X))) := by
    intro s
    have ready := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous (ν s) (ν₀ s) (limit s)
      (continuous_subtype_val : Continuous (Subtype.val : K s → X))
    have equal : (ν₀ s).map (Subtype.val : K s → X) = (equilibrium s).map (Subtype.val : ↥(Aᶜ) → X) := by
      apply ProbabilityMeasure.toMeasure_injective
      change _ = ((ν₀ s : Measure (K s)).map (liveMap s)).map Subtype.val
      rw [Measure.map_map measurable_subtype_coe (continuousLive s).measurable]
      rfl
    exact equal ▸ ready
  have smallWindow : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ε ≤ min P.window a.noise.window :=
    mem_nhdsWithin_of_mem_nhds (eventually_le_nhds (lt_min P.window_positive a.noise.window_positive))
  have actualPair := ActualAnosovGlobalChains.actual_pair D0 h.toHG1 a P L productCalculus
    linearCalculus (fun x => Real.exp (φ x)) hw.measurable R hR bound
  -- The selected product chains with the outcome chains: same maps, laws and weight.
  have outcomeChain : ∀ s ε (hε : 0 < ε) (hfw : ε ≤ (fd s).window) (hεP : ε ≤ (FP).window),
      RestrictedNoise.chain ((dl s).laws.law ε)
        (fun z : (X × Y) × cube (ι := ι ⊕ κ) ε => (dl s).maps.family ε z.2.val z.1)
        ((dl s).maps.raw_measurable ε hε (hfw.trans (fd s).window_bound)) (Q 0 (j s))
        (hcQ 0 (j s)).measurableSet (fun x => wP x.val) (fd s).weight_continuous.measurable
        (dl s).scale (dl s).scale_positive (fd s).weight_bound =
      RestrictedNoise.chain ((productLaws L a.laws).law ε)
        (fun z : (X × Y) × cube (ι := ι ⊕ κ) ε => (FP).family ε z.2.val z.1)
        ((FP).raw_measurable ε hε hεP) (Q 0 (j s)) (hcQ 0 (j s)).measurableSet
        (fun x => wP x.val) ((hwP).measurable.comp measurable_subtype_coe)
        (dl s).scale (dl s).scale_positive (fd s).weight_bound := by
    intro s ε hε hfw hεP
    have key : ∀ (G₀ : (X × Y) × cube (ι := ι ⊕ κ) ε → X × Y) (hG : Measurable G₀),
        G₀ = (fun z : (X × Y) × cube (ι := ι ⊕ κ) ε => (FP).family ε z.2.val z.1) →
        RestrictedNoise.chain ((dl s).laws.law ε) G₀ hG (Q 0 (j s)) (hcQ 0 (j s)).measurableSet
          (fun x => wP x.val) (fd s).weight_continuous.measurable (dl s).scale
          (dl s).scale_positive (fd s).weight_bound =
        RestrictedNoise.chain ((productLaws L a.laws).law ε)
          (fun z : (X × Y) × cube (ι := ι ⊕ κ) ε => (FP).family ε z.2.val z.1)
          ((FP).raw_measurable ε hε hεP) (Q 0 (j s)) (hcQ 0 (j s)).measurableSet
          (fun x => wP x.val) ((hwP).measurable.comp measurable_subtype_coe) (dl s).scale
          (dl s).scale_positive (fd s).weight_bound := by
      intro G₀ hG e
      subst e
      rw [lawsEq s]
    exact key _ _ (funext fun z => mapsEq s ε z.2.val z.1)
  have familyWindow : ∀ s, ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ε ≤ (fd s).window := fun s =>
    mem_nhdsWithin_of_mem_nhds (eventually_le_nhds (fd s).window_positive)
  have localUnique : ∀ s, ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ _hε : 0 < ε,
      ∀ ζ : Measure (Q 0 (j s)),
        (RestrictedLayerChain.chain (CP ε) (Q 0 (j s)) (hcQ 0 (j s)).measurableSet).IsQuasiErgodic ζ →
        {x | x.val ∈ LP ((D).index (j s))} ⊆ ζ.support → ζ = ((fd s).probability ε : Measure _) := by
    intro s
    filter_upwards [familyWindow s, actualPair, smallWindow] with ε hfw ha hwin
    intro hε ζ hζ hs
    have hεP : ε ≤ (FP).window := by
      have := hfw.trans (fd s).window_bound
      rwa [windowEq s] at this
    have rawEq : CP ε = NoiseKernel.chain ((productLaws L a.laws).law ε)
        (fun z : (X × Y) × cube (ι := ι ⊕ κ) ε => (FP).family ε z.2.val z.1)
        ((FP).raw_measurable ε hε hεP) APᶜ (hAP).measurableSet.compl wP (hwP).measurable R hR
        (fun z => bound z.1) := by
      apply (ha hε hwin).2.trans
      congr 1
    have localEq := LiteralNoiseLiveChain.actual_local_chain_eq_global_restriction
      ((productLaws L a.laws).law ε)
      (fun z : (X × Y) × cube (ι := ι ⊕ κ) ε => (FP).family ε z.2.val z.1)
      ((FP).raw_measurable ε hε hεP) APᶜ (Q 0 (j s)) (hAP).measurableSet.compl
      (hcQ 0 (j s)).measurableSet
      (closedLayer_subset_live (T.prodCongr a.map) AP hAP LP ell DP (j s))
      wP (hwP).measurable R hR (fun z => bound z.1)
    have qemR : (RestrictedNoise.chain ((productLaws L a.laws).law ε)
        (fun z : (X × Y) × cube (ι := ι ⊕ κ) ε => (FP).family ε z.2.val z.1)
        ((FP).raw_measurable ε hε hεP) (Q 0 (j s)) (hcQ 0 (j s)).measurableSet
        (fun x => wP x.val) ((hwP).measurable.comp measurable_subtype_coe) R hR
        (fun x => bound x.val.1)).IsQuasiErgodic ζ := by
      rw [localEq, ← rawEq]
      exact hζ
    have qemScale := ChainNormalizationTransport.isQuasiErgodic
      (RestrictedNoise.liveKernel ((productLaws L a.laws).law ε)
        (fun z : (X × Y) × cube (ι := ι ⊕ κ) ε => (FP).family ε z.2.val z.1)
        ((FP).raw_measurable ε hε hεP) (Q 0 (j s)) (hcQ 0 (j s)).measurableSet)
      (fun x => wP x.val) ((hwP).measurable.comp measurable_subtype_coe)
      (fun x => (Real.exp_pos _).le)
      (RestrictedNoise.liveKernel_mass_le_one _ _ _ _ _) R (dl s).scale hR (dl s).scale_positive
      (fun x => bound x.val.1) (fd s).weight_bound ζ qemR
    exact ((fd s).point ε hε hfw).2.2.1 ζ ((outcomeChain s ε hε hfw hεP) ▸ qemScale) hs
  have produced := NativeFiltrationShiftedPrefixes.produce LP (fun z : X × Y => g z.1) AP hAP
    (ProductAdaptedFiltration.strict_trapping T a.map A strict) DP basicP liveP r1 regP invP wP hwP
    (fun z => Real.exp_pos _) coreWeightP localWeightP stableP pressure pressureP (FP)
    (productLaws L a.laws) R hR1 (fun i => hRP ((D).index i)) (fun z => bound z.1) pG σP source
    t terminal root mixingP equilibriumP
    (ActualHG2BasinGeometry.adapted_pressure_gap D0 g A h
      (HG2.proved_retained_pressure_finiteness h) D (chosen).index)
    (fun N i hi bound => by
      rw [ProductAdaptedFiltration.shifted_levels]
      exact (chosen).boundary N i hi bound)
    CP sfP same (fun s => (fd s).probability) localUnique
  obtain ⟨νY, eventY⟩ := NativeAuxiliaryGapFamily.exists_family_native a
  have auxiliary : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ (hε : 0 < ε) (hwin : ε ≤ min P.window a.noise.window),
      ∃ ζ : ProbabilityMeasure (univ : Set Y),
        LocalConclusions.NormalizedGap
          (ActualCompactNoiseGap.auxiliaryLocal P a.noise a.laws ε hε hwin 1 le_rfl) univ ζ := by
    filter_upwards [eventY] with ε output
    obtain ⟨hεY, windowY, gapY⟩ := output
    intro hε hwin
    exact ⟨νY ε, gapY⟩
  have localGaps : ∀ s, ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, LocalConclusions.NormalizedGapAt P L (K s)
      (Λ ((D).index (j s))) (layerCompact A Λ ell 0 D (j s)).measurableSet
      (fun x => Real.exp (φ x.val)) (hw.measurable.comp measurable_subtype_coe)
      R hR (fun x => bound x.val) (ν s ε) ε := by
    intro s
    filter_upwards [familyWindow s, auxiliary, actualPair, smallWindow, self_mem_nhdsWithin]
      with ε hfw hy ha hwin he
    have hεP : ε ≤ (FP).window := by
      have := hfw.trans (fd s).window_bound
      rwa [windowEq s] at this
    let νY' := Classical.choose (hy he hwin)
    have gapY := Classical.choose_spec (hy he hwin)
    have localEq := LiteralNoiseLiveChain.actual_local_chain_eq_global_restriction
      (L.law ε) (actualMap P ε) (actualMap_measurable P ε he (le_min_iff.mp hwin).1)
      Aᶜ (K s) h.absorbing_open.measurableSet.compl (layerCompact A Λ ell 0 D (j s)).measurableSet
      (closedLayer_subset_live T A h.absorbing_open Λ ell D (j s))
      (fun x => Real.exp (φ x)) hw.measurable R hR bound
    have sfLocal : HasStrongFellerKernel (ActualProductRestrictedChain.originalChain L ε
        (actualMap P ε) (actualMap_measurable P ε he (le_min_iff.mp hwin).1)
        (K s) (layerCompact A Λ ell 0 D (j s)).measurableSet
        (fun x => Real.exp (φ x)) hw.measurable R hR bound) := by
      change HasStrongFellerKernel (RestrictedNoise.chain _ _ _ _ _ _ _ _ _ _)
      rw [localEq, ← (ha he hwin).1]
      exact RestrictedLayerChain.strongFeller (C ε) (sf ε he) (K s)
        (layerCompact A Λ ell 0 D (j s)).measurableSet
    obtain ⟨_he, _hw, gapScale⟩ := (fd s).gap ε he hfw
    have gapOutcome := (outcomeChain s ε he hfw hεP) ▸ gapScale
    have gapR := NormalizedGapRenormalization.restrictedNoise ((productLaws L a.laws).law ε)
      (fun z : (X × Y) × cube (ι := ι ⊕ κ) ε => (FP).family ε z.2.val z.1)
      ((FP).raw_measurable ε he hεP) (Q 0 (j s)) (hcQ 0 (j s)).measurableSet
      (fun x => wP x.val) ((hwP).measurable.comp measurable_subtype_coe) (dl s).scale R
      (dl s).scale_positive hR (fd s).weight_bound (fun x => bound x.val.1) _ _ gapOutcome
    have gap := ProductLocalMarginalGap.normalized_gap L a.laws ε
      (actualMap P ε) (actualMap a.noise ε)
      (actualMap_measurable P ε he (le_min_iff.mp hwin).1)
      (actualMap_measurable a.noise ε he (le_min_iff.mp hwin).2)
      (K s) (layerCompact A Λ ell 0 D (j s)).measurableSet
      (Q 0 (j s)) (hcQ 0 (j s)).measurableSet
      (ProductAdaptedFiltration.closedLayer_product T a.map A Λ ell D 0 (j s))
      (fun x => Real.exp (φ x)) hw.measurable (fun x => (Real.exp_pos (φ x)).le)
      R hR bound (fun z => (FP).family ε z.2.val z.1) ((FP).raw_measurable ε he hεP)
      (product_maps ε) ((fd s).probability ε) (ν s ε) (marginal s ε)
      (Λ ((D).index (j s))) (Classical.choice a.nonempty) sfLocal νY' gapY gapR
    exact ⟨he, (le_min_iff.mp hwin).1, gap⟩
  have ready := StabilizedShiftedPrefixApplication.all_clauses_from_produced_prefixes
    T a.map A h.absorbing_open Λ ell D t terminal root P a.noise L a.laws
    (fun x => Real.exp (φ x)) hw.measurable R hR bound (fun x => le_of_lt (Real.exp_pos _))
    C sf CP sfP (fun s ε => (ν s ε : Measure (K s)))
    (fun s ε => ((fd s).probability ε : Measure (Q 0 (j s)))) produced
    actualPair auxiliary invariant (fun s => ((D).index (j s)).property) marginal
    (fun _ _ => inferInstance) equilibrium localWeak
    (fun s => (D0.basic ((D).index (j s)).val).nonempty) (G).selected_order geometry
    (ActualHG2BasinGeometry.order_positive D0 g A h (HG2.proved_retained_pressure_finiteness h))
    P.constant P.constant_positive.le
    (ActualHG2BasinGeometry.continued_noise_bound D0 g A h
      (HG2.proved_retained_pressure_finiteness h) D (chosen).index
      strict P L openEndpoint φ hφ R hR bound) (Classical.choice a.nonempty)
  obtain ⟨family, products, familyEq, δ₀, positive, clauses⟩ := ready
  have equilibriumFamily : ∀ s, ThermodynamicDefinitions.IsEquilibriumState T
      (fun x => φ x - Real.log ((D0.basic ((D).index (j s)).val).hyperbolic.unstableJacobian x))
      (Λ ((D).index (j s))) ((family.equilibrium s).map (Subtype.val : ↥(Aᶜ) → X)) := by
    intro s
    rw [familyEq, equilibriumMap]
    exact state_equilibrium s
  have unique : ∀ s (ζ : ProbabilityMeasure X), ThermodynamicDefinitions.IsEquilibriumState T
      (fun x => φ x - Real.log ((D0.basic ((D).index (j s)).val).hyperbolic.unstableJacobian x))
      (Λ ((D).index (j s))) ζ →
      ζ = (family.equilibrium s).map (Subtype.val : ↥(Aᶜ) → X) := fun s ζ hζ =>
    (state_unique s ζ hζ).trans (state_unique s _ (equilibriumFamily s)).symm
  have familyGaps : ∀ s, ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, LocalConclusions.NormalizedGapAt P L (K s)
      (Λ ((D).index (j s))) (layerCompact A Λ ell 0 D (j s)).measurableSet
      (fun x => Real.exp (φ x.val)) (hw.measurable.comp measurable_subtype_coe)
      R hR (fun x => bound x.val)
      (⟨family.closedProduct s ε, family.closedProduct_probability s ε⟩ : ProbabilityMeasure (K s)) ε := by
    intro s
    filter_upwards [localGaps s] with ε gap
    have sameν : (⟨family.closedProduct s ε, family.closedProduct_probability s ε⟩ :
        ProbabilityMeasure (K s)) = ν s ε := by
      apply ProbabilityMeasure.toMeasure_injective
      exact congrFun (congrFun products s) ε
    exact sameν.symm ▸ gap
  exact ⟨sf, family, equilibriumFamily, unique, familyGaps⟩

include a productCalculus hφ in
set_option maxHeartbeats 6400000 in
/-- Native thm:global-global: the HG2 conclusions for any normalizer of the physical weight. -/
theorem complete_with_local_strata_native
    (weightCalculus : HilbertFirstProjectionRegularity (E := E) (F := H) (X := X) (Y := Y) (h.r - 1))
    (coreAgreement : ∀ i, D0.core i ⊆ Aᶜ →
      EqOn (fun x => Real.exp (φ x)) g (D0.core i))
    (localWeightX : ∀ i, D0.core i ⊆ Aᶜ → ∃ W : Set X, IsOpen W ∧ D0.core i ⊆ W ∧
      ∀ ζ : X → ℝ, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ ζ → tsupport ζ ⊆ W →
        FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (h.r - 1)
          (ζ * fun x => Real.exp (φ x)))
 :
    letI : CompactSpace ↥(Aᶜ) := isCompact_iff_compactSpace.mp h.absorbing_open.isClosed_compl.isCompact
    ∃ sf : ∀ ε, 0 < ε → HasStrongFellerKernel (C ε),
      ∃ family : Families T A h.absorbing_open Λ ell D t terminal root C sf,
        (∀ s, ThermodynamicDefinitions.IsEquilibriumState T
          (fun x => φ x - Real.log ((D0.basic ((D).index (j s)).val).hyperbolic.unstableJacobian x))
          (Λ ((D).index (j s))) ((family.equilibrium s).map (Subtype.val : ↥(Aᶜ) → X))) ∧
        (∀ s (ζ : ProbabilityMeasure X), ThermodynamicDefinitions.IsEquilibriumState T
          (fun x => φ x - Real.log ((D0.basic ((D).index (j s)).val).hyperbolic.unstableJacobian x))
          (Λ ((D).index (j s))) ζ →
          ζ = (family.equilibrium s).map (Subtype.val : ↥(Aᶜ) → X)) ∧
        ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ P.window ∧
          LiteralHG2Clauses.Clauses T A Λ ell D t terminal root
            (WindowedHG2Application.literalProcess WG) (WG).maps
            (liveLaw T A h.absorbing_open Λ ell D t terminal root C sf family) family.equilibrium δ ∧
          LabelledHG2Clauses.Clauses T A Λ ell D t terminal root
            (WindowedHG2Application.literalProcess WG)
            (liveLaw T A h.absorbing_open Λ ell D t terminal root C sf family) δ ∧
          (∀ ε, 0 < ε → ε < δ → Nonempty (LocalConclusions.SimpleSpectralWitness
            (WindowedHG2Application.literalProcess WG ε) R
            (liveLaw T A h.absorbing_open Λ ell D t terminal root C sf family firstSelected ε))) ∧
          ∀ ε (he : 0 < ε) (_small : ε < δ) (window : ε ≤ P.window) (q : Fin t),
            ∃ νU : ProbabilityMeasure (U q),
              (νU : Measure (U q)).map Subtype.val =
                (liveLaw T A h.absorbing_open Λ ell D t terminal root C sf family q ε : Measure ↥(Aᶜ)).map Subtype.val ∧
              let CU := RestrictedNoise.chain (L.law ε) (actualMap P ε)
                (actualMap_measurable P ε he window) (U q) (hU q)
                (fun x => Real.exp (φ x.val)) (hw.measurable.comp measurable_subtype_coe)
                R hR (fun x => bound x.val)
              CU.IsQuasiErgodic (νU : Measure (U q)) ∧
                {x : U q | x.val ∈ Λ ((D).index (j q))} ⊆ (νU : Measure (U q)).support ∧
                ∀ ζ : Measure (U q), CU.IsQuasiErgodic ζ →
                  {x : U q | x.val ∈ Λ ((D).index (j q))} ⊆ ζ.support → ζ = (νU : Measure (U q)) := by
  have localWeight : ∀ i, D0.core i ⊆ Aᶜ → ∃ W : Set (X × Y), IsOpen W ∧
      D0.core i ×ˢ (univ : Set Y) ⊆ W ∧
      ∀ ζ : X × Y → ℝ, ContMDiff (𝓘(ℝ, WithLp 2 (E × H))) (𝓘(ℝ)) ∞ ζ → tsupport ζ ⊆ W →
        FractionalManifoldRegularity.Regular (E := WithLp 2 (E × H)) (F := ℝ) (h.r - 1)
          (ζ * fun z : X × Y => Real.exp (φ z.1)) := fun i hi => by
    obtain ⟨W, hW, coreW, smooth⟩ := localWeightX i hi
    exact NativeProductLocalWeight.product_local_weight (F := H) (Y := Y) (h.r - 1)
      (by linarith [h.regularity_gt_one]) (D0.core i) W
      (D0.basic i).hyperbolic.compact hW coreW (fun x => Real.exp (φ x))
      (fun x => (Real.exp_pos _).le) smooth
  classical
  have rank : SmoothCubeSubmersionContract (E := E) (M := X) (ι := ι) :=
    proved_smoothCubeSubmersionContract
  let : CompactSpace ↥(Aᶜ) := isCompact_iff_compactSpace.mp h.absorbing_open.isClosed_compl.isCompact
  -- A large normalizer; every analytic construction is made there.
  let Rbig : ℝ := max R 1 + ∑ i : PaperHG2GreedySelection.Retained D0 A, (Real.exp (pressure i) + 1)
  have sumNonneg : 0 ≤ ∑ i : PaperHG2GreedySelection.Retained D0 A, (Real.exp (pressure i) + 1) :=
    Finset.sum_nonneg fun i _ => by positivity
  have hRbig1 : 1 ≤ Rbig := (le_max_right R 1).trans (le_add_of_nonneg_right sumNonneg)
  have hRbig : 0 < Rbig := zero_lt_one.trans_le hRbig1
  have hRR : R ≤ Rbig := (le_max_left R 1).trans (le_add_of_nonneg_right sumNonneg)
  have boundBig : ∀ x, Real.exp (φ x) ≤ Rbig := fun x => (bound x).trans hRR
  have hRP : ∀ i : PaperHG2GreedySelection.Retained D0 A, Real.exp (pressure i) + 1 ≤ Rbig :=
    fun i => (Finset.single_le_sum
      (f := fun i : PaperHG2GreedySelection.Retained D0 A => Real.exp (pressure i) + 1)
      (fun i _ => by positivity) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left (zero_le_one.trans (le_max_right R 1)))
  obtain ⟨sfB, familyB, equilibriumFamily, unique, gapsB⟩ :=
    families_large (D0 := D0) (g := g) (φ := φ) (A := A) (h := h) (strict := strict) (a := a)
      (P := P) (L := L) (productCalculus := productCalculus) (hw := hw) (R := Rbig) (hR := hRbig)
      (bound := boundBig) (hφ := hφ) weightCalculus coreAgreement localWeight hRbig1 hRP
  -- Rescale the families to the given normalizer.
  let sf := originalRegularity D0 g φ A h P L hw R hR bound rank
  have scale : ∀ ε x, (C ε).killedTransition x = ENNReal.ofReal (Rbig / R) •
      (ActualAnosovGlobalChains.original D0 h.toHG1 P L (fun x => Real.exp (φ x)) hw.measurable
        Rbig hRbig boundBig ε).killedTransition x := by
    intro ε x
    simp only [ActualAnosovGlobalChains.original, ActualOriginalGlobalChain.chain,
      Global.PositiveNoiseContinuation.chain, ActualOriginalGlobalChain.rawChain, NoiseKernel.chain]
    exact ChainNormalizationTransport.ofBoundedWeight_scale _ _ _ _ Rbig R hRbig hR boundBig bound x
  let family := FamiliesRescale.Families.rescale T A h.absorbing_open Λ ell D t terminal root
    (ActualAnosovGlobalChains.original D0 h.toHG1 P L (fun x => Real.exp (φ x)) hw.measurable
      Rbig hRbig boundBig) C sfB sf (Rbig / R) (div_pos hRbig hR) scale familyB
  have familyGaps : ∀ s, ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, LocalConclusions.NormalizedGapAt P L (K s)
      (Λ ((D).index (j s))) (layerCompact A Λ ell 0 D (j s)).measurableSet
      (fun x => Real.exp (φ x.val)) (hw.measurable.comp measurable_subtype_coe)
      R hR (fun x => bound x.val)
      (⟨family.closedProduct s ε, family.closedProduct_probability s ε⟩ : ProbabilityMeasure (K s)) ε := by
    intro s
    filter_upwards [gapsB s] with ε gap
    obtain ⟨he, hwin, gap⟩ := gap
    exact ⟨he, hwin, NormalizedGapRenormalization.restrictedNoise (L.law ε)
      (fun z : X × cube (ι := ι) ε => P.family ε z.2.val z.1) (P.raw_measurable ε he hwin)
      (K s) (layerCompact A Λ ell 0 D (j s)).measurableSet (fun x => Real.exp (φ x.val))
      (hw.measurable.comp measurable_subtype_coe) Rbig R hRbig hR (fun x => boundBig x.val)
      (fun x => bound x.val) _ _ gap⟩
  let geometry := (ActualHG2BasinGeometry.windowed D0 g A h
    (HG2.proved_retained_pressure_finiteness h) D (chosen).index
    strict P L openEndpoint φ hφ R hR bound).continued P.window_positive
  obtain ⟨δ₀, positive, clauses⟩ := DerivedHG2Conclusions.conditional_global_global T A
    h.absorbing_open Λ ell D t terminal root C sf family geometry
    (ActualHG2BasinGeometry.order_positive D0 g A h (HG2.proved_retained_pressure_finiteness h))
    P.constant P.constant_positive.le
    (ActualHG2BasinGeometry.continued_noise_bound D0 g A h
      (HG2.proved_retained_pressure_finiteness h) D (chosen).index
      strict P L openEndpoint φ hφ R hR bound)
  have source : ControlSubmersionSources (E := WithLp 2 (E × H)) (ι := ι ⊕ κ) σP :=
    canonical_controlSubmersionSources (volume : Measure (WithLp 2 (E × H)))
  have selectedLocal : ∀ q, ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      ∃ νU : ProbabilityMeasure (U q),
        (νU : Measure (U q)).map Subtype.val = (family.closedProduct q ε).map Subtype.val ∧
        (RestrictedLayerChain.chain (C ε) (U q) (hU q)).IsQuasiErgodic (νU : Measure (U q)) ∧
        {x : U q | x.val ∈ Λ ((D).index (j q))} ⊆ (νU : Measure (U q)).support ∧
        ∀ ζ : Measure (U q), (RestrictedLayerChain.chain (C ε) (U q) (hU q)).IsQuasiErgodic ζ →
          {x : U q | x.val ∈ Λ ((D).index (j q))} ⊆ ζ.support → ζ = (νU : Measure (U q)) := by
    intro q
    have smallP : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ε ≤ (FP).window :=
      mem_nhdsWithin_of_mem_nhds (eventually_le_nhds (FP).window_positive)
    have smallY : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ε ≤ a.noise.window :=
      mem_nhdsWithin_of_mem_nhds (eventually_le_nhds a.noise.window_positive)
    have smallFamily : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ε < family.window q 0 :=
      mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds (family.window_positive q 0))
    filter_upwards [familyGaps q, smallP, smallY, smallFamily] with ε gap hp hy hfam
    obtain ⟨he, hwin, gap⟩ := gap
    have null : σP (((K q) \ (U q)) ×ˢ (univ : Set Y)) = 0 :=
      (chosen).extra 0 (j q)
    have coreU : Λ ((D).index (j q)) ⊆ U q := by
      exact (basic_set_interior_stratum T A Λ ell 0 D
        (ActualHG2BasinGeometry.retained_separation D0 A strict) (j q)).trans interior_subset
    have support : {x : K q | x.val ∈ Λ ((D).index (j q))} ⊆
        (family.closedProduct q ε).support := by
      intro x hx
      have hs := family.core_support q 0 ε he hfam
      rw [family.base_product_identity q ε he hfam] at hs
      exact ComparedLocalQuasiErgodic.mem_support_of_mem_support_map (K q) _ x (hs hx)
    have actual : C ε = NoiseKernel.chain (L.law ε) (actualMap P ε)
        (actualMap_measurable P ε he hwin) Aᶜ h.absorbing_open.measurableSet.compl
        (fun x => Real.exp (φ x)) hw.measurable R hR bound :=
      ActualOriginalGlobalChain.chain_eq P L Aᶜ h.absorbing_open.measurableSet.compl
        (fun x => Real.exp (φ x)) hw.measurable R hR bound ε he hwin
    exact ProductSelectedStratumQuasiErgodic.identify FP L a.laws σP
      source ε he hp
      (actualMap P ε) (actualMap a.noise ε)
      (actualMap_measurable P ε he hwin) (actualMap_measurable a.noise ε he hy)
      (fun control z => by rw [ActualAnosovGlobalStabilization.Data.maps_family]; rfl)
      Aᶜ (K q) (U q) h.absorbing_open.measurableSet.compl
      (layerCompact A Λ ell 0 D (j q)).measurableSet (hU q)
      (closedLayer_subset_live T A h.absorbing_open Λ ell D (j q)) subset_closure
      null (Classical.choice a.nonempty) (fun x => Real.exp (φ x)) hw.measurable R hR bound
      (C ε) (sf ε he) actual (Λ ((D).index (j q)))
      (D0.basic ((D).index (j q)).val).nonempty coreU
      ⟨family.closedProduct q ε, family.closedProduct_probability q ε⟩ gap support
  have allSelected := Filter.eventually_all.mpr selectedLocal
  obtain ⟨r, hr, ball⟩ := Metric.mem_nhdsWithin_iff.mp allSelected
  let δlocal := Real.toNNReal r
  have positiveLocal : 0 < δlocal := Real.toNNReal_pos.mpr hr
  have near : ∀ ε : ℝ≥0, 0 < ε → ε < δlocal →
      ε ∈ Metric.ball (0 : ℝ≥0) r ∩ Ioi 0 := by
    intro ε he hsmall
    refine ⟨?_, he⟩
    change dist ε 0 < r
    simpa only [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg ε.coe_nonneg] using
      (show (ε : ℝ) < r from Real.lt_toNNReal_iff_coe_lt.mp hsmall)
  have localUntil := fun ε he hsmall => ball (near ε he hsmall)
  have reach := ActualHG2BasinGeometry.adapted_interval_reachable D0 g A h (HG2.proved_retained_pressure_finiteness h) D
    (chosen).index
  have finished := CompleteHG2Conclusion.conclude T A h.absorbing_open Λ ell D t terminal root
    C sf family ((WG).continued P.window_positive) positive clauses reach firstSelected
    (ActualHG2BasinGeometry.first_terminal_full D0 g A h (HG2.proved_retained_pressure_finiteness h))
  obtain ⟨δ, positiveδ, _leδ₀, _lewindow, nine, labelled, witness⟩ := finished
  have same : ∀ ε, ε ≤ P.window →
      DerivedHG2Conclusions.literalChain T A h.absorbing_open Λ ell D t terminal root C
        ((WG).continued P.window_positive) ε = WindowedHG2Application.literalProcess WG ε :=
    WindowedHG2Application.continued_literal_eq WG P.window_positive
  have originalNine := (nine.transfer_window P.window_positive same
    (fun ε he => congrArg (WG).maps (PositiveNoiseContinuation.scale_eq he))).transfer_window
      positiveLocal (fun _ _ => rfl) (fun _ _ => rfl)
  have originalLabel := (labelled.transfer_window P.window_positive same).transfer_window
    positiveLocal (fun _ _ => rfl)
  refine ⟨sf, family, equilibriumFamily, unique, min (min δ P.window) δlocal,
    lt_min (lt_min positiveδ P.window_positive) positiveLocal,
    (min_le_left _ _).trans (min_le_right _ _), originalNine, originalLabel, ?_, ?_⟩
  · intro ε he small
    have hδ : ε < δ := small.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hwindow : ε ≤ P.window := (small.trans_le ((min_le_left _ _).trans (min_le_right _ _))).le
    have ready := witness ε he hδ
    rw [same ε hwindow] at ready
    exact ready
  · intro ε he small window q
    obtain ⟨νU, mapped, qem, support, uniqueU⟩ :=
      localUntil ε he (small.trans_le (min_le_right _ _)) q
    have literalEq := LiteralNoiseLiveChain.actual_local_chain_eq_global_restriction
      (L.law ε) (actualMap P ε) (actualMap_measurable P ε he window) Aᶜ (U q)
      h.absorbing_open.measurableSet.compl (hU q)
      (subset_closure.trans (closedLayer_subset_live T A h.absorbing_open Λ ell D (j q)))
      (fun x => Real.exp (φ x)) hw.measurable R hR bound
    have actual : C ε = NoiseKernel.chain (L.law ε) (actualMap P ε)
        (actualMap_measurable P ε he window) Aᶜ h.absorbing_open.measurableSet.compl
        (fun x => Real.exp (φ x)) hw.measurable R hR bound :=
      ActualOriginalGlobalChain.chain_eq P L Aᶜ h.absorbing_open.measurableSet.compl
        (fun x => Real.exp (φ x)) hw.measurable R hR bound ε he window
    rw [← actual] at literalEq
    refine ⟨νU, mapped.trans ?_, ?_, support, ?_⟩
    · exact (congrArg (fun p : ProbabilityMeasure X => (p : Measure X))
        (liveLaw_map T A h.absorbing_open Λ ell D t terminal root C sf family q ε)).symm
    · rwa [literalEq]
    · intro ζ hζ hs
      rw [literalEq] at hζ
      exact uniqueU ζ hζ hs

end ConditionedStochasticStabilityHyperbolic.Paper.NativeProvedHG2
