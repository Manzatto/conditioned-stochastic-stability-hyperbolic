module
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualAnosovGlobalChains
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualOriginalGlobalFiltration
public import ConditionedStochasticStabilityHyperbolic.Paper.HG1EquilibriumIdentification
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeAuxiliaryGapFamily
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeFiltrationPrefixSources
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeFiltrationLocal
public import ConditionedStochasticStabilityHyperbolic.Paper.ChainNormalizationTransport
public import ConditionedStochasticStabilityHyperbolic.Paper.CanonicalControlSubmersionSources
public import ConditionedStochasticStabilityHyperbolic.Paper.CompactMarginalEquilibrium
public import ConditionedStochasticStabilityHyperbolic.Global.StabilizedSinglePrefixApplication
public import ConditionedStochasticStabilityHyperbolic.Global.HG1FullPrefixFamilyConclusion
public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedGlobalCubeChain
import all ConditionedStochasticStabilityHyperbolic.Paper.ActualAnosovGlobalStabilization
import all ConditionedStochasticStabilityHyperbolic.Paper.ActualAnosovGlobalChains

/-! Original HG1 global existence and stability (thm:global-existence, thm:global). All product
geometry, native analytic packets of every closed layer, the native selected local outcome, gaps
and probability families are constructed; no source record, spectral radius, leading record or
auxiliary layer record is assumed. The physical weight `exp φ` equals `g` on the retained basic
sets and is locally regular near them (manuscript: `e^φ ∈ C^{r-1}` on every basic set). Every
analytic construction uses one large normalizer; the literal clauses are transported to the
given normalizer `R`. -/
public noncomputable section
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 20000
open Set Function Bundle MeasureTheory Filter IsManifold
open scoped Manifold ContDiff Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.NativeHG1Application
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
variable [IsContinuousRiemannianBundle E (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle F (fun y : Y => TangentSpace (𝓘(ℝ, F)) y)]
local instance hg1ActualSourceOrdinaryCharts : ChartedSpace (E × F) (X × Y) := productCharts
local instance hg1ActualSourceOrdinaryManifold : IsManifold (𝓘(ℝ, E × F)) ∞ (X × Y) := productManifold
local instance hg1ActualSourceHilbertCharts : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance hg1ActualSourceHilbertManifold : IsManifold (𝓘(ℝ, WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)]
  [IsContinuousRiemannianBundle (WithLp 2 (E × F))
    (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)]
  {T : X ≃ₜ X} (D : SpectralDecomposition (E := E) T) {g : X → ℝ} {A : Set X}
  (h : HG1 D g A) (a : AuxiliaryAnosov (F := F) (Y := Y) (ι := κ) h.r)

variable (P : Maps (E := E) (ι := ι) T h.r) (L : Laws (ι := ι))
  (productCalculus : FractionalProductCalculus (E := E) (F := F) (X := X) (Y := Y) h.r)
  (linearCalculus : LinearFractionalCalculus (T := T.prodCongr a.map)
    (LinearRechartedManifold.hilbertProductEquiv (A := E) (B := F)) h.r)

variable (φ : X → ℝ) (hw : Continuous (fun x => Real.exp (φ x)))
  (R : ℝ) (hR : 0 < R) (bound : ∀ x, Real.exp (φ x) ≤ R)
  {ℓ : ℕ} (retained : AdaptedSource T A D.core ℓ)
  (j : Fin ℓ) (selected : retained.index j = h.dominant)
  (pressure : Fin D.count → ℝ)
local notation "PF" => ActualAnosovGlobalStabilization.Data.maps D h a P productCalculus linearCalculus
local notation "PL" => productLaws L a.laws
set_option quotPrecheck false in
local notation "AP" => (A ×ˢ (univ : Set Y))
local notation "hAP" => h.absorbing_open.prod isOpen_univ
set_option quotPrecheck false in
local notation "LP" => (fun i => D.core i ×ˢ (univ : Set Y))
local notation "DP" => ProductAdaptedFiltration.source T a.map A D.core ℓ retained
set_option quotPrecheck false in
local notation "wP" => (fun z : X × Y => Real.exp (φ z.1))
local notation "hwP" => hw.comp continuous_fst
local notation "Q" i:max => closedLayer (T.prodCongr a.map) AP LP ℓ 0 DP i
local notation "hcQ" i:max => layerCompact AP LP ℓ 0 DP i
local notation "K" => closedLayer T A D.core ℓ 0 retained j
local instance productLayerCompact (i : Fin ℓ) : CompactSpace (Q i) :=
  isCompact_iff_compactSpace.mp (hcQ i)
local instance originalLayerCompact : CompactSpace (K) :=
  isCompact_iff_compactSpace.mp (layerCompact A D.core ℓ 0 retained j)
local instance auxiliaryUnivCompact : CompactSpace (univ : Set Y) :=
  isCompact_iff_compactSpace.mp isCompact_univ

include selected in
omit [CompactSpace X] [SecondCountableTopology X] [CompactSpace Y] [SecondCountableTopology Y]
  [BorelSpace X] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  [MeasurableSpace (WithLp 2 (E × F))] [BorelSpace (WithLp 2 (E × F))] [BorelSpace Y]
  [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)] in
omit [IsContinuousRiemannianBundle E (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle F (fun y : Y => TangentSpace (𝓘(ℝ, F)) y)] in
theorem productMixing : MixingOn (T.prodCongr a.map) (LP (retained.index j)) := by
  rw [selected]
  exact h.dominant_mixing.product a.hl.mixing

include productCalculus linearCalculus selected in
omit [MeasurableSpace E] [BorelSpace E] in
/-- Native thm:global-existence and thm:global on the original system, through the stabilizing
product with the auxiliary Anosov factor. -/
theorem conclusions_native
    (geometry : ActualAnosovGlobalStabilization.Data D h a)
    (pressure_identity : ∀ i : Fin ℓ, D.pressure g (retained.index i) =
      (pressure (retained.index i) : EReal))
    (coreWeight : ∀ i : Fin ℓ, EqOn g (fun x => Real.exp (φ x)) (D.core (retained.index i)))
    (localWeight : ∀ i : Fin ℓ, ∃ W : Set (X × Y), IsOpen W ∧
      D.core (retained.index i) ×ˢ (univ : Set Y) ⊆ W ∧
      ∀ ζ : X × Y → ℝ, ContMDiff (𝓘(ℝ, WithLp 2 (E × F))) (𝓘(ℝ)) ∞ ζ → tsupport ζ ⊆ W →
        FractionalManifoldRegularity.Regular (E := WithLp 2 (E × F)) (F := ℝ) (h.r - 1)
          (ζ * fun z : X × Y => Real.exp (φ z.1)))
    (strict : MapsTo T (closure A) A)
    (shifted_boundary_null : ∀ N i, 0 < i → i ≤ ℓ →
      (FiniteSmoothReferenceCharts.referenceMeasure (M := X × Y)
        (volume : Measure (WithLp 2 (E × F))))
        (frontier (levels (T.prodCongr a.map) AP LP ℓ N DP i)) = 0)
    (smoothOriginal : SmoothCubeSubmersionContract (E := E) (M := X) (ι := ι))
    (product_equilibrium : ThermodynamicDefinitions.IsEquilibriumState (T.prodCongr a.map)
      (fun z => φ z.1 - Real.log ((geometry.geometry.tangent (retained.index j)).unstableJacobian z))
      (LP (retained.index j))
      (⟨(h.deterministic_equilibrium.state : Measure X).prod (a.equilibrium.state : Measure Y),
        inferInstance⟩ : ProbabilityMeasure (X × Y))) :
    letI : CompactSpace ↥(Aᶜ) := isCompact_iff_compactSpace.mp h.absorbing_open.isClosed_compl.isCompact
    ∃ initial : ProbabilityMeasure ↥(Aᶜ), ∃ ν : ℝ≥0 → ProbabilityMeasure ↥(Aᶜ),
      (initial : Measure ↥(Aᶜ)).map Subtype.val = (h.deterministic_equilibrium.state : Measure X) ∧
      ThermodynamicDefinitions.IsEquilibriumState T
        (fun x => φ x - Real.log ((D.basic h.dominant).hyperbolic.unstableJacobian x))
        (D.core h.dominant) h.deterministic_equilibrium.state ∧
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
  classical
  let : CompactSpace ↥(Aᶜ) := isCompact_iff_compactSpace.mp h.absorbing_open.isClosed_compl.isCompact
  -- One large normalizer above the weight and every retained pressure.
  let Rbig : ℝ := max R 1 + ∑ i : Fin ℓ, (Real.exp (pressure (retained.index i)) + 1)
  have sumNonneg : 0 ≤ ∑ i : Fin ℓ, (Real.exp (pressure (retained.index i)) + 1) :=
    Finset.sum_nonneg fun i _ => by positivity
  have hRbig1 : 1 ≤ Rbig := (le_max_right R 1).trans (le_add_of_nonneg_right sumNonneg)
  have hRbig : 0 < Rbig := zero_lt_one.trans_le hRbig1
  have hRR : R ≤ Rbig := (le_max_left R 1).trans (le_add_of_nonneg_right sumNonneg)
  have boundBig : ∀ x, Real.exp (φ x) ≤ Rbig := fun x => (bound x).trans hRR
  have hRP : ∀ i : Fin ℓ, Real.exp (pressure (retained.index i)) + 1 ≤ Rbig := fun i =>
    (Finset.single_le_sum (f := fun i : Fin ℓ => Real.exp (pressure (retained.index i)) + 1)
      (fun i _ => by positivity) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left (zero_le_one.trans (le_max_right R 1)))
  have hφ : Continuous φ := by
    simpa only [Real.log_exp] using hw.log (fun x => (Real.exp_pos _).ne')
  let C₁ := ActualAnosovGlobalChains.original D h P L (fun x => Real.exp (φ x)) hw.measurable
    Rbig hRbig boundBig
  let CP₁ := ActualAnosovGlobalChains.stabilized D h a P L productCalculus linearCalculus
    (fun x => Real.exp (φ x)) hw.measurable Rbig hRbig boundBig
  let sf := ActualOriginalGlobalChain.strongFeller P L Aᶜ h.absorbing_open.measurableSet.compl
    (fun x => Real.exp (φ x)) hw.measurable Rbig hRbig boundBig hw (fun x => (Real.exp_pos _).le)
    (fun ε hε window => smoothOriginal ε hε (fun z => P.family ε z.1 z.2)
      (P.joint_C1 ε hε window) (P.control_surjective ε hε window))
  -- Product objects.
  let σP := FiniteSmoothReferenceCharts.referenceMeasure (M := X × Y)
    (volume : Measure (WithLp 2 (E × F)))
  have source : ControlSubmersionSources (E := WithLp 2 (E × F)) (ι := ι ⊕ κ) σP :=
    canonical_controlSubmersionSources (volume : Measure (WithLp 2 (E × F)))
  let sfP := ActualOriginalGlobalChain.strongFeller (PF) (PL) APᶜ (hAP).measurableSet.compl
    wP (hwP).measurable Rbig hRbig (fun z => boundBig z.1) hwP (fun z => (Real.exp_pos _).le)
    (fun ε hε window => source.smooth_density ε hε (fun z => (PF).family ε z.1 z.2)
      ((PF).joint_C1 ε hε window) ((PF).control_surjective ε hε window))
  let Dd := ActualAnosovGlobalStabilization.Data.decomposition D h a geometry
  have r1 : 1 < h.r := h.regularity_gt_one
  have auxRegular : FractionalManifoldRegularity.Regular (E := F) (F := F) h.r (a.map : Y → Y) := by
    simpa only [a.regularity] using a.hl.map_regular
  have auxInverse : FractionalManifoldRegularity.Regular (E := F) (F := F) h.r
      (a.map.symm : Y → Y) := by
    simpa only [a.regularity] using a.hl.inverse_regular
  have regP : FractionalManifoldRegularity.Regular (E := WithLp 2 (E × F)) (F := WithLp 2 (E × F))
      h.r (T.prodCongr a.map) :=
    geometry.map_calculus T a.map h.map_regular auxRegular
  have invP : FractionalManifoldRegularity.Regular (E := WithLp 2 (E × F)) (F := WithLp 2 (E × F))
      h.r (T.prodCongr a.map).symm :=
    geometry.map_calculus T.symm a.map.symm h.inverse_regular auxInverse
  let basicP : ∀ i : Fin ℓ, BasicData (E := WithLp 2 (E × F)) (T.prodCongr a.map)
      (LP ((DP).index i)) (Dd.collar (retained.index i)) := fun i => Dd.basic (retained.index i)
  have liveP : ∀ i : Fin ℓ, LP ((DP).index i) ⊆ APᶜ := fun i z hz hzA =>
    ActualHG1DominantOrdering.index_live T A D.core ℓ retained i hz.1 hzA.1
  have coreWeightP : ∀ i : Fin ℓ, EqOn (fun z : X × Y => g z.1) wP (LP ((DP).index i)) :=
    fun i z hz => coreWeight i hz.1
  have stableP : ∀ i : Fin ℓ, ∀ z ∈ LP ((DP).index i),
      0 < Module.finrank ℝ ((basicP i).hyperbolic.stable z) := fun i =>
    ActualAnosovGlobalStabilization.Data.stable_positive D h a geometry (retained.index i)
  have pressureP : ∀ i : Fin ℓ, ThermodynamicDefinitions.pressure (T.prodCongr a.map)
      ((basicP i).hyperbolic.potential (fun z : X × Y => g z.1)) (LP ((DP).index i)) =
      (pressure ((DP).index i) : EReal) := fun i =>
    (geometry.pressure D h a (retained.index i)
      (ActualHG1DominantOrdering.index_live T A D.core ℓ retained i)).trans (pressure_identity i)
  let pG := MapImage.representation (PF) h.regularity_gt_one.le (PF).window le_rfl
    (PF).window_positive
  let terminal : Fin 1 → Fin ℓ := fun _ => ⟨ℓ - 1, by have hj := j.isLt; omega⟩
  let roots : ∀ s, Fin ((terminal s).val + 1) := fun _ => ⟨j.val, by have hj := j.isLt; dsimp [terminal]; omega⟩
  have rootIndex : selectedIndex ℓ 1 terminal roots 0 = j := Fin.ext rfl
  -- The native selected local outcome.
  obtain ⟨g', V', h', hyperbolic, dl, mapsEq, windowEq, lawsEq, -⟩ :=
    NativeFiltrationLocal.exists_local_outcome LP AP hAP
      (ProductAdaptedFiltration.strict_trapping T a.map A strict) 0 DP basicP liveP r1 regP invP
      (fun z : X × Y => φ z.1) (hφ.comp continuous_fst) j (localWeight j) (stableP j)
      (productMixing D h a retained j selected) (PF) (PL) 0
  let fd := dl.family
  have productEq : ThermodynamicDefinitions.IsEquilibriumState (T.prodCongr a.map)
      (fun z => φ z.1 - Real.log (h'.basic.hyperbolic.unstableJacobian z))
      (LP (retained.index j))
      (⟨(h.deterministic_equilibrium.state : Measure X).prod (a.equilibrium.state : Measure Y),
        inferInstance⟩ : ProbabilityMeasure (X × Y)) := by
    rw [hyperbolic]
    exact product_equilibrium
  obtain ⟨ν₀, ν, limit, mapped, marginal⟩ := CompactMarginalEquilibrium.from_generated_family
    (K) (Q j) (ProductAdaptedFiltration.closedLayer_product T a.map A D.core ℓ retained 0 j)
    T a.map (fun z => φ z.1 - Real.log (h'.basic.hyperbolic.unstableJacobian z))
    (LP (retained.index j)) fd.probability fd.initialLimit fd.equilibrium
    fd.limit fd.map_limit fd.equilibrium_unique h.deterministic_equilibrium.state
    a.equilibrium.state productEq
  -- The native prefix sources at the large normalizer.
  have same : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, CP₁ ε =
      NoiseKernel.chain ((PL).fixedLaw ε)
        (fun z : (X × Y) × RegularNoise.FixedControl (ι := ι ⊕ κ) =>
          MapImage.maps (PF) h.regularity_gt_one.le (PF).window le_rfl (pG.fixedParameters ε z.2) z.1)
        (pG.allScale_measurable ε) APᶜ (hAP).measurableSet.compl wP (hwP).measurable Rbig
        (zero_lt_one.trans_le hRbig1) (fun z => boundBig z.1) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds pG.window_positive)] with ε hε window
    have exactRaw := ActualOriginalGlobalChain.chain_eq (PF) (PL) APᶜ (hAP).measurableSet.compl
      wP (hwP).measurable Rbig hRbig (fun z => boundBig z.1) ε hε (window.le.trans pG.window_le)
    exact exactRaw.trans (pG.global_chain_literal_cube (PL) ε hε window.le
      APᶜ (hAP).measurableSet.compl wP (hwP).measurable Rbig hRbig (fun z => boundBig z.1)).symm
  have pGap := HG1EquilibriumIdentification.real_pressure_gap D h retained j selected pressure pressure_identity
  let prepared := NativeFiltrationPrefixSources.prefixSources LP (fun z : X × Y => g z.1) AP hAP
    (ProductAdaptedFiltration.strict_trapping T a.map A strict) 0 DP basicP liveP r1 regP invP wP hwP
    (fun z => Real.exp_pos _) coreWeightP localWeight stableP pressure pressureP (PF) (PL) Rbig
    hRbig1 hRP (fun z => boundBig z.1) pG σP source source.smooth_density
    ((terminal 0).val + 1) (by have hj := j.isLt; dsimp [terminal]; omega)
    (selectedIndex ℓ 1 terminal roots 0) (roots 0).isLt
    (by rw [rootIndex]; exact productMixing D h a retained j selected)
    (by
      rw [rootIndex]
      change EquilibriumPackage (Dd.basic (retained.index j)).hyperbolic (fun z : X × Y => g z.1)
      rw [selected]
      exact geometry.equilibrium)
    (fun i _hi different => pGap i (rootIndex ▸ different))
    shifted_boundary_null CP₁ same
  have actual := ActualAnosovGlobalChains.actual_pair D h a P L productCalculus linearCalculus
    (fun x => Real.exp (φ x)) hw.measurable Rbig hRbig boundBig
  have invariant := ActualOriginalGlobalChain.eventually_all_levels P L 0 A h.absorbing_open strict
    retained.levels ℓ retained.compact_positive retained.adapted_positive
    (fun x => Real.exp (φ x)) hw.measurable Rbig hRbig boundBig
  have smallWindow : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ε ≤ min P.window a.noise.window :=
    mem_nhdsWithin_of_mem_nhds (eventually_le_nhds (lt_min P.window_positive a.noise.window_positive))
  have familyWindow : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ε ≤ fd.window :=
    mem_nhdsWithin_of_mem_nhds (eventually_le_nhds fd.window_positive)
  have localUnique : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ _hε : 0 < ε,
      ∀ ζ : Measure (Q j),
        (RestrictedLayerChain.chain (CP₁ ε) (Q j) (hcQ j).measurableSet).IsQuasiErgodic ζ →
        {x | x.val ∈ LP (retained.index j)} ⊆ ζ.support → ζ = (fd.probability ε : Measure _) := by
    filter_upwards [familyWindow, actual, smallWindow] with ε hfw ha hwin
    intro hε ζ hζ hs
    have hεP : ε ≤ (PF).window := by
      have := hfw.trans fd.window_bound
      rwa [windowEq] at this
    have rawEq : CP₁ ε = NoiseKernel.chain ((PL).law ε)
        (fun z : (X × Y) × cube (ι := ι ⊕ κ) ε => (PF).family ε z.2.val z.1)
        ((PF).raw_measurable ε hε hεP) APᶜ (hAP).measurableSet.compl wP (hwP).measurable Rbig
        hRbig (fun z => boundBig z.1) := by
      apply (ha hε hwin).2.trans
      congr 1
    have localEq := LiteralNoiseLiveChain.actual_local_chain_eq_global_restriction
      ((PL).law ε)
      (fun z : (X × Y) × cube (ι := ι ⊕ κ) ε => (PF).family ε z.2.val z.1)
      ((PF).raw_measurable ε hε hεP) APᶜ (Q j) (hAP).measurableSet.compl (hcQ j).measurableSet
      (closedLayer_subset_live (T.prodCongr a.map) AP hAP LP ℓ DP j)
      wP (hwP).measurable Rbig hRbig (fun z => boundBig z.1)
    have qemBig : (RestrictedNoise.chain ((PL).law ε)
        (fun z : (X × Y) × cube (ι := ι ⊕ κ) ε => (PF).family ε z.2.val z.1)
        ((PF).raw_measurable ε hε hεP) (Q j) (hcQ j).measurableSet (fun x => wP x.val)
        ((hwP).measurable.comp measurable_subtype_coe) Rbig hRbig
        (fun x => boundBig x.val.1)).IsQuasiErgodic ζ := by
      rw [localEq, ← rawEq]
      exact hζ
    have qemScale := ChainNormalizationTransport.isQuasiErgodic
      (RestrictedNoise.liveKernel ((PL).law ε)
        (fun z : (X × Y) × cube (ι := ι ⊕ κ) ε => (PF).family ε z.2.val z.1)
        ((PF).raw_measurable ε hε hεP) (Q j) (hcQ j).measurableSet)
      (fun x => wP x.val) ((hwP).measurable.comp measurable_subtype_coe)
      (fun x => (Real.exp_pos _).le)
      (RestrictedNoise.liveKernel_mass_le_one _ _ _ _ _) Rbig dl.scale hRbig dl.scale_positive
      (fun x => boundBig x.val.1) fd.weight_bound ζ qemBig
    have point := fd.point ε hε hfw
    have sameMap : ∀ (G : (X × Y) × cube (ι := ι ⊕ κ) ε → X × Y) (hG : Measurable G),
        G = (fun z : (X × Y) × cube (ι := ι ⊕ κ) ε => (PF).family ε z.2.val z.1) →
        RestrictedNoise.chain (dl.laws.law ε) G hG (Q j) (hcQ j).measurableSet
          (fun x => wP x.val) fd.weight_continuous.measurable dl.scale dl.scale_positive
          fd.weight_bound =
        RestrictedNoise.chain ((PL).law ε)
          (fun z : (X × Y) × cube (ι := ι ⊕ κ) ε => (PF).family ε z.2.val z.1)
          ((PF).raw_measurable ε hε hεP) (Q j) (hcQ j).measurableSet (fun x => wP x.val)
          ((hwP).measurable.comp measurable_subtype_coe) dl.scale dl.scale_positive
          fd.weight_bound := by
      intro G hG e
      subst e
      rw [lawsEq]
    have chainEq := sameMap _ (dl.maps.raw_measurable ε hε (hfw.trans fd.window_bound))
      (funext fun z => mapsEq ε z.2.val z.1)
    exact point.2.2.1 ζ (chainEq ▸ qemScale) hs
  let familyP := fun (_q : Fin 1) ε => fd.probability ε
  let family := fun (_q : Fin 1) ε => ν ε
  have produced : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ hε : 0 < ε,
      Nonempty (At (T.prodCongr a.map) AP hAP LP ℓ DP 1 terminal roots CP₁ sfP
        (fun q ε => (familyP q ε : Measure _)) 0 0 ε hε) := by
    obtain ⟨_outputs, event⟩ := prepared.sources.produce
    filter_upwards [event, prepared.sources.hnoUp, localUnique] with ε hp hn hu
    intro hε
    obtain ⟨sfε, dg, _hq, hsupp, hpos, dc, _hrate, μ, hμ, hm, hproduct⟩ := hp
    have hsfeq : sfε = sfP ε hε := Subsingleton.elim _ _
    subst sfε
    let : IsFiniteMeasure μ := hμ
    apply at_of_actual_produced_pair (T.prodCongr a.map) AP hAP LP ℓ DP 1 terminal roots CP₁ sfP
      (fun q ε => (familyP q ε : Measure _)) 0 0 ε hε dg
      (hn hε ((terminal 0).val + 1) le_rfl) hpos hsupp prepared.sources.R prepared.sources.hR dc μ hm hproduct
    intro _hN ζ hζ hs
    rw [hu hε ζ hζ hs]
  obtain ⟨νY, eventY⟩ := NativeAuxiliaryGapFamily.exists_family_native a
  have auxiliary : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ (hε : 0 < ε)
      (hwindow : ε ≤ min P.window a.noise.window), ∃ ζ : ProbabilityMeasure (univ : Set Y),
      LocalConclusions.NormalizedGap
        (ActualCompactNoiseGap.auxiliaryLocal P a.noise a.laws ε hε hwindow 1 le_rfl) univ ζ := by
    filter_upwards [eventY] with ε output
    obtain ⟨hεY, windowY, gapY⟩ := output
    intro hε hwindow
    exact ⟨νY ε, gapY⟩
  have invariantPrefix : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ _hε : 0 < ε,
      ∀ x ∈ actualPrefix T A D.core ℓ retained (terminal 0) 0,
        (C₁ ε).killedTransition x (actualPrefix T A D.core ℓ retained (terminal 0) 0)ᶜ = 0 := by
    filter_upwards [invariant] with ε hi
    intro _hε
    exact hi ((terminal 0).val + 1) (by have hj := j.isLt; dsimp [terminal]; omega)
  have weakAmbient := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous ν ν₀ limit
    (continuous_subtype_val : Continuous (Subtype.val : K → X))
  have mapProbability : ν₀.map (Subtype.val : K → X) = h.deterministic_equilibrium.state :=
    ProbabilityMeasure.toMeasure_injective mapped
  have originalAt := StabilizedSinglePrefixApplication.same_family
    T a.map A h.absorbing_open D.core ℓ retained 1 terminal roots P a.noise L a.laws
    (fun x => Real.exp (φ x)) hw.measurable Rbig hRbig boundBig (fun x => (Real.exp_pos _).le)
    C₁ sf CP₁ sfP family (fun q ε => (familyP q ε : Measure _)) 0
    h.deterministic_equilibrium.state (mapProbability ▸ weakAmbient) produced actual auxiliary invariantPrefix
    (ActualHG1DominantOrdering.index_live T A D.core ℓ retained _) marginal
    (Classical.choice a.nonempty)
  obtain ⟨_ambient, _weak, _qem, atOriginal⟩ := originalAt
  have full : actualPrefix T A D.core ℓ retained (terminal 0) 0 = univ := by
    have size : (terminal 0).val + 1 = ℓ := by have hj := j.isLt; dsimp [terminal]; omega
    change levels T A D.core ℓ 0 retained ((terminal 0).val + 1) = univ
    rw [size, levels, shiftedFiltration_pos T 0 A retained.levels (by have hj := j.isLt; omega)]
    simpa only [Function.iterate_zero, id_eq, preimage_id_eq] using retained.terminal
  have zeroA : ∀ ε, 0 < ε → ∀ x, (C₁ ε).killedTransition x A = 0 := by
    intro ε _hε x
    let δ := min ε P.window
    let : IsProbabilityMeasure (L.law δ) := L.probability δ
    exact ActualAbsorbingKernelSupport.target_absorbing_mass_zero (L.law δ)
      (ActualOriginalGlobalChain.rawMap P δ) (ActualOriginalGlobalChain.rawMap_measurable P δ)
      A h.absorbing_open.measurableSet (fun x => Real.exp (φ x)) hw.measurable Rbig hRbig boundBig x
  obtain ⟨initial, probability, initialMap, weak, package⟩ := HG1FullPrefixFamilyConclusion.conclude
    T A h.absorbing_open D.core ℓ retained 1 terminal roots C₁ sf family 0 ν₀
    h.deterministic_equilibrium.state limit mapped full (D.basic (retained.index j)).nonempty
    zeroA atOriginal Rbig hRbig
  refine ⟨initial, probability, initialMap, HG1EquilibriumIdentification.equilibrium D h φ
    (selected ▸ coreWeight j), weak, ?_⟩
  filter_upwards [package] with ε point
  intro hε window
  have raw := ActualOriginalGlobalChain.chain_eq P L Aᶜ h.absorbing_open.measurableSet.compl
    (fun x => Real.exp (φ x)) hw.measurable Rbig hRbig boundBig ε hε window
  let : IsProbabilityMeasure (L.law ε) := L.probability ε
  have liveEq := LiteralNoiseLiveChain.actual_local_chain_eq_global_restriction (L.law ε)
    (fun z : X × cube (ι := ι) ε => P.family ε z.2.val z.1)
    (P.raw_measurable ε hε window) Aᶜ Aᶜ h.absorbing_open.measurableSet.compl
    h.absorbing_open.measurableSet.compl Subset.rfl (fun x => Real.exp (φ x)) hw.measurable Rbig
    hRbig boundBig
  have source := point hε
  have coreEq : D.core (retained.index (selectedIndex ℓ 1 terminal roots 0)) = D.core h.dominant := by
    rw [rootIndex, selected]
  rw [coreEq] at source
  dsimp only [C₁, ActualAnosovGlobalChains.original] at source
  rw [raw, ← liveEq] at source
  obtain ⟨gap, qem, support, unique, ⟨witness⟩⟩ := source
  have kernelMass := RestrictedNoise.liveKernel_mass_le_one (L.law ε)
    (fun z : X × cube (ι := ι) ε => P.family ε z.2.val z.1)
    (P.raw_measurable ε hε window) Aᶜ h.absorbing_open.measurableSet.compl
  refine ⟨NormalizedGapRenormalization.restrictedNoise (L.law ε)
      (fun z : X × cube (ι := ι) ε => P.family ε z.2.val z.1)
      (P.raw_measurable ε hε window) Aᶜ h.absorbing_open.measurableSet.compl
      (fun x => Real.exp (φ x.val)) (hw.comp continuous_subtype_val).measurable Rbig R hRbig hR
      (fun x => boundBig x.val) (fun x => bound x.val) _ _ gap,
    ChainNormalizationTransport.restrictedNoise_isQuasiErgodic (L.law ε)
      (fun z : X × cube (ι := ι) ε => P.family ε z.2.val z.1)
      (P.raw_measurable ε hε window) Aᶜ h.absorbing_open.measurableSet.compl
      (fun x => Real.exp (φ x.val)) (hw.comp continuous_subtype_val).measurable
      (fun x => (Real.exp_pos _).le) Rbig R hRbig hR (fun x => boundBig x.val)
      (fun x => bound x.val) _ qem,
    support, fun ζ hζ hs => unique ζ (ChainNormalizationTransport.restrictedNoise_isQuasiErgodic
      (L.law ε) (fun z : X × cube (ι := ι) ε => P.family ε z.2.val z.1)
      (P.raw_measurable ε hε window) Aᶜ h.absorbing_open.measurableSet.compl
      (fun x => Real.exp (φ x.val)) (hw.comp continuous_subtype_val).measurable
      (fun x => (Real.exp_pos _).le) R Rbig hR hRbig (fun x => bound x.val)
      (fun x => boundBig x.val) ζ hζ) hs,
    ⟨ChainNormalizationTransport.restrictedNoise_witness (L.law ε)
      (fun z : X × cube (ι := ι) ε => P.family ε z.2.val z.1)
      (P.raw_measurable ε hε window) Aᶜ h.absorbing_open.measurableSet.compl
      (fun x => Real.exp (φ x.val)) (hw.comp continuous_subtype_val).measurable Rbig R hRbig hR
      (fun x => boundBig x.val) (fun x => bound x.val) _ witness⟩⟩

end ConditionedStochasticStabilityHyperbolic.Paper.NativeHG1Application
