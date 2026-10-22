module
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedHilbertProductSplitting
public import LeanShared.Dynamics.MixingDenseOrbit
public import LeanShared.Dynamics.HyperbolicHilbertProduct
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedLinearFractionalCalculus
public import ConditionedStochasticStabilityHyperbolic.Paper.ConstructedSaddleLocalSetup
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedRegularNoiseSmoothing
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedHyperbolicEquilibrium
public import LeanShared.Dynamics.EquilibriumExponentialWeight
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedHLProductVariational
public import ConditionedStochasticStabilityHyperbolic.Paper.LocalGapRetention
public import ConditionedStochasticStabilityHyperbolic.Paper.CanonicalStabilizedLocalRetention
public import ConditionedStochasticStabilityHyperbolic.Paper.PrescribedAdaptedLocalMetadata
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeStabilizedLocalStability
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeStabilizedLocalRetention
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeLocalOutcomeProducer

/-! Literal local stochastic stability and gap retention (thm:local, thm:qem-local), without any
original stable/unstable dimension hypothesis and without ordinary source records. The auxiliary
Anosov and the stabilizing product receive the native local outcome (carrier pair, leading
records, D07, physical sources, conjugations and the local consumer); their same-family gaps are
projected to the original process. -/
public noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 20000
open Set IsManifold MeasureTheory Bundle Filter
open scoped Manifold ContDiff NNReal Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.NativeStabilizedLocalLeading
open LeanShared HyperbolicBasicSet RegularNoise

variable {X : Type} {Y : Type} {E F UY UP AY AP IY IP ΩY ΩP : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [MeasurableSpace (WithLp 2 (E × F))] [BorelSpace (WithLp 2 (E × F))]
  [NormedAddCommGroup UY] [NormedSpace ℝ UY] [FiniteDimensional ℝ UY]
  [MeasurableSpace UY] [BorelSpace UY]
  [NormedAddCommGroup UP] [NormedSpace ℝ UP] [FiniteDimensional ℝ UP]
  [MeasurableSpace UP] [BorelSpace UP]
  [MetricSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [CompactSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [RiemannianBundle (fun y : Y => TangentSpace (𝓘(ℝ, F)) y)]
  [MetricSpace ΩY] [MetricSpace ΩP]
  {RY : IY → Type*} [∀i,NormedAddCommGroup (RY i)]
  [∀i,NormedSpace ℂ (RY i)] [∀i,CompleteSpace (RY i)]
  {RP : IP → Type*} [∀i,NormedAddCommGroup (RP i)]
  [∀i,NormedSpace ℂ (RP i)] [∀i,CompleteSpace (RP i)]
  {μY : Measure UY} [μY.IsAddHaarMeasure] {μP : Measure UP} [μP.IsAddHaarMeasure]
  {ι κ OY OP : Type*} [Fintype ι] [Fintype κ] [Fintype OY] [Fintype OP]
  {T : X ≃ₜ X} {g : X → ℝ} {Λ V : Set X}
  (h : HL (E := E) T g Λ V)
  (a : AuxiliaryAnosov (F := F) (Y := Y) (ι := κ) h.r)

local instance literalSaddleOrdinaryCharts : ChartedSpace (E × F) (X × Y) := productCharts
local instance literalSaddleOrdinaryManifold : IsManifold (𝓘(ℝ, E × F)) ∞ (X × Y) := productManifold
local instance literalSaddleProductCharts : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
@[expose] local instance literalSaddleProductManifold : IsManifold (𝓘(ℝ, WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
@[expose] local instance literalSaddleCompactUniv : CompactSpace (univ : Set Y) :=
  isCompact_iff_compactSpace.mp isCompact_univ
@[expose] local instance literalSaddleCompactClosure {M : Type*} [TopologicalSpace M]
    [T2Space M] [CompactSpace M] (W : Set M) : CompactSpace (closure W) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact

variable [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)]
  [IsContinuousRiemannianBundle E (TangentSpace (𝓘(ℝ,E)) : X → Type _)]
  [IsContinuousRiemannianBundle F (TangentSpace (𝓘(ℝ,F)) : Y → Type _)]
  [IsContinuousRiemannianBundle (WithLp 2 (E × F))
    (TangentSpace (𝓘(ℝ,WithLp 2 (E × F))) : X × Y → Type _)]
  (productCalculus : FractionalProductCalculus (E := E) (F := F) (X := X) (Y := Y) h.r)
  (weightCalculus : HilbertScalarProductRegularity (E := E) (F := F)
    (X := X) (Y := Y) (h.r - 1))
  (P : Maps (E := E) (ι := ι) T h.r) (L : Laws (ι := ι))
  (w : X → ℝ) (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x) (agree : EqOn w g Λ)
  (W : Set (X × Y)) (hW : IsOpen W) (coreW : Λ ×ˢ (univ : Set Y) ⊆ W)
  (within : W ⊆ V ×ˢ univ)
  (smoothProduct : ∀ ζ : X × Y → ℝ,
    ContMDiff (𝓘(ℝ, WithLp 2 (E × F))) (𝓘(ℝ)) ∞ ζ → tsupport ζ ⊆ W →
    FractionalManifoldRegularity.Regular (E := WithLp 2 (E × F)) (F := ℝ)
      (h.r - 1) (ζ * (fun z => w z.1)))

local notation "tangent" => HilbertProduct.of_factors h.basic.hyperbolic a.hl.basic.hyperbolic
  (h.map_regular.mdifferentiable h.regularity_gt_one.le)
  (h.inverse_regular.mdifferentiable h.regularity_gt_one.le)
  (a.hl.map_regular.mdifferentiable a.hl.regularity_gt_one.le)
  (a.hl.inverse_regular.mdifferentiable a.hl.regularity_gt_one.le)

local notation "outer" => ActualSaddleStabilization.outer h a productCalculus (proved_linearFractionalCalculus (T := T.prodCongr a.map) (LinearRechartedManifold.hilbertProductEquiv (A := E) (B := F)) h.r) weightCalculus tangent (h.mixing.exists_product_dense_orbit a.hl.mixing h.compact_core a.hl.compact_core h.nonempty_core a.hl.nonempty_core h.basic.hyperbolic.invariant a.hl.basic.hyperbolic.invariant)
local notation "setupY" => ConstructedSaddleLocalSetup.auxiliarySetup h a
local notation "setupP" => ConstructedSaddleLocalSetup.productSetup h a productCalculus (proved_linearFractionalCalculus (T := T.prodCongr a.map) (LinearRechartedManifold.hilbertProductEquiv (A := E) (B := F)) h.r) weightCalculus tangent (h.mixing.exists_product_dense_orbit a.hl.mixing h.compact_core a.hl.compact_core h.nonempty_core a.hl.nonempty_core h.basic.hyperbolic.invariant a.hl.basic.hyperbolic.invariant) w hw agree W hW coreW within smoothProduct
local notation "noiseY" => ActualSaddleStabilization.auxiliaryNoise h a
local notation "noiseP" => ConstructedSaddleLocalSetup.productNoise h a productCalculus (proved_linearFractionalCalculus (T := T.prodCongr a.map) (LinearRechartedManifold.hilbertProductEquiv (A := E) (B := F)) h.r) weightCalculus tangent (h.mixing.exists_product_dense_orbit a.hl.mixing h.compact_core a.hl.compact_core h.nonempty_core a.hl.nonempty_core h.basic.hyperbolic.invariant a.hl.basic.hyperbolic.invariant) w hw agree W hW coreW within smoothProduct P
local notation "original" => ActualSaddleStabilization.originalForAuxiliary h a P

include hw0 a productCalculus weightCalculus w hw agree W hW coreW within smoothProduct in
/-- Literal local stochastic stability and gap retention on `closure V` for the weight `exp φ`. -/
theorem stability_and_retention
    (φ : X → ℝ) (weight_exp : ∀ x : closure V, w x.val = Real.exp (φ x.val)) :
    ∃ (hwExp : Continuous (fun x : closure V => Real.exp (φ x.val)))
      (R : ℝ) (hR : 0 < R) (bound : ∀ x : closure V, Real.exp (φ x.val) ≤ R),
      LocalConclusions.Stability P L (closure V) Λ isClosed_closure.measurableSet
        (fun x => Real.exp (φ x.val)) hwExp.measurable R hR bound
        (fun x => φ x - Real.log (h.basic.hyperbolic.unstableJacobian x)) ∧
      LocalConclusions.GapRetention P L (closure V) Λ isClosed_closure.measurableSet
        (fun x => Real.exp (φ x.val)) hwExp.measurable R hR bound := by
  have splitting : ProductSplittingIdentification h.basic.hyperbolic
      a.hl.basic.hyperbolic tangent :=
    ProductSplittingIdentification.of_actual_product _ _ tangent
      (h.map_regular.mdifferentiable h.regularity_gt_one.le)
      (h.inverse_regular.mdifferentiable h.regularity_gt_one.le)
      (a.hl.map_regular.mdifferentiable a.hl.regularity_gt_one.le)
      (a.hl.inverse_regular.mdifferentiable a.hl.regularity_gt_one.le)
      ((outer).map_regular.mdifferentiable (outer).regularity_gt_one.le)
      ((outer).inverse_regular.mdifferentiable (outer).regularity_gt_one.le)
  have smoothSource (ε : ℝ≥0) (positive : 0 < ε) (window : ε ≤ P.window) :=
    proved_smoothCubeSubmersionContract (E := E) (M := X) (ι := ι)
      ε positive (fun z => P.family ε z.1 z.2)
      (P.joint_C1 ε positive window) (P.control_surjective ε positive window)
  have stable := ActualSaddleStabilization.stable_positive h a tangent splitting
  have hφ (x : X) (hx : x ∈ Λ) : g x = Real.exp (φ x) :=
    (agree hx).symm.trans (weight_exp ⟨x, subset_closure (h.basic.subset_neighborhood hx)⟩)
  let νeq := h.proved_equilibriumPackage.state
  have equilibrium := h.proved_equilibriumPackage.equilibrium_actual_phi φ hφ
  have unique := h.proved_equilibriumPackage.unique_actual_phi φ hφ
  -- The auxiliary outcome (weight one, potential zero, live state `univ`).
  have auxCore : isolatedCore a.map (univ : Set Y) = univ := by
    simpa only [closure_univ] using a.hl.actual_isolated_core.symm
  have hφY : ∀ y ∈ (univ : Set Y), ((setupY).cutoff * fun _ : Y => (1 : ℝ)) y = Real.exp ((fun _ : Y => 0) y) :=
    fun y hy => ((setupY).core_agreement hy).trans Real.exp_zero.symm
  obtain ⟨dY, dYmaps, dYlaws, -⟩ := NativeLocalOutcomeProducer.native_local_outcome a.hl
    (fun _ => 1) continuous_const (fun _ => zero_le_one) (setupY) univ isCompact_univ auxCore
    (subset_univ _) (fun y _ => by rw [(setupY).hyperbolic_eq]; exact a.stable_positive y)
    ((noiseY).changeRegularity (setupY).regularity_eq.symm) a.laws (fun _ => 0) hφY 0
  let cy := dY.transfer a.hl (setupY).regularity_eq
    (fun y => by rw [(setupY).hyperbolic_eq])
  -- The product outcome on the closed product live state.
  have hpTangent : (setupP).fresh.basic.hyperbolic = tangent := (setupP).hyperbolic_eq.trans rfl
  have productCore : isolatedCore (T.prodCongr a.map) (closure (V ×ˢ (univ : Set Y))) =
      Λ ×ˢ univ := by
    rw [closure_prod_eq, isolatedCore_product, ← h.actual_isolated_core,
      ← a.hl.actual_isolated_core]
  have hφP (z : X × Y) (hz : z ∈ Λ ×ˢ (univ : Set Y)) :
      ((setupP).cutoff * (fun z : X × Y => w z.1)) z = Real.exp (φ z.1) :=
    ((setupP).core_agreement hz).trans (by simpa only [mul_one] using hφ z.1 hz.1)
  obtain ⟨xw, -, maxw⟩ := isCompact_univ.exists_isMaxOn (h.nonempty_core.mono (subset_univ _)) hw.continuousOn
  obtain ⟨cp, cpMaps, cpLaws, cpFloor⟩ := NativeLocalOutcomeProducer.native_local_outcome (outer)
    (fun z : X × Y => w z.1) (hw.comp continuous_fst) (fun z => hw0 z.1) (setupP)
    (closure (V ×ˢ (univ : Set Y))) isClosed_closure.isCompact productCore
    (within.trans subset_closure) (fun z hz => by rw [hpTangent]; exact stable z hz) (noiseP)
    (productLaws L a.laws) (fun z => φ z.1) hφP (w xw)
  have bound (x : X) : w x ≤ cp.scale := (maxw (mem_univ x)).trans cpFloor
  have mapsMatch (ε : ℝ≥0) : cp.maps.family ε = independentFamily (original) cy.maps ε := by
    rw [cpMaps]
    funext control z
    rw [ConstructedSaddleLocalSetup.productNoise_family]
    simp only [independentFamily, cy, NativeLocalOutcome.transfer, dYmaps,
      Maps.changeRegularity_family]
  have lawsMatch (ε : ℝ≥0) : cp.laws.law ε = (productLaws L cy.laws).law ε := by
    rw [cpLaws]
    simp only [cy, NativeLocalOutcome.transfer, dYlaws]
  have smoothOriginal : ∀ ε (_hε : 0 < ε) (_hwindow : ε ≤ (original).window),
      ∀ q : Control (ι := ι) → ℝ, HasCompactSupport q → ContDiff ℝ ∞ q →
        ∀ f : X → ℝ, Measurable f → (∃ C ≥ 0, ∀x, ‖f x‖ ≤ C) →
          Continuous (fun x => ∫ z : cube (ι := ι) ε,
            q z.val * f ((original).family ε z.val x) ∂cubeVolume ε) := by
    intro ε hε hwindow q hq hs f hf hb
    have window : ε ≤ P.window := by
      rwa [ActualSaddleStabilization.originalForAuxiliary, Maps.changeRegularity_window] at hwindow
    simpa only [ActualSaddleStabilization.originalForAuxiliary, Maps.changeRegularity_family] using
      smoothSource ε hε window q hq hs f hf hb
  have productVariationalFresh : ∀ ζ : ProbabilityMeasure Y,
      ThermodynamicDefinitions.IsEquilibriumState a.map
        (fun y => (0 : ℝ) - Real.log (a.hl.basic.hyperbolic.unstableJacobian y)) univ ζ →
      ThermodynamicDefinitions.IsEquilibriumState (T.prodCongr a.map)
        (fun z => φ z.1 - Real.log ((setupP).fresh.basic.hyperbolic.unstableJacobian z))
        (Λ ×ˢ univ) (⟨(νeq : Measure X).prod (ζ : Measure Y), inferInstance⟩ : ProbabilityMeasure (X × Y)) := by
    intro ζ hζ
    rw [hpTangent]
    have hn : (1 : ℕ) ≤ ⌊h.r⌋₊ :=
      Nat.le_floor (by simpa only [Nat.cast_one] using h.regularity_gt_one.le)
    have forward : ContMDiff (𝓘(ℝ,WithLp 2 (E × F)))
        (𝓘(ℝ,WithLp 2 (E × F))) 1 (T.prodCongr a.map) :=
      (outer).map_regular.differentiable.of_le (by exact_mod_cast hn)
    have inverse : ContMDiff (𝓘(ℝ,WithLp 2 (E × F)))
        (𝓘(ℝ,WithLp 2 (E × F))) 1 (T.prodCongr a.map).symm :=
      (outer).inverse_regular.differentiable.of_le (by exact_mod_cast hn)
    exact h.product_variational_actual_phi a.hl tangent splitting
      (forward.mdifferentiable (by norm_num)) (inverse.mdifferentiable (by norm_num))
      φ hφ νeq ζ equilibrium hζ
  have result := NativeStabilizedLocalStability.stability
    (h := h) (a := a.hl) (hp := (setupP).fresh)
    (w := w) (hw := hw) (hw0 := hw0) (φP := fun z => φ z.1)
    cy cp (original) L bound mapsMatch lawsMatch smoothOriginal
    (fun x => φ x - Real.log (h.basic.hyperbolic.unstableJacobian x)) νeq
    equilibrium unique productVariationalFresh
  have retained := NativeStabilizedLocalRetention.retention
    (h := h) (a := a.hl) (hp := (setupP).fresh)
    (w := w) (hw := hw) (hw0 := hw0) (φP := fun z => φ z.1)
    cy cp (original) L bound mapsMatch lawsMatch smoothOriginal
  have retainedOriginal := (LocalConclusions.gapRetention_changeRegularity P L
    (closure V) Λ isClosed_closure.measurableSet (fun x => w x.val)
    (hw.measurable.comp measurable_subtype_coe) cp.scale cp.scale_positive
    (fun x => bound x.val) a.regularity.symm).mp retained
  have resultOriginal := (P.stability_changeRegularity a.regularity.symm L
    (closure V) Λ isClosed_closure.measurableSet (fun x => w x.val)
    (hw.measurable.comp measurable_subtype_coe) cp.scale cp.scale_positive (fun x => bound x.val)
    (fun x => φ x - Real.log (h.basic.hyperbolic.unstableJacobian x))).mp result
  have weight : (fun x : closure V => w x.val) = (fun x => Real.exp (φ x.val)) := funext weight_exp
  have hwExp : Continuous (fun x : closure V => Real.exp (φ x.val)) :=
    weight ▸ (hw.comp continuous_subtype_val)
  have boundExp (x : closure V) : Real.exp (φ x.val) ≤ cp.scale :=
    (weight_exp x).symm.trans_le (bound x.val)
  refine ⟨hwExp, cp.scale, cp.scale_positive, boundExp, ?_⟩
  simpa only [← weight] using (And.intro resultOriginal retainedOriginal)

end ConditionedStochasticStabilityHyperbolic.Paper.NativeStabilizedLocalLeading
