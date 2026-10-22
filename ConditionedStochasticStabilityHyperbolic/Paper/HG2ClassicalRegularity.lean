module

public import ConditionedStochasticStabilityHyperbolic.Paper.ActualAnosovGlobalChains
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualOriginalGlobalFiltration
public import ConditionedStochasticStabilityHyperbolic.Paper.SmoothSubmersionSource
public import ConditionedStochasticStabilityHyperbolic.Paper.ProductRegularNoiseMaps

/-! Strong Feller regularity of the actual original and stabilized global chains in the literal
nonvanishing HG2 branch, an ordinary rank-chart consequence. -/
public noncomputable section
set_option maxHeartbeats 3200000
open Set MeasureTheory IsManifold Bundle Filter Function
open scoped Manifold ContDiff NNReal Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.HG2ClassicalGlobalStability
open LeanShared HyperbolicBasicSet Global ShiftedFiltrationGeometry ActualFiltrationGrowth
open DerivedHG2Application FiltrationPressureConfinement
open RegularNoise ActualProductRestrictedChain
open LeanShared.ControlledPlaqueClosure
attribute [local instance] Classical.propDecidable
variable {X Y E H ι κ : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace H] [BorelSpace H]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [ChartedSpace H Y] [IsManifold (𝓘(ℝ, H)) ∞ Y]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
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
variable (a : AuxiliaryAnosov (F := H) (Y := Y) (ι := κ) h.r)
  (P : Maps (E := E) (ι := ι) T h.r) (L : Laws (ι := ι))
  (productCalculus : FractionalProductCalculus (E := E) (F := H) (X := X) (Y := Y) h.r)
  (linearCalculus : LinearFractionalCalculus (T := T.prodCongr a.map)
    (LinearRechartedManifold.hilbertProductEquiv (A := E) (B := H)) h.r)
  (σP : Measure (X × Y)) [IsFiniteMeasure σP] [σP.IsOpenPosMeasure]
  (σY : Measure Y) [IsFiniteMeasure σY] [σY.IsOpenPosMeasure]
  (hw : Continuous (fun x => Real.exp (φ x)))
  (R : ℝ) (hR : 0 < R) (bound : ∀ x, Real.exp (φ x) ≤ R)
set_option quotPrecheck false in
local notation "FP" => ActualAnosovGlobalStabilization.Data.maps D0 h.toHG1 a P productCalculus linearCalculus
set_option quotPrecheck false in
local notation "C" => ActualAnosovGlobalChains.original D0 h.toHG1 P L
  (fun x => Real.exp (φ x)) hw.measurable R hR bound
set_option quotPrecheck false in
local notation "CP" => ActualAnosovGlobalChains.stabilized D0 h.toHG1 a P L productCalculus linearCalculus
  (fun x => Real.exp (φ x)) hw.measurable R hR bound
set_option quotPrecheck false in
local notation "AP" => (A ×ˢ (univ : Set Y))
set_option quotPrecheck false in
local notation "hAP" => h.absorbing_open.prod isOpen_univ
set_option quotPrecheck false in
local notation "wP" => (fun z : X × Y => Real.exp (φ z.1))
set_option quotPrecheck false in
local notation "hwP" => hw.comp continuous_fst

/- The actual chains' regularity is an ordinary rank-chart consequence. -/
omit [MeasurableSpace E] [BorelSpace E] [CompactSpace X] [SecondCountableTopology X] in
theorem originalRegularity
    (rank : SmoothCubeSubmersionContract (E := E) (M := X) (ι := ι)) :
    ∀ ε, 0 < ε → HasStrongFellerKernel (C ε) :=
  ActualOriginalGlobalChain.strongFeller P L Aᶜ h.absorbing_open.measurableSet.compl
    (fun x => Real.exp (φ x)) hw.measurable R hR bound hw
    (fun _ => (Real.exp_pos _).le)
    (fun ε he hew => rank ε he (fun z => P.family ε z.1 z.2)
      (P.joint_C1 ε he hew) (P.control_surjective ε he hew))

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace H] [BorelSpace H]
  [CompactSpace X] [SecondCountableTopology X] [CompactSpace Y]
  [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × H))) z)] in
theorem productRegularity
    (rank : SmoothCubeSubmersionContract (E := WithLp 2 (E × H))
      (M := X × Y) (ι := ι ⊕ κ)) :
    ∀ ε, 0 < ε → HasStrongFellerKernel (CP ε) :=
  ActualOriginalGlobalChain.strongFeller FP (productLaws L a.laws) APᶜ (hAP).measurableSet.compl
    wP (hwP).measurable R hR (fun z => bound z.1) hwP
    (fun _ => (Real.exp_pos _).le)
    (fun ε he hew => rank ε he (fun z => (FP).family ε z.1 z.2)
      ((FP).joint_C1 ε he hew) ((FP).control_surjective ε he hew))

end ConditionedStochasticStabilityHyperbolic.Paper.HG2ClassicalGlobalStability
