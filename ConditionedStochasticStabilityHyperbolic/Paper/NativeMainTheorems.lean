module
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeLocalTheorem
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeProvedHG1
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeProvedHG2
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedHilbertScalarProductRegularity
public import ConditionedStochasticStabilityHyperbolic.Paper.ConcreteToralAuxiliaryAnosov
public import ConditionedStochasticStabilityHyperbolic.Paper.ConcreteToralHLProduct
public import ConditionedStochasticStabilityHyperbolic.Paper.ProductWhitneyBound

/-! Native global main theorems on the original system (thm:global-existence, thm:global).
The auxiliary Anosov factor is the concrete toral cat map, and the product and first-projection
calculi are the proved ones, so the hypotheses are those of the manuscript: the deterministic,
noise and weight data, and the local regularity of the physical weight near the retained basic
sets. The local theorems (thm:qem-local, thm:local) are
`NativeLocalTheorem.stability_and_retention`. -/

public noncomputable section
set_option maxHeartbeats 3200000
open Set Function Bundle MeasureTheory Filter IsManifold
open scoped Manifold ContDiff Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.NativeMainTheorems
open LeanShared HyperbolicBasicSet RegularNoise

variable {E ι : Type*} {X : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace X] [CompactSpace X] [SecondCountableTopology X] [ChartedSpace E X]
  [IsManifold (𝓘(ℝ, E)) ∞ X]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  {T : X ≃ₜ X} (D : SpectralDecomposition (E := E) T) {g : X → ℝ} {A : Set X}

local instance mainOrdinaryCharts : ChartedSpace (E × ToralCatMap.Model) (X × ToralCatMap.Torus) :=
  prodChartedSpace E X ToralCatMap.Model ToralCatMap.Torus
local instance mainProductCharts :
    ChartedSpace (WithLp 2 (E × ToralCatMap.Model)) (X × ToralCatMap.Torus) :=
  LinearRechartedManifold.productCharts
local instance mainProductManifold :
    IsManifold (𝓘(ℝ, WithLp 2 (E × ToralCatMap.Model))) ∞ (X × ToralCatMap.Torus) :=
  LinearRechartedManifold.product_manifold

local instance mainWithLpMeasurable : MeasurableSpace (WithLp 2 (E × ToralCatMap.Model)) := borel _
local instance mainWithLpBorel : BorelSpace (WithLp 2 (E × ToralCatMap.Model)) := ⟨rfl⟩
local instance mainProductBundle : RiemannianBundle (fun z : X × ToralCatMap.Torus =>
    TangentSpace (𝓘(ℝ, WithLp 2 (E × ToralCatMap.Model))) z) :=
  ConcreteToralHLProduct.bundle
local instance mainProductContinuous : IsContinuousRiemannianBundle (WithLp 2 (E × ToralCatMap.Model))
    (fun z : X × ToralCatMap.Torus => TangentSpace (𝓘(ℝ, WithLp 2 (E × ToralCatMap.Model))) z) :=
  SmoothMetricBundleClasses.continuous (ConcreteToralHLProduct.metric (E := E) (X := X))

omit [MeasurableSpace E] [BorelSpace E] in
/-- Native thm:global-existence and thm:global on the original system. -/
theorem global_existence (h : HG1 D g A) (P : Maps (E := E) (ι := ι) T h.r)
    (L : Laws (ι := ι)) (φ : X → ℝ) (hw : Continuous (fun x => Real.exp (φ x)))
    (R : ℝ) (hR : 0 < R) (bound : ∀ x, Real.exp (φ x) ≤ R)
    (strict : MapsTo T (closure A) A)
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
  exact NativeProvedHG1.conclusions_native D h (ToralCatMap.auxiliary h.r h.regularity_gt_one) P L
    (proved_fractionalProductCalculus h.r) φ hw R hR bound strict
    (proved_hilbertFirstProjectionRegularity (h.r - 1)) coreAgreement localWeightX

/-- Native thm:global-global on the original system: the HG2 conclusions for any normalizer of
the physical weight, with the prescribed greedy filtration. -/
theorem global_global (D0 : SpectralDecomposition (E := E) T) (g φ : X → ℝ) (A : Set X)
    (h : HG2 D0 g A) (strict : MapsTo T (closure A) A) (P : Maps (E := E) (ι := ι) T h.r)
    (L : Laws (ι := ι)) (hw : Continuous (fun x => Real.exp (φ x)))
    (R : ℝ) (hR : 0 < R) (bound : ∀ x, Real.exp (φ x) ≤ R) (hφ : Measurable φ)
    (coreAgreement : ∀ i, D0.core i ⊆ Aᶜ → EqOn (fun x => Real.exp (φ x)) g (D0.core i))
    (localWeightX : ∀ i, D0.core i ⊆ Aᶜ → ∃ W : Set X, IsOpen W ∧ D0.core i ⊆ W ∧
      ∀ ζ : X → ℝ, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ ζ → tsupport ζ ⊆ W →
        FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (h.r - 1)
          (ζ * fun x => Real.exp (φ x))) :
    type_of% (NativeProvedHG2.complete_with_local_strata_native (Y := ToralCatMap.Torus)
      (H := ToralCatMap.Model) (D0 := D0) (g := g) (φ := φ) (A := A) (h := h) (strict := strict)
      (a := ToralCatMap.auxiliary h.r h.regularity_gt_one) (P := P) (L := L)
      (productCalculus := proved_fractionalProductCalculus h.r) (hw := hw) (R := R) (hR := hR)
      (bound := bound) (hφ := hφ)
      (proved_hilbertFirstProjectionRegularity (h.r - 1)) coreAgreement localWeightX) :=
  NativeProvedHG2.complete_with_local_strata_native (Y := ToralCatMap.Torus)
    (H := ToralCatMap.Model) (D0 := D0) (g := g) (φ := φ) (A := A) (h := h) (strict := strict)
    (a := ToralCatMap.auxiliary h.r h.regularity_gt_one) (P := P) (L := L)
    (productCalculus := proved_fractionalProductCalculus h.r) (hw := hw) (R := R) (hR := hR)
    (bound := bound) (hφ := hφ)
    (proved_hilbertFirstProjectionRegularity (h.r - 1)) coreAgreement localWeightX

end ConditionedStochasticStabilityHyperbolic.Paper.NativeMainTheorems
