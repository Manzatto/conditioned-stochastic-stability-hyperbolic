module
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualAnosovGlobalStabilization
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualOriginalGlobalChain
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualProductNoiseChain

/-! Original and stabilized GLOBAL chain families are constructed directly
from the genuine control-cube product maps/laws. Exact pair provenance is a
conclusion; no arbitrary product process or law-matching field is needed. -/
@[expose] public noncomputable section
open Set Function Bundle MeasureTheory Filter
open scoped Manifold ContDiff Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.ActualAnosovGlobalChains
open LeanShared HyperbolicBasicSet RegularNoise ActualProductRestrictedChain
variable {E F X Y ι κ : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [MetricSpace Y] [SecondCountableTopology Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [RiemannianBundle (fun y : Y => TangentSpace (𝓘(ℝ, F)) y)]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [Fintype ι] [Fintype κ]
local instance actualAnosovGlobalChainsOrdinaryCharts : ChartedSpace (E × F) (X × Y) := productCharts
local instance actualAnosovGlobalChainsOrdinaryManifold : IsManifold (𝓘(ℝ, E × F)) ∞ (X × Y) := productManifold
local instance actualAnosovGlobalChainsHilbertCharts : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance actualAnosovGlobalChainsHilbertManifold : IsManifold (𝓘(ℝ, WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)]
  {T : X ≃ₜ X} (D : SpectralDecomposition (E := E) T) {g : X → ℝ} {A : Set X}
  (h : HG1 D g A) (a : AuxiliaryAnosov (F := F) (Y := Y) (ι := κ) h.r)


variable (P : Maps (E := E) (ι := ι) T h.r) (L : Laws (ι := ι))
  (productCalculus : FractionalProductCalculus (E := E) (F := F) (X := X) (Y := Y) h.r)
  (linearCalculus : LinearFractionalCalculus (T := T.prodCongr a.map)
    (LinearRechartedManifold.hilbertProductEquiv (A := E) (B := F)) h.r)
  (w : X → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (bound : ∀ x, w x ≤ R)
local notation "PF" => ActualAnosovGlobalStabilization.Data.maps D h a P productCalculus linearCalculus
local notation "PL" => ActualAnosovGlobalStabilization.Data.laws D h a L
local notation "hAP" => h.absorbing_open.prod isOpen_univ

def original : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain X :=
  ActualOriginalGlobalChain.chain P L Aᶜ h.absorbing_open.measurableSet.compl w hw R hR bound

def stabilized : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain (X × Y) :=
  ActualOriginalGlobalChain.chain (PF) (PL) (A ×ˢ (univ : Set Y))ᶜ
    (hAP).measurableSet.compl (fun z => w z.1) (hw.comp measurable_fst)
    R hR (fun z => bound z.1)

local instance actualAnosovChainOriginalProbability (ε : ℝ≥0) : IsProbabilityMeasure (L.law ε) :=
  L.probability ε
local instance actualAnosovChainProductProbability (ε : ℝ≥0) :
    IsProbabilityMeasure ((productLaws L a.laws).law ε) := (productLaws L a.laws).probability ε

omit [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)] in
/-- The exact raw chains use the ORIGINAL laws at ε and the actual sum-cube
product. The continuation disappears on one common positive noise germ. -/
theorem actual_pair :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ (hε : 0 < ε)
      (window : ε ≤ min P.window a.noise.window),
      original D h P L w hw R hR bound ε =
        NoiseKernel.chain (L.law ε) (actualMap P ε)
          (actualMap_measurable P ε hε (le_min_iff.mp window).1)
          Aᶜ h.absorbing_open.measurableSet.compl w hw R hR bound ∧
      stabilized D h a P L productCalculus linearCalculus w hw R hR bound ε =
        NoiseKernel.chain ((productLaws L a.laws).law ε)
          (joint ε (actualMap P ε) (actualMap a.noise ε))
          (measurable_joint ε (actualMap P ε) (actualMap a.noise ε)
            (actualMap_measurable P ε hε (le_min_iff.mp window).1)
            (actualMap_measurable a.noise ε hε (le_min_iff.mp window).2))
          (A ×ˢ (univ : Set Y))ᶜ (hAP).measurableSet.compl
          (fun z => w z.1) (hw.comp measurable_fst) R hR (fun z => bound z.1) := by
  have small : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ε < (PF).window :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (PF).window_positive)
  filter_upwards [small] with ε hp
  intro hε window
  refine ⟨ActualOriginalGlobalChain.chain_eq P L Aᶜ h.absorbing_open.measurableSet.compl
    w hw R hR bound ε hε (le_min_iff.mp window).1, ?_⟩
  have mapEq :
      (fun z : (X × Y) × cube (ι := ι ⊕ κ) ε => (PF).family ε z.2.val z.1) =
      joint ε (actualMap P ε) (actualMap a.noise ε) := by
    funext z
    rw [ActualAnosovGlobalStabilization.Data.maps_family]
    rfl
  have exactChain := ActualOriginalGlobalChain.chain_eq (PF) (PL)
    (A ×ˢ (univ : Set Y))ᶜ (hAP).measurableSet.compl
    (fun z => w z.1) (hw.comp measurable_fst) R hR (fun z => bound z.1) ε hε hp.le
  simpa only [stabilized, ActualAnosovGlobalStabilization.Data.laws, mapEq] using exactChain

end ConditionedStochasticStabilityHyperbolic.Paper.ActualAnosovGlobalChains
