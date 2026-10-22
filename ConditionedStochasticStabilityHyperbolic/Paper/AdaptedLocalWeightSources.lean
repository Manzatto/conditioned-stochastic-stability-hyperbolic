module

public import ConditionedStochasticStabilityHyperbolic.Paper.AdaptedLocalWeightSetup
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularLayerClassicalInputs

/-! The analysis support and the original live state are independent. The
retained nonreturn certificate is proved for the original closed region. -/

public noncomputable section
open Set MeasureTheory Bundle
open scoped Manifold ContDiff Bundle BoundedContinuousFunction NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.AdaptedLocalWeightSources
open LeanShared RegularNoise
variable {E M ι Parameters Test TestCore : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [Fintype ι] [MetricSpace Parameters]
  [NormedAddCommGroup Test] [NormedSpace ℂ Test] [CompleteSpace Test]
  [AddCommGroup TestCore] [Module ℂ TestCore]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M}
  (h : HL (E := E) T g Λ V) (w : M → ℝ) (W : Set M)
  (setup : AdaptedLocalWeightSetup.Data h w W)
  {r : ℝ} {N : Maps (E := E) (ι := ι) T r} {evaluate : Parameters → M → M}

local instance originalClosedCompact : CompactSpace (closure V) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact

/-- Ordinary plaque/calculus inputs on the small analysis neighborhood give
the full source for the unchanged original closed live process. -/
def source
    (hW : IsOpen W) (hWV : W ⊆ V)
    (p : Representation N Parameters evaluate) (σ : Measure M) (R : ℝ)
    (view : Test →ₗ[ℂ] (M → ℂ)) (inj : Function.Injective view)
    (qt : TestCore →ₗ[ℂ] Test)
    (ordinary : RegularLayerClassicalInputs.ClassicalInputs p σ W (closure V) setup.collar
      isClosed_closure.isCompact (fun x => w x.val) (setup.liveCutoff h w W) R view inj qt)
    (hw : Continuous w) (hwn : ∀ x ∈ closure V, 0 ≤ w x) :
    RegularLayerNoiseSources.Data p σ W (closure V) setup.collar setup.retained
      isClosed_closure.isCompact (fun x => w x.val) (setup.liveCutoff h w W) R view inj qt := by
  have core_collar : isolatedCore T (closure V) ⊆ setup.collar := by
    rw [← h.actual_isolated_core]
    exact setup.core_collar
  exact RegularLayerClassicalInputs.ClassicalInputs.withGeometry p σ W (closure V) setup.collar
    isClosed_closure.isCompact (fun x => w x.val) (setup.liveCutoff h w W) R view inj qt ordinary
    setup.retained hW (hWV.trans subset_closure) setup.collar_open core_collar
    setup.retained_open (setup.core_live h w W) (setup.retained_live h w W) setup.no_return
    (fun x => hwn x.val x.property) (setup.liveCutoff_continuous h w W hw)
    (setup.liveCutoff_nonnegative h w W) (setup.liveCutoff_support h w W)
    (setup.liveCutoff_agreement h w W)

end ConditionedStochasticStabilityHyperbolic.Paper.AdaptedLocalWeightSources
