module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ProducedWeakIntermediate
public import ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalGlobalApplication
public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniConfinement

/-! A derived analytic family for one actual closed killed process. No noisy spectral gap, leading
vector, quasi-ergodic measure or limit is an input field. -/

public noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.ClosedLayerAnalyticPacket
open LeanShared KellerLiverani1999 ComplexStrongFeller

universe uS uW

structure Data {X Ξ : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Ξ] (K : Set X) [CompactSpace K]
    (C : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain K)
    (law : ℝ≥0 → Measure Ξ) (probability : ∀ ε, IsProbabilityMeasure (law ε))
    (scale pressure : ℝ) where
  Strong : Type uS
  [strongNormed : NormedAddCommGroup Strong]
  [strongScalar : NormedSpace ℂ Strong]
  [strongComplete : CompleteSpace Strong]
  [strongNontrivial : Nontrivial Strong]
  Weak : Type uW
  [weakNormed : NormedAddCommGroup Weak]
  [weakScalar : NormedSpace ℂ Weak]
  [weakComplete : CompleteSpace Weak]
  inclusion : Strong →L[ℂ] Weak
  generator : ℝ≥0 → Ξ → Strong →L[ℂ] Strong
  model : ProducedAnnealedModel.Data inclusion inclusion law probability generator scale
  essential : EssentialRadiusContract (E := Strong) (W := Weak)
  confinement : ClassicalConfinementContract (E := Strong) (W := Weak)
  reference_radius : spectralRadius ℂ ((scale : ℂ) • model.inputs.operator 0) =
    ENNReal.ofReal (Real.exp pressure)
  principal_below_pressure : model.inputs.principal < Real.exp pressure
  eigenvectors : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
    ∀ sf : HasStrongFellerKernel (C ε), ∀ f : K →ᵇ ℂ, f ≠ 0 → ∀ z : ℂ,
      (scale • transferOperator (𝕜 := ℂ) (C ε) sf) f = z • f →
      model.inputs.principal < ‖z‖ →
      ∃ v : Strong, v ≠ 0 ∧ ((scale : ℂ) • model.inputs.operator ε) v = z • v

attribute [instance] Data.strongNormed Data.strongScalar Data.strongComplete
  Data.strongNontrivial Data.weakNormed Data.weakScalar Data.weakComplete

end ConditionedStochasticStabilityHyperbolic.Paper.ClosedLayerAnalyticPacket
