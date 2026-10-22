module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldModel
public import LeanShared.Analysis.ActualRegularNoiseContinuity

/-! Ordinary lower-Hölder interpolation yields actual evaluated-core continuity.
The top fractional C^r parameter family need not be continuous in its C^r norm.
The primitive contract is the ordinary interpolation inequality, combined with
joint physical map continuity. Noise laws may vary with scale. -/

public noncomputable section
open Set IsManifold MeasureTheory Filter
open scoped Manifold ContDiff SchwartzMap BigOperators Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldNoiseSources
open LeanShared LeanShared.DyadicCompletion LeanShared.CompletedChartPairTransfer
open LeanShared.FiniteRegularTransferRealization

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*}
  [∀ k, NormedAddCommGroup (LocalReg k)] [∀ k, NormedSpace ℂ (LocalReg k)]
  [∀ k, CompleteSpace (LocalReg k)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)



variable [MetricSpace Ω]
structure Data where
  T : Ω
  joint : Continuous (fun z : Ω × M => m.maps z.1 z.2)
  weight_continuous : Continuous m.weight
  exponent : ℝ
  exponent_positive : 0 < exponent
  constant : PhysicalManifoldModel.Core (E := E) V → Ω → ℝ
  interpolation : ∀ c a₀ a ε, 0 ≤ ε →
    (∀ x, ‖m.view (regularAction (SmoothSupportedManifoldCore.functions V) Reg
      m.view m.view_injective m.maps m.weight m.coreRegular a c) x -
      m.view (regularAction (SmoothSupportedManifoldCore.functions V) Reg
      m.view m.view_injective m.maps m.weight m.coreRegular a₀ c) x‖ ≤ ε) →
    dist (regularAction (SmoothSupportedManifoldCore.functions V) Reg
      m.view m.view_injective m.maps m.weight m.coreRegular a c)
      (regularAction (SmoothSupportedManifoldCore.functions V) Reg
      m.view m.view_injective m.maps m.weight m.coreRegular a₀ c) ≤ constant c a₀ * ε ^ exponent

namespace Data
variable (n : Data m)

include n in
omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [∀ k, CompleteSpace (LocalReg k)] in
theorem core_continuous (c : PhysicalManifoldModel.Core (E := E) V) :
    Continuous (fun a => regularAction (SmoothSupportedManifoldCore.functions V) Reg
      m.view m.view_injective m.maps m.weight m.coreRegular a c) := by
  exact ActualRegularNoiseContinuity.continuous_noisy_core
    (SmoothSupportedManifoldCore.functions V) m.view m.view_injective m.maps m.weight
    m.coreRegular id n.joint n.weight_continuous
    (fun c => (SmoothSupportedManifoldCore.smooth V c).continuous)
    Set.univ isCompact_univ (by simp) n.exponent n.exponent_positive n.constant n.interpolation c

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [∀ k, CompleteSpace (LocalReg k)] in
theorem core_tendsto (c : PhysicalManifoldModel.Core (E := E) V) :
    Tendsto (fun a => regularAction (SmoothSupportedManifoldCore.functions V) Reg
      m.view m.view_injective m.maps m.weight m.coreRegular a c) (𝓝 n.T)
      (𝓝 (regularAction (SmoothSupportedManifoldCore.functions V) Reg
        m.view m.view_injective m.maps m.weight m.coreRegular n.T c)) :=
  (n.core_continuous m c).continuousAt

include n in
omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [∀ k, CompleteSpace (LocalReg k)] in
theorem noise_core_continuous {Z : Type*} [TopologicalSpace Z]
    (noise : ℝ≥0 → Z → Ω) (continuous_noise : ∀ ε, Continuous (noise ε))
    (ε : ℝ≥0) (c : PhysicalManifoldModel.Core (E := E) V) :
    Continuous (fun z => regularAction (SmoothSupportedManifoldCore.functions V) Reg
      m.view m.view_injective m.maps m.weight m.coreRegular (noise ε z) c) :=
  (n.core_continuous m c).comp (continuous_noise ε)

end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldNoiseSources
