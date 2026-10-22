module

public import ConditionedStochasticStabilityHyperbolic.Paper.LocalFamilyWindow
public import ConditionedStochasticStabilityHyperbolic.Paper.EquilibriumOnCollar

/-! The actual HL equilibrium determines the only zero-noise probability.
A proved eventual physical point family therefore yields the literal local
stability target, with one noise window and unchanged probability family. -/

public noncomputable section
open Set MeasureTheory Filter Bundle
open scoped Topology NNReal Manifold ContDiff Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
open LeanShared HyperbolicBasicSet
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M}
  (h : HL (E := E) T g Λ V)
  (e : EquilibriumPackage h.basic.hyperbolic g)
  (F : RegularNoise.Maps (E := E) (ι := ι) T h.r) (L : RegularNoise.Laws (ι := ι))
  (K : Set M) (hK : MeasurableSet K) (hΛK : Λ ⊆ K)
  (w : K → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)

theorem stability_of_hl_eventual_points
    (φ : M → ℝ) (hφ : ∀ x ∈ Λ, g x = Real.exp (φ x))
    (ν : ℝ≥0 → ProbabilityMeasure K)
    (limit : Tendsto ν (𝓝[>] (0 : ℝ≥0)) (𝓝 (h.stateOnCollar e K hK hΛK)))
    (points : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), PointAt F L K Λ hK w hw R hR hwR (ν ε) ε) :
    Stability F L K Λ hK w hw R hR hwR
      (fun x => φ x - Real.log (h.basic.hyperbolic.unstableJacobian x)) := by
  apply stability_of_eventual_points F L K Λ hK w hw R hR hwR _
    (h.stateOnCollar e K hK hΛK) e.state (h.stateOnCollar_map e K hK hΛK)
    (h.stateOnCollar_equilibrium e φ hφ) _ ν limit points
  intro ζ hζ
  exact e.unique ζ ((h.equilibrium_exp_on_core φ hφ ζ).mpr hζ)

end ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
