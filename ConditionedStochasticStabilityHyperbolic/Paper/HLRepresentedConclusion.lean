module

public import ConditionedStochasticStabilityHyperbolic.Paper.HLFamilyConclusion
public import ConditionedStochasticStabilityHyperbolic.Paper.EquilibriumOnCollar

/-! The represented physical family gives the literal shrinking-cube theorem.
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

variable {Parameters : Type*} [MetricSpace Parameters] {evaluate : Parameters → M → M}

theorem stability_of_hl_represented_points
    (p : RegularNoise.Representation F Parameters evaluate)
    (hmap : ∀ ε : ℝ≥0, Measurable
      (fun z : M × RegularNoise.FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1))
    (φ : M → ℝ) (hφ : ∀ x ∈ Λ, g x = Real.exp (φ x))
    (ν : ℝ≥0 → ProbabilityMeasure K)
    (limit : Tendsto ν (𝓝[>] (0 : ℝ≥0)) (𝓝 (h.stateOnCollar e K hK hΛK)))
    (points : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
      Point (RestrictedNoise.chain (L.fixedLaw ε)
        (fun z : M × RegularNoise.FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1)
        (hmap ε) K hK w hw R hR hwR) R {x : K | x.val ∈ Λ} (ν ε)) :
    Stability F L K Λ hK w hw R hR hwR
      (fun x => φ x - Real.log (h.basic.hyperbolic.unstableJacobian x)) := by
  exact stability_of_hl_eventual_points h e F L K hK hΛK w hw R hR hwR φ hφ ν limit
    (eventual_points_of_represented F L K Λ hK w hw R hR hwR p hmap ν points)

end ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
