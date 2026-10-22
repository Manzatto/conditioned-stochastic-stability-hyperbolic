module
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedBasicInverseCubeGeometry
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseDensityFamily

/-! Only literal scalar inverse weights and change of variables remain in
this source. Every inverse-calculus and random-plaque field of the former
inverse density source is derived from actual hyperbolicity and regular noise. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set MeasureTheory IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle NNReal ENNReal
open LeanShared.HyperbolicBasicSet

structure InverseDensityWeights
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [ChartedSpace E M] [Fintype ι]
    [MeasurableSpace M] [BorelSpace M]
    {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
    (J : InverseFamily F) (σ : Measure M) (K G : Set M) (w : K → ℝ) (R : ℝ) where
  window : ℝ≥0
  positive : 0 < window
  window_le : window ≤ J.window
  weight : (ε : ℝ≥0) → M × cube (ι := ι) ε → ℝ
  measurable : ∀ ε, 0 < ε → ε ≤ window → Measurable (weight ε)
  nonnegative : ∀ ε, 0 < ε → ε ≤ window → ∀ x a, 0 ≤ weight ε (x,a)
  continuous : ∀ ε, 0 < ε → ε ≤ window → ∀ a, Continuous (fun x => weight ε (x,a))
  bounded : ∀ ε, 0 < ε → ε ≤ window → ∃ B : ℝ, 0 ≤ B ∧ ∀ x a, ‖weight ε (x,a)‖ ≤ B
  positive_on : ∀ ε, 0 < ε → ε ≤ window → ∀ x, x ∈ K → x ∈ G → ∀ a, 0 < weight ε (x,a)
  change_variables : ∀ ε, 0 < ε → ε ≤ window → ∀ f g : M → ℝ≥0∞, Measurable f → Measurable g →
    ∀ a : cube (ι := ι) ε,
      (∫⁻ x, g x * (ENNReal.ofReal (weight ε (x,a)) * K.indicator f (J.map ε (a.val,x))) ∂σ.restrict K) =
      ∫⁻ x, f x * (ENNReal.ofReal (LeanShared.SubtypeKernel.zeroExtend K w x / R) *
        K.indicator g (F.family ε a.val x)) ∂σ.restrict K

set_option maxHeartbeats 3200000 in
def InverseDensityWeights.produce
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    {T : M ≃ₜ M} {r : ℝ} {Λ V₀ V K G : Set M} {σ : Measure M} {w : K → ℝ} {R : ℝ}
    {F : Maps (E := E) (ι := ι) T r} {J : InverseFamily F}
    (c : InverseDensityWeights J σ K G w R) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (basic : BasicData (E := E) T Λ V₀)
    (compactK : IsCompact K) (core : LeanShared.isolatedCore T K ⊆ Λ)
    (openV : IsOpen V) (insideK : V ⊆ K) (containsV : Λ ⊆ V)
    (openG : IsOpen G) (containsG : Λ ⊆ G) : InverseDensityOrdinarySources F σ V K G w R := by
  classical
  have witness := J.eventually_basic_inverse_geometry regularity deterministic inverse basic
    compactK core openV insideK containsV openG containsG
  let η := Classical.choose witness
  have properties := Classical.choose_spec witness
  let chooseGeometry := fun ε hp hw => Classical.choose (properties.2.2 ε hp hw)
  have mapGeometry ε hp hw : (chooseGeometry ε hp hw).map = J.map ε :=
    Classical.choose_spec (properties.2.2 ε hp hw)
  refine {
    window := min c.window η
    window_positive := lt_min c.positive properties.1
    window_le := (min_le_left _ _).trans (c.window_le.trans J.window_le)
    geometry := fun ε hp hw => chooseGeometry ε hp (hw.trans (min_le_right _ _))
    weight := c.weight
    measurable_weight := fun ε hp hw => c.measurable ε hp (hw.trans (min_le_left _ _))
    nonnegative_weight := fun ε hp hw => c.nonnegative ε hp (hw.trans (min_le_left _ _))
    continuous_weight := fun ε hp hw => c.continuous ε hp (hw.trans (min_le_left _ _))
    bounded_weight := fun ε hp hw => c.bounded ε hp (hw.trans (min_le_left _ _))
    positive_weight := fun ε hp hw => c.positive_on ε hp (hw.trans (min_le_left _ _))
    change_variables := ?_ }
  intro ε hp hw f g hf hg a
  change (∫⁻ x, g x * (ENNReal.ofReal (c.weight ε (x,a)) *
    K.indicator f ((chooseGeometry ε hp (hw.trans (min_le_right _ _))).map (a.val,x))) ∂σ.restrict K) = _
  rw [mapGeometry ε hp (hw.trans (min_le_right _ _))]
  exact c.change_variables ε hp (hw.trans (min_le_left _ _)) f g hf hg a

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
