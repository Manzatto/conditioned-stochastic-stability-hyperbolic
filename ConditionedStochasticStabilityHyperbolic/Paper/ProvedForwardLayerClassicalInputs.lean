module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularLayerClassicalInputs
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedBasicClassicalPlaques

/-! Forward random plaques are proved internally. The remaining source is
ordinary inverse calculus, per-map Jacobian integration and inverse plaque
geometry; no forward plaque, continuity or finite-capture field remains. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularLayerClassicalInputs
open Set MeasureTheory Filter IsManifold Bundle
open scoped Topology NNReal BoundedContinuousFunction Manifold ContDiff Bundle
open LeanShared ControlledPlaqueClosure RegularNoise HyperbolicBasicSet

structure CalculusInputs
    {E M ι Parameters Test TestCore : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype ι]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [MetricSpace Parameters]
    [NormedAddCommGroup Test] [NormedSpace ℂ Test] [CompleteSpace Test]
    [AddCommGroup TestCore] [Module ℂ TestCore]
    {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
    {evaluate : Parameters → M → M} (p : Representation F Parameters evaluate)
    (σ : Measure M) (V K G : Set M) (hK : IsCompact K) [CompactSpace K]
    (w wc : K → ℝ) (R : ℝ) (view : Test →ₗ[ℂ] (M → ℂ))
    (inj : Function.Injective view) (qt : TestCore →ₗ[ℂ] Test) where
  inverse_density_geometry : InverseDensityOrdinarySources F σ V K G w R
  inverseWindow : ℝ≥0
  inverseWindow_positive : 0 < inverseWindow
  inverseMap : ℝ≥0 → FixedControl (ι := ι) → M → M
  inverseWeight : ℝ≥0 → M × FixedControl (ι := ι) → ℝ
  inverseRegular : ∀ ε, 0 < ε → ε ≤ inverseWindow → InverseRegularTransfer.OrdinarySources view (inverseMap ε) (inverseWeight ε)
  inverse_joint : ∀ ε, 0 < ε → ε ≤ inverseWindow → Continuous (fun z : FixedControl (ι := ι) × M => inverseMap ε z.1 z.2)
  inverse_weight_joint : ∀ ε, 0 < ε → ε ≤ inverseWindow → Continuous (fun z : FixedControl (ι := ι) × M => inverseWeight ε (z.2, z.1))
  smooth_continuous : ∀ c, Continuous (view (qt c))
  inverseExponent : ℝ
  inverseExponent_positive : 0 < inverseExponent
  inverseInterpolationConstant : ℝ≥0 → TestCore → FixedControl (ι := ι) → ℝ
  inverse_interpolation : ∀ ε (hp : 0 < ε) (hw : ε ≤ inverseWindow) c z₀ z e, 0 ≤ e →
    (∀ x, ‖view ((inverseRegular ε hp hw).operator inj z (qt c)) x -
      view ((inverseRegular ε hp hw).operator inj z₀ (qt c)) x‖ ≤ e) →
    dist ((inverseRegular ε hp hw).operator inj z (qt c))
      ((inverseRegular ε hp hw).operator inj z₀ (qt c)) ≤
        inverseInterpolationConstant ε c z₀ * e ^ inverseExponent
  jacobian : ∀ ε, 0 < ε → ε ≤ inverseWindow → ∀ z (f : K →ᵇ ℂ) v,
    (∫ x, ActualCutoffAdjoint.raw K
      (fun y : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε y.2) y.1) wc z f x *
      view v x.val ∂σ.comap Subtype.val) =
      ∫ x, f x * ((inverseWeight ε (x.val, z) : ℂ) * view v (inverseMap ε z x.val)) ∂σ.comap Subtype.val


set_option maxHeartbeats 3200000 in
/-- Constructs the complete previous source with its forward-manifold
packet proved from the actual compact basic set and literal regular noise. -/
def CalculusInputs.produce
    {E M ι Parameters Test TestCore : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype ι]
    [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [MetricSpace Parameters]
    [NormedAddCommGroup Test] [NormedSpace ℂ Test] [CompleteSpace Test]
    [AddCommGroup TestCore] [Module ℂ TestCore]
    {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
    {evaluate : Parameters → M → M} {p : Representation F Parameters evaluate}
    {σ : Measure M} {Λ V₀ V K G : Set M} {hK : IsCompact K} [CompactSpace K]
    {w wc : K → ℝ} {R : ℝ} {view : Test →ₗ[ℂ] (M → ℂ)}
    {inj : Function.Injective view} {qt : TestCore →ₗ[ℂ] Test}
    (c : CalculusInputs p σ V K G hK w wc R view inj qt)
    (regularity : 1 ≤ r) (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    (basic : BasicData (E := E) T Λ V₀) (core : isolatedCore T K ⊆ Λ)
    (openV : IsOpen V) (insideK : V ⊆ K) (containsV : Λ ⊆ V)
    (openG : IsOpen G) (containsG : Λ ⊆ G) :
    ClassicalInputs p σ V K G hK w wc R view inj qt := by
  have existence := F.eventually_basic_classical_plaques regularity deterministic
    inverse basic hK core openV insideK containsV openG containsG
  let window := Classical.choose existence
  have positiveWindow := (Classical.choose_spec existence).1
  have make := (Classical.choose_spec existence).2
  refine {
    plaqueWindow := min window p.window
    plaqueWindow_positive := lt_min positiveWindow p.window_positive
    plaqueWindow_le := min_le_right _ _
    forward_plaques := ?_
    inverse_density_geometry := c.inverse_density_geometry
    inverseWindow := c.inverseWindow
    inverseWindow_positive := c.inverseWindow_positive
    inverseMap := c.inverseMap
    inverseWeight := c.inverseWeight
    inverseRegular := c.inverseRegular
    inverse_joint := c.inverse_joint
    inverse_weight_joint := c.inverse_weight_joint
    smooth_continuous := c.smooth_continuous
    inverseExponent := c.inverseExponent
    inverseExponent_positive := c.inverseExponent_positive
    inverseInterpolationConstant := c.inverseInterpolationConstant
    inverse_interpolation := c.inverse_interpolation
    jacobian := c.jacobian
  }
  intro ε hp hw
  have chosen := Classical.choice (make ε hp (hw.trans (min_le_left _ _)))
  have identity : (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1) =
      (fun z : M × FixedControl (ι := ι) => F.fixedMap ε z.1 z.2) :=
    funext (fun z => p.actual_fixedMap ε hp (hw.trans (min_le_right _ _)) z.1 z.2)
  rw [identity]
  exact chosen

end ConditionedStochasticStabilityHyperbolic.Paper.RegularLayerClassicalInputs
