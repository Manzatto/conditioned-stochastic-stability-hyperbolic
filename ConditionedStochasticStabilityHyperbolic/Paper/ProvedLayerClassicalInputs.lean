module
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedForwardLayerClassicalInputs
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedInverseDensitySources

/-! Both forward and inverse random-plaque geometry are constructed. The
remaining ordinary source consists of literal scalar weights/Jacobian laws,
full-test action and interpolation estimates; it has no plaque/capture or
inverse calculus packet. The inverse family argument is the generated output
of Maps.inverseFamily at the final ordinary instantiation. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularLayerClassicalInputs
open Set MeasureTheory Filter IsManifold Bundle
open scoped Topology NNReal BoundedContinuousFunction Manifold ContDiff Bundle
open LeanShared ControlledPlaqueClosure RegularNoise HyperbolicBasicSet

structure PrimitiveInputs
    {E M ι Parameters Test TestCore : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype ι]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [MetricSpace Parameters]
    [NormedAddCommGroup Test] [NormedSpace ℂ Test] [CompleteSpace Test]
    [AddCommGroup TestCore] [Module ℂ TestCore]
    {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
    {evaluate : Parameters → M → M} (p : Representation F Parameters evaluate) (J : InverseFamily F)
    (σ : Measure M) (V K G : Set M) (hK : IsCompact K) [CompactSpace K]
    (w wc : K → ℝ) (R : ℝ) (view : Test →ₗ[ℂ] (M → ℂ))
    (inj : Function.Injective view) (qt : TestCore →ₗ[ℂ] Test) where
  inverse_density_weights : InverseDensityWeights J σ K G w R
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
def PrimitiveInputs.produce
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
    {evaluate : Parameters → M → M} {p : Representation F Parameters evaluate} {J : InverseFamily F}
    {σ : Measure M} {Λ V₀ V K G : Set M} {hK : IsCompact K} [CompactSpace K]
    {w wc : K → ℝ} {R : ℝ} {view : Test →ₗ[ℂ] (M → ℂ)}
    {inj : Function.Injective view} {qt : TestCore →ₗ[ℂ] Test}
    (c : PrimitiveInputs p J σ V K G hK w wc R view inj qt)
    (regularity : 1 ≤ r) (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (basic : BasicData (E := E) T Λ V₀) (core : isolatedCore T K ⊆ Λ)
    (openV : IsOpen V) (insideK : V ⊆ K) (containsV : Λ ⊆ V)
    (openG : IsOpen G) (containsG : Λ ⊆ G) :
    ClassicalInputs p σ V K G hK w wc R view inj qt := by
  let calculated : CalculusInputs p σ V K G hK w wc R view inj qt := {
    inverse_density_geometry := c.inverse_density_weights.produce regularity deterministic inverse
      basic hK core openV insideK containsV openG containsG
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
  exact calculated.produce regularity deterministic (inverse.mdifferentiable (by norm_num))
    basic core openV insideK containsV openG containsG

end ConditionedStochasticStabilityHyperbolic.Paper.RegularLayerClassicalInputs
