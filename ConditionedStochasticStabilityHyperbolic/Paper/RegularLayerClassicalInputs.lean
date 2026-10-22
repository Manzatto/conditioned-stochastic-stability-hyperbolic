module
public import ConditionedStochasticStabilityHyperbolic.Spectral.UltraFellerSource

public import ConditionedStochasticStabilityHyperbolic.Paper.RegularLayerNoiseSources
public import ConditionedStochasticStabilityHyperbolic.Paper.ClassicalInversePlaqueSources
public import ConditionedStochasticStabilityHyperbolic.Spectral.SquareCompactFredholmSource
public import ConditionedStochasticStabilityHyperbolic.Spectral.PowerCompactRieszSource

/-! Only ordinary plaque, inverse-calculus, Jacobian and classical compact
spectral facts remain in this source record. Retained nonreturn, positive
collars and cutoff agreement are deliberately absent; the constructor below
combines this record with the independently proved deterministic geometry.
No smoothing, noisy comparison, gap, QEM or weak limit is a source field. -/

public noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularLayerClassicalInputs
open LeanShared ControlledPlaqueClosure RegularNoise
variable {E M ι Parameters Test TestCore : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [MetricSpace Parameters]
  [NormedAddCommGroup Test] [NormedSpace ℂ Test] [CompleteSpace Test]
  [AddCommGroup TestCore] [Module ℂ TestCore]
  {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
  {evaluate : Parameters → M → M}

/-- Ordinary random local-manifold facts. Finite capture is derived from
the local backward-orbit characterization, rather than being assumed. -/
structure LocalBackwardPlaqueGeometry
    (H : M × FixedControl (ι := ι) → M) (V G : Set M) where
  plaque : (ℤ → FixedControl (ι := ι)) → Set M
  lower : ∀ path : ℤ → FixedControl (ι := ι),
    ∀ paths : ℕ → ℤ → FixedControl (ι := ι), Tendsto paths atTop (𝓝 path) →
      ∀ z ∈ plaque path, ∃ zn : ℕ → M, Tendsto zn atTop (𝓝 z) ∧
        ∀ k, zn k ∈ plaque (paths k)
  backward : ∀ path : ℤ → FixedControl (ι := ι), ∀ z ∈ plaque path,
    ∃ b : ℕ → M, b 0 = z ∧ (∀ n, b n ∈ V ∩ G) ∧
      ∀ n, H (b (n + 1), backwardNoise path n) = b n
  local_backward : ∀ (path : ℤ → FixedControl (ι := ι)) (b : ℕ → M),
    (∀ n, b n ∈ G) →
    (∀ n, H (b (n + 1), backwardNoise path n) = b n) → b 0 ∈ plaque path

def LocalBackwardPlaqueGeometry.constructed
    {H : M × FixedControl (ι := ι) → M} {V G : Set M}
    (c : LocalBackwardPlaqueGeometry H V G) (K : Set M) :
    ClassicalPlaqueGeometry H V K G :=
  ClassicalPlaqueGeometry.of_local_backward H K c.plaque c.lower c.backward c.local_backward

structure ClassicalInputs (p : Representation F Parameters evaluate)
    (σ : Measure M) (V K G : Set M) (hK : IsCompact K) [CompactSpace K]
    (w wc : K → ℝ) (R : ℝ)
    (view : Test →ₗ[ℂ] (M → ℂ)) (inj : Function.Injective view)
    (qt : TestCore →ₗ[ℂ] Test) where
  plaqueWindow : ℝ≥0
  plaqueWindow_positive : 0 < plaqueWindow
  plaqueWindow_le : plaqueWindow ≤ p.window
  forward_plaques : ∀ ε : ℝ≥0, 0 < ε → ε ≤ plaqueWindow →
    ClassicalPlaqueGeometry
      (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1) V K G
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


omit [FiniteDimensional ℝ E] [CompactSpace M] [SecondCountableTopology M] [CompleteSpace Test] in
/-- Ultra-Feller square compactness is proved from the actual strong-Feller kernel. -/
theorem ClassicalInputs.ultra
    {p : Representation F Parameters evaluate}
    {σ : Measure M} {V K G : Set M} {hK : IsCompact K} [CompactSpace K]
    {w wc : K → ℝ} {R : ℝ}
    {view : Test →ₗ[ℂ] (M → ℂ)} {inj : Function.Injective view}
    {qt : TestCore →ₗ[ℂ] Test}
    (_ : ClassicalInputs p σ V K G hK w wc R view inj qt) :
    StrongFellerSquareCompact.UltraFellerContract (X := K) :=
  StrongFellerSquareCompact.ultraFellerContract

omit [FiniteDimensional ℝ E] [CompactSpace M] [SecondCountableTopology M] [CompleteSpace Test] [BorelSpace M] in
/-- The square-compact Fredholm alternative is proved and is not an ordinary
source field. Intermediate generated records retain this proof as metadata. -/
theorem ClassicalInputs.fredholm
    {p : Representation F Parameters evaluate}
    {σ : Measure M} {V K G : Set M} {hK : IsCompact K} [CompactSpace K]
    {w wc : K → ℝ} {R : ℝ}
    {view : Test →ₗ[ℂ] (M → ℂ)} {inj : Function.Injective view}
    {qt : TestCore →ₗ[ℂ] Test}
    (_ : ClassicalInputs p σ V K G hK w wc R view inj qt) :
    PowerCompactGap.SquareCompactFredholm (F := K →ᵇ ℂ) :=
  PowerCompactGap.squareCompactFredholm

omit [FiniteDimensional ℝ E] [CompactSpace M] [SecondCountableTopology M] [CompleteSpace Test] [BorelSpace M] in
/-- The normalized real pair is constructed by Hahn–Banach and finite-rank
perturbation; no Riesz spectral-projector source remains in ordinary inputs. -/
theorem ClassicalInputs.riesz
    {p : Representation F Parameters evaluate}
    {σ : Measure M} {V K G : Set M} {hK : IsCompact K} [CompactSpace K]
    {w wc : K → ℝ} {R : ℝ}
    {view : Test →ₗ[ℂ] (M → ℂ)} {inj : Function.Injective view}
    {qt : TestCore →ₗ[ℂ] Test}
    (_ : ClassicalInputs p σ V K G hK w wc R view inj qt) :
    PowerCompactRealLeadingPair.ClassicalContract (X := K) :=
  PowerCompactRealLeadingPair.classicalContract


def ClassicalInputs.withGeometry (p : Representation F Parameters evaluate)
    (σ : Measure M) (V K G : Set M) (hK : IsCompact K) [CompactSpace K]
    (w wc : K → ℝ) (R : ℝ)
    (view : Test →ₗ[ℂ] (M → ℂ)) (inj : Function.Injective view)
    (qt : TestCore →ₗ[ℂ] Test)
    (c : ClassicalInputs p σ V K G hK w wc R view inj qt)
    (B : Set M)
    (live_open : IsOpen V)
    (live_subset : V ⊆ K)
    (collar_open : IsOpen G)
    (core_collar : isolatedCore T K ⊆ G)
    (retained_open : IsOpen B)
    (core_retained : isolatedCore T K ⊆ B)
    (retained_live : closure B ⊆ V)
    (no_return : (T '' closure B) ∩ forwardTrapped T K ⊆ B)
    (weight_nonnegative : ∀ x, 0 ≤ w x)
    (cutoff_continuous : Continuous wc)
    (cutoff_nonnegative : ∀ x, 0 ≤ wc x)
    (cutoff_support : tsupport wc ⊆ {x : K | x.val ∈ V})
    (weight_agreement : ∀ x : K, x.val ∈ closure B → wc x = w x)
    : RegularLayerNoiseSources.Data p σ V K G B hK w wc R view inj qt where
  live_open := live_open
  live_subset := live_subset
  collar_open := collar_open
  core_collar := core_collar
  retained_open := retained_open
  core_retained := core_retained
  retained_live := retained_live
  no_return := no_return
  weight_nonnegative := weight_nonnegative
  cutoff_continuous := cutoff_continuous
  cutoff_nonnegative := cutoff_nonnegative
  cutoff_support := cutoff_support
  weight_agreement := weight_agreement
  plaqueWindow := c.plaqueWindow
  plaqueWindow_positive := c.plaqueWindow_positive
  plaqueWindow_le := c.plaqueWindow_le
  forward_plaques := fun ε he hw => c.forward_plaques ε he hw
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
  ultra := c.ultra
  fredholm := c.fredholm
  riesz := c.riesz

end ConditionedStochasticStabilityHyperbolic.Paper.RegularLayerClassicalInputs
