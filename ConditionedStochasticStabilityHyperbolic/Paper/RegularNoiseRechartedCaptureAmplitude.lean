module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseCaptureWordAmplitudeHolder
public import LeanShared.Geometry.ManifoldLocalizationLinearRechart
import Mathlib.Tactic.Ring

/-! The full actual cutoff-word amplitude is transported through a specified
linear equivalence to its genuine Fourier coordinate model. The noise
maps, original normed manifold, weights, cutoffs, and reference are retained.
Only the explicit fixed coordinate-change Holder constant is added. -/
public noncomputable section
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction NNReal BigOperators
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared CylinderPrincipalCoefficient
variable {E Z M ι I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  [Fintype ι] [Fintype I]

theorem Maps.recharted_capture_word_amplitude_holder (μE : Measure E) [μE.IsAddHaarMeasure]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (hr : 1 ≤ r)
    (regular : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    {g : M → ℝ} {q a : ℝ} (ha : 0 < a) (ha1 : a < 1) (haq : a < q)
    (weight : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q g)
    {K : Set M} {v : I → Set M} (d : FiniteSmoothCapturePartition.Data (E := E) K v)
    (c : I → OpenPartialHomeomorph M E)
    (hc : ∀ i, c i ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (source : ∀ i, v i ⊆ (c i).source) (e : E ≃L[ℝ] Z) :
    ∃ η : NNReal, 0 < η ∧ η ≤ F.window ∧ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∀ ε : NNReal, 0 < ε → ε ≤ η → ∀ N : ℕ,
      ∀ controls : Fin N → cube (ι := ι) ε, ∀ labels : Fin (N + 1) → I,
      ∃ f : Z →ᵇ ℂ,
        (∀ x, f x = ChartLocalization.coordinate
          (LinearRechartedManifold.chartImage e (c (labels 0)))
          (fun m => (FiniteSmoothCapturePartition.wordCutoff d
            (fun j : Fin (N + 1) => prefixOrbit
              (fun control : cube (ι := ι) ε => F.family ε control.val) controls j.val m) labels : ℂ))
          (ActualFiniteRegularWord.weight
            (fun control : cube (ι := ι) ε => F.family ε control.val) g (List.ofFn controls)) x) ∧
        ‖f‖ ≤ C * B ^ N ∧
        tsupport (fun x => f x) ⊆ ChartLocalization.localSupport
          (LinearRechartedManifold.chartImage e (c (labels 0))) (fun m => (d.beta (labels 0) m : ℂ)) ∧
        ∀ x y, ‖f x - f y‖ ≤ (C * B ^ N) * dist x y ^ a := by
  obtain ⟨η, positive, below, B, C, nonnegB, nonnegC, estimates⟩ :=
    F.capture_word_amplitude_holder μE hr regular ha ha1 haq weight d c hc source
  let L : ℝ := ‖e.symm.toContinuousLinearMap‖
  let factor : ℝ := max 1 (L ^ a)
  have oneFactor : 1 ≤ factor := le_max_left _ _
  have rpowFactor : L ^ a ≤ factor := le_max_right _ _
  have nonnegFactor : 0 ≤ factor := zero_le_one.trans oneFactor
  refine ⟨η, positive, below, B, C * factor, nonnegB, mul_nonneg nonnegC nonnegFactor, ?_⟩
  intro ε hp hw N controls labels
  obtain ⟨f, formula, normBound, support, holder⟩ := estimates ε hp hw N controls labels
  let f' : Z →ᵇ ℂ := f.compContinuous ⟨e.symm, e.symm.continuous⟩
  have coefficient : C * B ^ N ≤ (C * factor) * B ^ N := by
    calc
      _ = (C * 1) * B ^ N := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left oneFactor nonnegC)
        (pow_nonneg nonnegB _)
  refine ⟨f', ?_, (BoundedContinuousFunction.norm_compContinuous_le _ _).trans
    (normBound.trans coefficient), ?_, ?_⟩
  · intro x
    exact (formula (e.symm x)).trans
      (ConstructedManifoldLocalization.coordinate_linearRechart c e (labels 0) _ _ x).symm
  · rw [ConstructedManifoldLocalization.localSupport_linearRechart c e]
    change tsupport ((fun x => f x) ∘ e.symm.toHomeomorph) ⊆ _
    rw [tsupport_comp_eq_preimage]
    intro x hx
    exact ⟨e.symm x, support hx, e.apply_symm_apply x⟩
  · intro x y
    have distance : dist (e.symm x) (e.symm y) ≤ L * dist x y :=
      e.symm.toContinuousLinearMap.lipschitzWith.dist_le_mul x y
    have compose := (holder (e.symm x) (e.symm y)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg distance ha.le)
        (mul_nonneg nonnegC (pow_nonneg nonnegB _)))
    rw [Real.mul_rpow (norm_nonneg _) dist_nonneg] at compose
    change ‖f (e.symm x) - f (e.symm y)‖ ≤ _
    calc
      _ ≤ (C * B ^ N) * (L ^ a * dist x y ^ a) := compose
      _ ≤ (C * B ^ N) * (factor * dist x y ^ a) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right rpowFactor (Real.rpow_nonneg dist_nonneg _))
          (mul_nonneg nonnegC (pow_nonneg nonnegB _))
      _ = _ := by ring

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
