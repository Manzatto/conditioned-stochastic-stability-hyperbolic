module
public import LeanShared.Analysis.BumpSupportedHolderDensity
public import LeanShared.Geometry.EuclideanFractionalHolder

/-! Exact-support smoothing of actual Euclidean fractional functions.
The global Hölder constant and the approximating sequence are both
constructed from fractional regularity and compact support. -/
public noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace LeanShared.SupportedFractionalApproximation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

include μ in
theorem exists_sequence (f : E →ᵇ ℂ) {V : Set E} (hV : IsOpen V)
    (support : tsupport f ⊆ V) (compact : HasCompactSupport f)
    {a b : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb : 0 ≤ b) (hab : b < a)
    (regular : FractionalManifoldRegularity.Regular (E := E) (F := ℂ) a (fun x => f x)) :
    ∃ C : ℝ, ∃ hC : 0 ≤ C,
      ∃ hf : ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ a,
      ∃ v : ℕ → BoundedHolderSpace.graph E b,
        (∀ n, BumpSupportedHolderDensity.SmoothGraph V (v n)) ∧
          Tendsto v atTop (𝓝 (BumpLowerHolderConvergence.lift f hb hab hC hf)) := by
  obtain ⟨C, hC, hf⟩ := FractionalManifoldRegularity.global_holder_of_regular
    f compact ha ha1 regular
  exact ⟨C, hC, hf, BumpSupportedHolderDensity.exists_sequence
    μ f hV support compact hb hab hC hf⟩
end LeanShared.SupportedFractionalApproximation
