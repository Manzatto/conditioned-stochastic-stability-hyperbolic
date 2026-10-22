module

public import LeanShared.Analysis.InvariantFiniteRegularTransfer
public import LeanShared.Analysis.DenseCoreRandomOperators

/-! Construct the actual inverse/Jacobian weighted action on FULL ordinary
little-Cu test functions. Its weight depends on both state and noise. The
only calculus inputs are literal product/composition membership and its
ordinary norm bound; no completed ambient operator is a source field. -/

@[expose] public noncomputable section
open MeasureTheory Set
namespace ConditionedStochasticStabilityHyperbolic.InverseRegularTransfer
open LeanShared FiniteRegularTransferRealization
variable {X Ω Test : Type*} [NormedAddCommGroup Test] [NormedSpace ℂ Test]

structure OrdinarySources (view : Test →ₗ[ℂ] (X → ℂ))
    (H : Ω → X → X) (W : X × Ω → ℝ) where
  membership : ∀ z f, weightedComposition (H z) (fun x => W (x, z)) (view f) ∈ view.range
  bound : ℝ
  bound_nonnegative : 0 ≤ bound
  norm_bound : ∀ z f v,
    view v = weightedComposition (H z) (fun x => W (x, z)) (view f) → ‖v‖ ≤ bound * ‖f‖

namespace OrdinarySources
variable {view : Test →ₗ[ℂ] (X → ℂ)} (inj : Function.Injective view)
  {H : Ω → X → X} {W : X × Ω → ℝ} (s : OrdinarySources view H W)

def action (z : Ω) : Test →ₗ[ℂ] Test :=
  InvariantFiniteRegularTransfer.action view inj (fun _ : Unit => H z)
    (fun x => W (x, z)) (fun _ f => s.membership z f) ()

theorem action_function (z : Ω) (f : Test) (x : X) :
    view (s.action inj z f) x = (W (x, z) : ℂ) * view f (H z x) :=
  InvariantFiniteRegularTransfer.action_apply _ _ _ _ _ _ _ _

include inj s in
theorem action_norm_le (z : Ω) (f : Test) : ‖s.action inj z f‖ ≤ s.bound * ‖f‖ := by
  apply s.norm_bound z f
  funext x
  exact s.action_function inj z f x

def operator (z : Ω) : Test →L[ℂ] Test :=
  (s.action inj z).mkContinuous s.bound (s.action_norm_le inj z)

theorem operator_function (z : Ω) (f : Test) (x : X) :
    view (s.operator inj z f) x = (W (x, z) : ℂ) * view f (H z x) :=
  s.action_function inj z f x

theorem operator_norm_le (z : Ω) : ‖s.operator inj z‖ ≤ s.bound :=
  LinearMap.mkContinuous_norm_le _ s.bound_nonnegative _

/-- The compactly supported cutoff removes the killed-target indicator
from the full ordinary test action. -/
theorem operator_function_killed (K : Set X)
    (outside_zero : ∀ x z, H z x ∉ K → W (x, z) = 0)
    (z : Ω) (f : Test) (x : X) :
    view (s.operator inj z f) x = (W (x, z) : ℂ) * K.indicator (view f) (H z x) := by
  rw [s.operator_function]
  by_cases hx : H z x ∈ K
  · rw [indicator_of_mem hx]
  · rw [outside_zero x z hx]
    simp only [Complex.ofReal_zero, zero_mul]

section Average
variable [MeasurableSpace Ω] [CompleteSpace Test]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {Core : Type*} (smooth : Core → Test) (dense : DenseRange smooth)
    (coreMeasurable : ∀ c, AEStronglyMeasurable (fun z => s.operator inj z (smooth c)) ρ)

def average : Test →L[ℂ] Test :=
  AnnealedOperatorBounds.pointwiseAnnealed ρ (s.operator inj)
    (fun v => DenseCoreRandomOperators.aestronglyMeasurable_of_denseRange ρ
      (s.operator inj) smooth dense coreMeasurable v) s.bound (s.operator_norm_le inj)

/-- Evaluation of the constructed inverse average is the literal integral
including the noise-dependent Jacobian weight. -/
theorem average_function (eval : ∀ _x : X, Test →L[ℂ] ℂ)
    (heval : ∀ x f, eval x f = view f x) (f : Test) (x : X) :
    view (s.average inj ρ smooth dense coreMeasurable f) x =
      ∫ z, (W (x, z) : ℂ) * view f (H z x) ∂ρ := by
  rw [← heval x]
  change eval x (∫ z, s.operator inj z f ∂ρ) = _
  rw [← (eval x).integral_comp_comm]
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => (heval x _).trans (s.operator_function inj z f x))
  · exact AnnealedOperatorBounds.random_apply_integrable ρ (s.operator inj)
      (fun v => DenseCoreRandomOperators.aestronglyMeasurable_of_denseRange ρ
        (s.operator inj) smooth dense coreMeasurable v) s.bound (s.operator_norm_le inj) f

end Average
end OrdinarySources
end ConditionedStochasticStabilityHyperbolic.InverseRegularTransfer
