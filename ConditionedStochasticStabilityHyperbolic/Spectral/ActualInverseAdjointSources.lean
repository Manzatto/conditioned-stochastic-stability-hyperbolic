module

public import ConditionedStochasticStabilityHyperbolic.Spectral.InverseRegularTransfer
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualCutoffAdjoint

/-! Ordinary inverse weighted product/composition and smooth-core noise
interpolation construct the full-test adjoint family used by A.2. The
completed scalar change-of-variables law is derived from the literal
per-diffeomorphism Jacobian integral identity. -/

public noncomputable section
open MeasureTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.InverseRegularTransfer
open LeanShared
variable {X Ω Test Core : Type*}
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace Ω] [NormedAddCommGroup Test] [NormedSpace ℂ Test]
  {view : Test →ₗ[ℂ] (X → ℂ)} (inj : Function.Injective view)
  {H : Ω → X → X} {W : X × Ω → ℝ} (s : OrdinarySources view H W)

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem operator_aestronglyMeasurable (ρ : Measure Ω)
    (smooth : Core → Test) (dense : DenseRange smooth)
    (core : ∀ c, AEStronglyMeasurable (fun ω => s.operator inj ω (smooth c)) ρ)
    (v : Test) : AEStronglyMeasurable (fun ω => s.operator inj ω v) ρ :=
  DenseCoreRandomOperators.aestronglyMeasurable_of_denseRange ρ
    (s.operator inj) smooth dense core v

omit [BorelSpace X] [MeasurableSpace Ω] in
theorem changeVariables_of_jacobian
    (K : Set X) (F : X × Ω → X) (w : K → ℝ) (σ : Measure K)
    (physical : Test →L[ℂ] (K →ᵇ ℂ))
    (physical_eq : ∀ v x, physical v x = view v x.val)
    (jacobian : ∀ ω (f : K →ᵇ ℂ) v,
      (∫ x, ActualCutoffAdjoint.raw K F w ω f x * view v x.val ∂σ) =
        ∫ x, f x * ((W (x.val, ω) : ℂ) * view v (H ω x.val)) ∂σ) :
    ∀ ω (f : K →ᵇ ℂ) v,
      (∫ x, ActualCutoffAdjoint.raw K F w ω f x * physical v x ∂σ) =
        ∫ x, f x * physical (s.operator inj ω v) x ∂σ := by
  intro ω f v
  simp_rw [physical_eq]
  rw [jacobian]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by dsimp only; rw [s.operator_function inj])

end ConditionedStochasticStabilityHyperbolic.InverseRegularTransfer
