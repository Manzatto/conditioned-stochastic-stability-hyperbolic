module

public import LeanShared.Geometry.SupportedRegularPairing
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Faithfulness on an open retained manifold only needs compactly supported
smooth tests, not uniform density in all bounded continuous functions. -/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.SupportedRegularPairing
variable {E X Reg : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace X] [ChartedSpace E X]
  [IsManifold (𝓘(ℝ, E)) ∞ X] [SigmaCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]

theorem faithful_of_smooth_compact_tests
    (σ : Measure X) [IsFiniteMeasure σ]
    (positive : ∀ x : X, x ∈ σ.support)
    (physical : Reg →L[ℂ] (X →ᵇ ℂ))
    (tests : ∀ g : X → ℝ, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ g →
      HasCompactSupport g → ∃ v : Reg, ∀ x, physical v x = (g x : ℂ)) :
    Function.Injective (embedding σ physical) := by
  intro f g hfg
  have zero : embedding σ physical (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  have aeZero : ∀ᵐ x ∂σ, (f - g) x = 0 := by
    apply ae_eq_zero_of_integral_contMDiff_smul_eq_zero (𝓘(ℝ, E))
      ((f - g).integrable σ).locallyIntegrable
    intro q smooth compact
    obtain ⟨v, hv⟩ := tests q smooth compact
    have hz := congrArg (fun d : Reg →L[ℂ] ℂ => d v) zero
    change (∫ x, (f - g) x * physical v x ∂σ) = 0 at hz
    calc
      (∫ x, q x • (f - g) x ∂σ) = ∫ x, (f - g) x * physical v x ∂σ := by
        apply integral_congr_ae
        exact ae_of_all _ (fun x => by
          change q x • (f - g) x = (f - g) x * physical v x
          rw [hv x]
          simp [Complex.real_smul, mul_comm])
      _ = 0 := hz
  have onSupport := σ.support_subset_of_isClosed
    (isClosed_eq (f - g).continuous continuous_const) aeZero
  apply sub_eq_zero.mp
  ext x
  exact onSupport (positive x)

end LeanShared.SupportedRegularPairing
