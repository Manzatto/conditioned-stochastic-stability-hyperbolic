module

public import LeanShared.Probability.RandomMapKernel
public import LeanShared.Probability.WeightedConditioning
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! An actual forward density gives the normalized killed-kernel density on
the restricted reference, with the SAME uniform bound. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace LeanShared.NormalizedKilledDensity
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

 theorem exists_density (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (F : X × Ω → X) (hF : Measurable F) (σ : Measure X)
    (q : X × X → ℝ≥0∞) (hq : Measurable q)
    (repr : ∀ x, RandomMapKernel.transition ρ F hF x = σ.withDensity (fun y => q (x, y)))
    (B : ℝ≥0∞) (bound : ∀ p, q p ≤ B)
    (K : Set X) (hK : MeasurableSet K)
    (w : X → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) :
    ∃ q' : X × X → ℝ≥0∞, Measurable q' ∧ (∀ p, q' p ≤ B) ∧ ∀ x,
      WeightedConditioning.normalizedKernel (RandomMapKernel.killed ρ F hF K hK) w R hw x =
        (σ.restrict K).withDensity (fun y => q' (x, y)) := by
  let q' : X × X → ℝ≥0∞ := fun p => ENNReal.ofReal (w p.1 / R) * q p
  have hq' : Measurable q' := ((hw.comp measurable_fst).div_const R).ennreal_ofReal.mul hq
  refine ⟨q', hq', ?_, ?_⟩
  · intro p
    have he := WeightedConditioning.normalizedWeight_le_one w hR hwR p.1
    change ENNReal.ofReal (w p.1 / R) * q p ≤ B
    calc
      _ ≤ 1 * B := mul_le_mul' he (bound p)
      _ = B := one_mul B
  · intro x
    change ENNReal.ofReal (w x / R) •
      (RandomMapKernel.transition ρ F hF x).restrict K = _
    rw [repr x, restrict_withDensity hK]
    exact (withDensity_smul (ENNReal.ofReal (w x / R))
      (hq.comp measurable_prodMk_left)).symm

end LeanShared.NormalizedKilledDensity
