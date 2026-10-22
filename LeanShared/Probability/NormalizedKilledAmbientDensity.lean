module

public import LeanShared.Probability.NormalizedKilledDensity

/-! The actual normalized killed density also exists relative to AMBIENT
volume, by inserting the live-set indicator. This lets the global filtration
use ordinary ambient nonsingularity, without incorrectly requiring the
restricted live volume to be nonsingular on points that can be absorbed. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace LeanShared.NormalizedKilledAmbientDensity
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
        σ.withDensity (fun y => q' (x, y)) := by
  obtain ⟨b, hb, boundb, reprb⟩ := NormalizedKilledDensity.exists_density
    ρ F hF σ q hq repr B bound K hK w hw R hR hwR
  let a : X × X → ℝ≥0∞ := (Prod.snd ⁻¹' K).indicator b
  refine ⟨a, hb.indicator (hK.preimage measurable_snd), ?_, ?_⟩
  · intro p
    by_cases hp : p ∈ Prod.snd ⁻¹' K
    · simpa only [a, indicator_of_mem hp] using boundb p
    · simp only [a, indicator_of_notMem hp, zero_le]
  · intro x
    rw [reprb x, ← withDensity_indicator hK]
    rfl

end LeanShared.NormalizedKilledAmbientDensity
