module

public import Mathlib.Probability.Kernel.RadonNikodym

/-! Uniform domination constructs a jointly measurable, everywhere bounded
kernel density. Clipping a kernel Radon–Nikodym derivative removes exceptional
sets separately at each starting point without choosing nonmeasurable versions. -/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace LeanShared.DominatedKernelDensity
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace.CountableOrCountablyGenerated X Y]
  (κ : Kernel X Y) [IsFiniteKernel κ] (σ : Measure Y) [IsFiniteMeasure σ]

 theorem exists_bounded_density (B : ℝ≥0∞) (hB : B ≠ ∞)
    (dom : ∀ x, κ x ≤ B • σ) :
    ∃ q : X × Y → ℝ≥0∞, Measurable q ∧ (∀ p, q p ≤ B) ∧
      ∀ x, κ x = σ.withDensity (fun y => q (x, y)) := by
  have : IsFiniteMeasure (B • σ) := ⟨by simp only [Measure.smul_apply, smul_eq_mul]; exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hB (measure_ne_top σ Set.univ))⟩
  let η := Kernel.const X (B • σ)
  let f : X × Y → ℝ≥0∞ := fun p => min (κ.rnDeriv η p.1 p.2) 1
  have hf : Measurable f := (κ.measurable_rnDeriv η).min measurable_const
  refine ⟨fun p => B * f p, measurable_const.mul hf, ?_, ?_⟩
  · intro p
    calc
      B * f p ≤ B * 1 := by dsimp [f]; gcongr; exact min_le_right _ _
      _ = B := mul_one B
  · intro x
    have hle : κ x ≤ η x := dom x
    have hae : ∀ᵐ y ∂η x, κ.rnDeriv η x y ≤ 1 := by
      filter_upwards [κ.rnDeriv_eq_rnDeriv_measure (η := η) (a := x),
        Measure.rnDeriv_le_one_of_le hle] with y he hy
      exact he.trans_le hy
    have he : (η x).withDensity (fun y => f (x, y)) = κ x := by
      rw [withDensity_congr_ae (hae.mono (fun y hy => min_eq_left hy))]
      have hk := Kernel.withDensity_rnDeriv_eq (Measure.absolutelyContinuous_of_le hle)
      rw [Kernel.withDensity_apply η (κ.measurable_rnDeriv η)] at hk
      exact hk
    rw [← he]
    change (B • σ).withDensity (fun y => f (x, y)) = _
    rw [withDensity_smul_measure]
    exact (withDensity_smul B (hf.comp measurable_prodMk_left)).symm

end LeanShared.DominatedKernelDensity
