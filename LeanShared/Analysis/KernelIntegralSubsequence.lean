module

public import LeanShared.Analysis.RadonNikodymL1Rows
public import LeanShared.Analysis.BoundedL1Functional
public import LeanShared.Analysis.WeakDualSubsequence
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! Common finite domination yields one subsequence on which all kernel
integrals converge pointwise. The kernel rows need not have bounded densities. -/
public noncomputable section
open Filter Topology MeasureTheory TopologicalSpace
namespace LeanShared.KernelIntegralSubsequence
variable {X Y : Type*} [MeasurableSpace Y]

/-- Banach--Alaoglu on the separable L1 predual controls every RN row
simultaneously. No pointwise compactness of the original functions is assumed. -/
theorem exists_pointwise (κ : X → Measure Y) [∀ x, IsFiniteMeasure (κ x)]
    (μ : Measure Y) [SigmaFinite μ] [SeparableSpace (Lp ℂ 1 μ)]
    (ac : ∀ x, κ x ≪ μ)
    (f : ℕ → Y → ℂ) (measurable : ∀ n, Measurable (f n))
    (B : ℝ) (hB : 0 ≤ B) (bounded : ∀ n y, ‖f n y‖ ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : X → ℂ,
      ∀ x, Tendsto (fun n => ∫ y, f (φ n) y ∂κ x) atTop (𝓝 (g x)) := by
  let F : ℕ → Lp ℂ 1 μ →L[ℂ] ℂ := fun n =>
    BoundedL1Functional.functional μ (f n) B (measurable n).aestronglyMeasurable
      (ae_of_all _ (bounded n))
  have bound (n : ℕ) : ‖F n‖ ≤ B :=
    BoundedL1Functional.functional_norm_le μ (f n) B hB
      (measurable n).aestronglyMeasurable (ae_of_all _ (bounded n))
  obtain ⟨l,_,φ,mono,converges⟩ := WeakDualSubsequence.exists_pointwise F B bound
  refine ⟨φ,mono,(fun x => l (RadonNikodymL1Rows.row (κ x) μ)),fun x => ?_⟩
  have equality (n : ℕ) : F (φ n) (RadonNikodymL1Rows.row (κ x) μ) =
      ∫ y, f (φ n) y ∂κ x := by
    rw [BoundedL1Functional.functional_apply]
    exact RadonNikodymL1Rows.integral_mul_row (κ x) μ (ac x) (f (φ n))
  simpa only [equality] using converges (RadonNikodymL1Rows.row (κ x) μ)

end LeanShared.KernelIntegralSubsequence
