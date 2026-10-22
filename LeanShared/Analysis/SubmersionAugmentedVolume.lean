module
public import LeanShared.Analysis.SubmersionLinearCoordinates
public import LeanShared.Analysis.LocalVolumeDomination

/-! Full-rank maps with excess control coordinates give genuine square local
volume bounds after adjoining their constructed kernel coordinates. -/
public noncomputable section
namespace LeanShared.SubmersionLinearCoordinates
open Set MeasureTheory
open scoped ENNReal

theorem exists_augmented_local_volume_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → F} {x : E} (smooth : ContDiffAt ℝ 1 f x)
    (rank : Function.Surjective (fderiv ℝ f x)) :
    ∃ P : E →L[ℝ] (fderiv ℝ f x).ker,
    ∃ e : E ≃L[ℝ] ((fderiv ℝ f x).ker × F),
      (∀ z, e z = (P z, fderiv ℝ f x z)) ∧
    ∃ u : Set E, IsOpen u ∧ x ∈ u ∧
      DifferentiableOn ℝ (fun z => e.symm (P z, f z)) u ∧
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      (μ.restrict u).map (fun z => e.symm (P z, f z)) ≤ C • μ := by
  obtain ⟨P, e, coordinates⟩ := exists_kernel_coordinates (fderiv ℝ f x) rank
  have linear_identity : e.symm.toContinuousLinearMap.comp
      (P.prod (fderiv ℝ f x)) = ContinuousLinearMap.id ℝ E := by
    ext z
    change e.symm (P z, fderiv ℝ f x z) = z
    rw [← coordinates, e.symm_apply_apply]
  have derivative := e.symm.toContinuousLinearMap.hasStrictFDerivAt.comp x
    (P.hasStrictFDerivAt.prodMk (smooth.hasStrictFDerivAt one_ne_zero))
  rw [linear_identity] at derivative
  have regular : ContDiffAt ℝ 1 (fun z => e.symm (P z, f z)) x :=
    e.symm.contDiff.contDiffAt.comp x (P.contDiff.contDiffAt.prodMk smooth)
  have bound := DifferentialVolumeBound.exists_local_volume_bound_without_measurability
    μ regular (ContinuousLinearEquiv.refl ℝ E) derivative
  exact ⟨P, e, coordinates, bound⟩

end LeanShared.SubmersionLinearCoordinates
