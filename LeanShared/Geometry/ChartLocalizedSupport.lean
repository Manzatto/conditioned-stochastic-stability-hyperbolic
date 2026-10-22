module
public import LeanShared.Geometry.ChartLocalization

/-! Chart localization retains the original function's exact support,
in addition to the fixed cutoff support. This is needed for smoothing
inside the original open region rather than a larger collar. -/
public noncomputable section
open Set
namespace LeanShared.ChartLocalizedSupport
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  (e : OpenPartialHomeomorph M E) (θ f : M → ℂ)
  (support : tsupport θ ⊆ e.source) (compact : HasCompactSupport θ)

include support compact in
omit [NormedSpace ℝ E] [ChartedSpace E M] in
theorem subset : tsupport (ChartLocalization.coordinate e θ f) ⊆
    e '' (tsupport θ ∩ tsupport f) := by
  have compactK : IsCompact (e '' (tsupport θ ∩ tsupport f)) :=
    (compact.inter_right (isClosed_tsupport f)).image_of_continuousOn
      (e.continuousOn.mono (fun x hx => support hx.1))
  apply closure_minimal _ compactK.isClosed
  intro y hy
  change ChartLocalization.coordinate e θ f y ≠ 0 at hy
  by_cases target : y ∈ e.target
  · have nonzero : θ (e.symm y) * f (e.symm y) ≠ 0 := by
      simpa only [ChartLocalization.coordinate, ite_eq_left target] using hy
    exact ⟨e.symm y,
      ⟨subset_tsupport θ (mul_ne_zero_iff.mp nonzero).1,
        subset_tsupport f (mul_ne_zero_iff.mp nonzero).2⟩, e.right_inv target⟩
  · exact False.elim (hy (by simp only [ChartLocalization.coordinate, ite_eq_right target]))

include support compact in
omit [NormedSpace ℝ E] [ChartedSpace E M] in
theorem in_region {V : Set M} (region : tsupport f ⊆ V) :
    tsupport (ChartLocalization.coordinate e θ f) ⊆ e.target ∩ e.symm ⁻¹' V := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := subset e θ f support compact hy
  exact ⟨e.map_source (support hx.1), by
    change e.symm (e x) ∈ V
    rw [e.left_inv (support hx.1)]
    exact region hx.2⟩
end LeanShared.ChartLocalizedSupport
