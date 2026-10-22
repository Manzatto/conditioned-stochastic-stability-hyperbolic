module

public import LeanShared.Analysis.CompactEstimateClosedRange
public import LeanShared.Analysis.TwoNormSpectralShift

/-! Closed ranges of every shifted power outside the strong growth disk.
These are consequences of compact weak inclusion and the actual two-norm
estimate, rather than additional Fredholm hypotheses. -/

public section
open ContinuousLinearMap
namespace LeanShared.CompactTwoNormClosedRange
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- A single Peetre compact estimate closes the range of every operator power. -/
theorem closed_range_powers (S : E →L[ℂ] E) (i : E →L[ℂ] W)
    (hi : IsCompactOperator i) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (estimate : ∀ x, ‖x‖ ≤ A * ‖S x‖ + B * ‖i x‖) (n : ℕ) :
    IsClosed ((S ^ n).range : Set E) := by
  induction n with
  | zero =>
    have h : ((S ^ 0).range : Set E) = Set.univ := by ext x; simp
    rw [h]
    exact isClosed_univ
  | succ n ih =>
    let V := (S ^ n).range
    let : CompleteSpace V := ih.isComplete.completeSpace_coe
    let Sj : V →L[ℂ] E := S.comp V.subtypeL
    let ij : V →L[ℂ] W := i.comp V.subtypeL
    have hclosed : IsClosed (Sj.range : Set E) :=
      CompactEstimateClosedRange.closed_range Sj ij (hi.comp_clm V.subtypeL)
        A B hA hB (fun x => estimate x.val)
    have hrange : (Sj.range : Set E) = ((S ^ (n + 1)).range : Set E) := by
      ext y
      constructor
      · rintro ⟨⟨v, hv⟩, hy⟩
        obtain ⟨x, hx⟩ := hv
        change (S ^ n) x = v at hx
        refine ⟨x, ?_⟩
        rw [pow_succ']
        change S ((S ^ n) x) = y
        rw [hx]
        exact hy
      · rintro ⟨x, hx⟩
        refine ⟨⟨(S ^ n) x, ⟨x, rfl⟩⟩, ?_⟩
        change S ((S ^ n) x) = y
        change (S ^ (n + 1)) x = y at hx
        rw [pow_succ'] at hx
        exact hx
    rw [← hrange]
    exact hclosed

/-- Every shifted power has closed range outside the strong growth disk.
The weak space need not be complete, and no injectivity of the inclusion is needed. -/
theorem spectral_shift (T : E →L[ℂ] E) (i : E →L[ℂ] W)
    (hi : IsCompactOperator i) (α R C D : ℝ)
    (hα : 0 ≤ α) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (estimate : ∀ n x, ‖(T ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖)
    (z : ℂ) (hz : α < ‖z‖) :
    FiniteDimensional ℂ (T - z • 1).ker ∧
      ∀ n : ℕ, IsClosed (((T - z • 1) ^ n).range : Set E) := by
  obtain ⟨A, B, hA, hB, hbound⟩ :=
    TwoNormSpectralShift.exists_annulus_bound T i α R C D ‖z‖ ‖z‖
      hα hR hD hz (norm_nonneg z) estimate
  have bound := hbound z le_rfl le_rfl
  have peetre : ∀ x, ‖x‖ ≤ B * ‖(T - z • 1) x‖ + A * ‖i x‖ := by
    intro x
    simpa only [add_comm] using bound x
  exact ⟨CompactEstimateClosedRange.finite_kernel (T - z • 1) i hi B A hA peetre,
    closed_range_powers (T - z • 1) i hi B A hB hA peetre⟩

end LeanShared.CompactTwoNormClosedRange
