module

public import LeanShared.Analysis.CompactTwoNormAscent
public import LeanShared.Analysis.CompactTwoNormDescent
public import LeanShared.LinearAlgebra.FiniteFittingDecomposition
public import Mathlib.Analysis.Normed.Module.Complemented

/-! Actual finite-dimensional spectral decomposition outside the strong
growth disk, derived from compact inclusion and Lasota–Yorke estimates. -/

public section
open ContinuousLinearMap Submodule
namespace LeanShared.CompactTwoNormDecomposition
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Every spectral shift outside the strong growth disk has a finite-dimensional
stabilized generalized kernel and a closed, topologically complementary
stabilized range. No decomposition or Fredholm theorem is a source premise. -/
theorem exists_decomposition (T : E →L[ℂ] E) (i : E →L[ℂ] W)
    (hi : IsCompactOperator i) (α R C D : ℝ)
    (hα : 0 ≤ α) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (estimate : ∀ n x, ‖(T ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖)
    (z : ℂ) (hz : α < ‖z‖) :
    ∃ n : ℕ, FiniteDimensional ℂ ((T - z • 1) ^ n).ker ∧
      IsTopCompl ((T - z • 1) ^ n).ker ((T - z • 1) ^ n).range ∧
      (∀ m : ℕ, ((T - z • 1) ^ (n + m)).ker = ((T - z • 1) ^ n).ker) ∧
      (∀ m : ℕ, ((T - z • 1) ^ (n + m)).range = ((T - z • 1) ^ n).range) := by
  let S := T - z • (1 : E →L[ℂ] E)
  have ascent := CompactTwoNormAscent.finite_ascent T i hi α R C D hα hR hC hD estimate z hz
  have descent := CompactTwoNormDescent.finite_descent T i hi α R C D hα hR hC hD estimate z hz
  have ascentL : ∃ n : ℕ, ((S : Module.End ℂ E) ^ n).ker =
      ((S : Module.End ℂ E) ^ (n + 1)).ker := by
    simpa only [← toLinearMap_pow] using ascent
  have descentL : ∃ n : ℕ, ((S : Module.End ℂ E) ^ n).range =
      ((S : Module.End ℂ E) ^ (n + 1)).range := by
    simpa only [← toLinearMap_pow] using descent
  obtain ⟨n, complL, kerL, rangeL⟩ :=
    FiniteFittingDecomposition.exists_decomposition (S : Module.End ℂ E) ascentL descentL
  have first : FiniteDimensional ℂ S.ker :=
    (CompactTwoNormClosedRange.spectral_shift T i hi α R C D hα hR hD estimate z hz).1
  let _ : FiniteDimensional ℂ (S : Module.End ℂ E).ker := first
  have finite := FiniteKernelPowers.finiteDimensional (S : Module.End ℂ E) n
  have equality : ((S : Module.End ℂ E) ^ n).ker = (S ^ n).ker :=
    congrArg LinearMap.ker (toLinearMap_pow S n).symm
  rw [equality] at finite
  have compl : IsCompl (S ^ n).ker (S ^ n).range := by
    simpa only [← toLinearMap_pow] using complL
  have rangeClosed : IsClosed ((S ^ n).range : Set E) :=
    (CompactTwoNormClosedRange.spectral_shift T i hi α R C D hα hR hD estimate z hz).2 n
  refine ⟨n, finite, compl.isTopCompl_of_isClosed (S ^ n).isClosed_ker rangeClosed, ?_, ?_⟩
  · intro m
    simpa only [← toLinearMap_pow] using kerL m
  · intro m
    simpa only [← toLinearMap_pow] using rangeL m

end LeanShared.CompactTwoNormDecomposition
