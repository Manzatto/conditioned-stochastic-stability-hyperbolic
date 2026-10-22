module

public import LeanShared.Analysis.CompactTwoNormDecomposition
public import LeanShared.Analysis.MeromorphicFittingResolvent

/-! The actual resolvent is meromorphic outside the strong Lasota–Yorke
rate. The finite-dimensional Fitting splitting and Laurent expansion are
constructed from the estimates, rather than supplied as source contracts. -/

public section
open ContinuousLinearMap
namespace LeanShared.CompactTwoNormMeromorphicResolvent

/-- Exact translation law for the actual resolvent, including spectral points. -/
theorem shift_formula {A : Type*} [Ring A] [Algebra ℂ A]
    (T : A) (c u : ℂ) :
    resolvent (T - c • 1) u = resolvent T (u + c) := by
  unfold resolvent
  congr 1
  simp only [Algebra.algebraMap_eq_smul_one, add_smul]
  abel

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Compact weak inclusion and the actual all-power Lasota–Yorke estimate
imply meromorphy of the actual resolvent at every point outside the strong disk. -/
theorem meromorphicAt (T : E →L[ℂ] E) (i : E →L[ℂ] W)
    (hi : IsCompactOperator i) (α R C D : ℝ)
    (hα : 0 ≤ α) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (estimate : ∀ n x, ‖(T ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖)
    (z : ℂ) (hz : α < ‖z‖) : MeromorphicAt (resolvent T) z := by
  obtain ⟨n, _, compl, kernels, ranges⟩ :=
    CompactTwoNormDecomposition.exists_decomposition T i hi α R C D hα hR hC hD estimate z hz
  have shifted := MeromorphicFittingResolvent.meromorphicAt_zero
    (T - z • 1) n compl (kernels 1) (ranges 1)
  have translated : MeromorphicAt ((resolvent (T - z • 1)) ∘ (· - z)) z :=
    meromorphicAt_comp_sub_const_iff_meromorphicAt.mpr (by simpa only [sub_self] using shifted)
  have eqfun : ((resolvent (T - z • 1)) ∘ (· - z)) = resolvent T := by
    funext w
    simp only [Function.comp_apply, shift_formula, sub_add_cancel]
  rw [eqfun] at translated
  exact translated

/-- Meromorphy on the whole exterior disk, ready for the common-ambient
meromorphic identity theorem. -/
theorem meromorphicOn (T : E →L[ℂ] E) (i : E →L[ℂ] W)
    (hi : IsCompactOperator i) (α R C D : ℝ)
    (hα : 0 ≤ α) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (estimate : ∀ n x, ‖(T ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖) :
    MeromorphicOn (resolvent T) {z : ℂ | α < ‖z‖} :=
  fun z hz => meromorphicAt T i hi α R C D hα hR hC hD estimate z hz

end LeanShared.CompactTwoNormMeromorphicResolvent
