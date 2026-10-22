module

public import LeanShared.Analysis.TwoNormSpectralShift
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Tactic.Linarith

/-! Finite-dimensionality of eigenspaces outside the strong growth disk,
proved from compact weak inclusion and the actual two-norm power estimate. -/

public section
open Filter Topology ContinuousLinearMap
namespace LeanShared.CompactTwoNormEigenSpace
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- A compact bounded-below linear map can have only a finite-dimensional
Banach domain. This is proved by pulling back a compact neighbourhood. -/
theorem finiteDimensional_of_compact_bound (i : E →L[ℂ] W) (hi : IsCompactOperator i)
    (A : ℝ) (hA : 0 ≤ A) (bound : ∀ x : E, ‖x‖ ≤ A * ‖i x‖) :
    FiniteDimensional ℂ E := by
  have anti : ∃ K, AntilipschitzWith K i := by
    rw [antilipschitzWith_iff_exists_mul_le_norm]
    refine ⟨(A + 1)⁻¹, by positivity, fun x => ?_⟩
    rw [inv_mul_eq_div, div_le_iff₀ (by positivity : 0 < A + 1)]
    nlinarith [bound x, norm_nonneg (i x)]
  obtain ⟨Kanti, hanti⟩ := anti
  obtain ⟨K, hK, hneighbourhood⟩ := hi
  apply FiniteDimensional.of_isCompactOperator_id
  exact ⟨i ⁻¹' K, (hanti.isClosedEmbedding i.uniformContinuous).isCompact_preimage hK, hneighbourhood⟩

/-- The spectral kernel is finite dimensional at every value above the
strong growth rate. No Fredholm or discrete-spectrum source is assumed. -/
theorem finiteDimensional_spectralKernel (T : E →L[ℂ] E) (i : E →L[ℂ] W)
    (hi : IsCompactOperator i) (α R C D : ℝ)
    (hα : 0 ≤ α) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (estimate : ∀ n x, ‖(T ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖)
    (z : ℂ) (hz : α < ‖z‖) :
    FiniteDimensional ℂ (T - z • (1 : E →L[ℂ] E)).ker := by
  let S := T - z • (1 : E →L[ℂ] E)
  let V := S.ker
  let : CompleteSpace V := S.isClosed_ker.isComplete.completeSpace_coe
  let j : V →L[ℂ] W := i.comp V.subtypeL
  have hj : IsCompactOperator j := hi.comp_clm V.subtypeL
  let r := (α + ‖z‖) / 2
  have hr : α < r := by dsimp [r]; linarith
  obtain ⟨A, B, hA, _, hb⟩ := TwoNormSpectralShift.exists_annulus_bound T i α R C D r ‖z‖
    hα hR hD hr (norm_nonneg z) estimate
  apply finiteDimensional_of_compact_bound j hj A hA
  intro v
  have hzero : S v.val = 0 := v.property
  have hh := hb z (by dsimp [r]; linarith) le_rfl v.val
  change ‖v.val‖ ≤ A * ‖i v.val‖
  change ‖v.val‖ ≤ A * ‖i v.val‖ + B * ‖S v.val‖ at hh
  simpa only [hzero, norm_zero, mul_zero, add_zero] using hh

end LeanShared.CompactTwoNormEigenSpace
