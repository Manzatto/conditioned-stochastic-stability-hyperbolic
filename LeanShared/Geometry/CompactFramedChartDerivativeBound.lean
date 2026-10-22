module
public import LeanShared.Geometry.CenteredAtlasCoordinates
public import LeanShared.Analysis.CenteredFrameDerivative
public import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linarith

/-! The actual C1 chart map gives a uniform bound on its derivative in any
bounded pair of frames, over a compact valid set of source centers. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace LeanShared.CompactFramedChartDerivativeBound
open CenteredManifoldCoordinates
variable {E M P Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [TopologicalSpace M] [ChartedSpace E M]

theorem uniform_bound (H : M → M) (smooth : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 H)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
    (K : Set M) (compact : IsCompact K) (inside : K ⊆ c.source)
    (target : MapsTo H K d.source) (C : ℝ) (positiveC : 0 < C) :
    ∃ B > 0, ∀ x ∈ K, ∀ (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] E),
      ‖L.toContinuousLinearMap‖ ≤ C → ‖R.symm.toContinuousLinearMap‖ ≤ C → ∀ b : E,
      ‖fderiv ℝ (centered L R (c x) b (d ∘ H ∘ c.symm)) 0‖ ≤ B := by
  have compactCenters : IsCompact (c '' K) := compact.image_of_continuousOn
    (c.continuousOn.mono inside)
  have rawSmooth : ∀ a ∈ c '' K, ContDiffAt ℝ 1 (d ∘ H ∘ c.symm) a := by
    rintro _ ⟨x, hx, rfl⟩
    have source : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 c.symm (c x) :=
      (contMDiffAt_symm_of_mem_maximalAtlas hc (c.map_source (inside hx))).of_le (by simp)
    have middle : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 H (c.symm (c x)) := by
      rw [c.left_inv (inside hx)]
      exact smooth.contMDiffAt
    have last : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 d (H (c.symm (c x))) := by
      rw [c.left_inv (inside hx)]
      exact (contMDiffAt_of_mem_maximalAtlas hd (target hx)).of_le (by simp)
    exact (last.comp (c x) (middle.comp (c x) source)).contDiffAt
  have continuousDerivative : ContinuousOn (fderiv ℝ (d ∘ H ∘ c.symm)) (c '' K) :=
    fun a ha => ((rawSmooth a ha).continuousAt_fderiv (by simp)).continuousWithinAt
  obtain ⟨D, positiveD, boundD⟩ :=
    (compactCenters.image_of_continuousOn continuousDerivative).isBounded.exists_pos_norm_le
  refine ⟨C ^ 2 * D + 1, by positivity, ?_⟩
  intro x hx L R boundL boundR b
  have rawBound := boundD _ ⟨c x, mem_image_of_mem c hx, rfl⟩
  rw [fderiv_centered, _root_.map_zero, add_zero]
  calc
    _ ≤ ‖R.symm.toContinuousLinearMap‖ *
        (‖fderiv ℝ (d ∘ H ∘ c.symm) (c x)‖ * ‖L.toContinuousLinearMap‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ C * (D * C) := mul_le_mul boundR
      (mul_le_mul rawBound boundL (norm_nonneg _) positiveD.le)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) positiveC.le
    _ ≤ C ^ 2 * D + 1 := by nlinarith

end LeanShared.CompactFramedChartDerivativeBound
