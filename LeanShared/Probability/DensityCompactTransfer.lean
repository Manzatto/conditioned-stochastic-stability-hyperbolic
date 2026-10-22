module

public import LeanShared.Probability.DensitySmoothing
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! # Compact continuous transfer from an actual bounded transition density -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped BoundedContinuousFunction Topology

namespace LeanShared.DensityCompactTransfer

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {𝕜 : Type*} [RCLike 𝕜] [SecondCountableTopology 𝕜] [ProperSpace 𝕜]

theorem compact_of_bounded_continuous_density
    (P : (X →ᵇ 𝕜) →L[𝕜] (X →ᵇ 𝕜))
    (σ : Measure X) [IsFiniteMeasure σ] (q : X × X → ℝ) (hq : Measurable q)
    (M : ℝ) (hM : 0 ≤ M) (hqM : ∀ x y, ‖q (x, y)‖ ≤ M)
    (hc : ∀ᵐ y ∂σ, Continuous (fun x => q (x, y)))
    (hP : ∀ (f : X →ᵇ 𝕜) (x : X), P f x = ∫ y, q (x, y) • f y ∂σ) :
    IsCompactOperator P := by
  classical
  have hdiff (x z y : X) : ‖q (x, y) - q (z, y)‖ ≤ 2 * M := by
    exact (norm_sub_le (q (x, y)) (q (z, y))).trans (by linarith [hqM x y, hqM z y])
  have hint (x z : X) : Integrable (fun y => ‖q (x, y) - q (z, y)‖) σ :=
    Integrable.of_bound
      (((hq.comp (measurable_const.prodMk measurable_id)).sub
        (hq.comp (measurable_const.prodMk measurable_id))).norm.aestronglyMeasurable)
      (2 * M) (ae_of_all _ (fun y => by simpa only [norm_norm] using hdiff x z y))
  have hcont (x : X) : Continuous (fun z => ∫ y, ‖q (x, y) - q (z, y)‖ ∂σ) := by
    apply continuous_of_dominated (bound := fun _ : X => 2 * M)
    · intro z
      exact (((hq.comp (measurable_const.prodMk measurable_id)).sub
        (hq.comp (measurable_const.prodMk measurable_id))).norm.aestronglyMeasurable)
    · intro z
      exact ae_of_all _ (fun y => by simpa only [norm_norm] using hdiff x z y)
    · exact integrable_const _
    · filter_upwards [hc] with y hy
      exact (continuous_const.sub hy).norm
  have hbound (f : X →ᵇ 𝕜) (hf : ‖f‖ ≤ 1) (x z : X) :
      dist (P f x) (P f z) ≤ ∫ y, ‖q (x, y) - q (z, y)‖ ∂σ := by
    have hi (x : X) : Integrable (fun y => q (x, y) • f y) σ := by
      apply Integrable.of_bound
        (((hq.comp (measurable_const.prodMk measurable_id)).smul f.continuous.measurable).aestronglyMeasurable)
        (M * ‖f‖)
      exact ae_of_all _ (fun y => by
        change ‖q (x, y) • f y‖ ≤ M * ‖f‖
        rw [norm_smul]
        exact mul_le_mul (hqM x y) (f.norm_coe_le_norm y) (norm_nonneg _) hM)
    rw [dist_eq_norm, hP, hP, ← integral_sub (hi x) (hi z)]
    have he : (fun y => q (x, y) • f y - q (z, y) • f y) =
        (fun y => (q (x, y) - q (z, y)) • f y) := by
      funext y
      rw [sub_smul]
    rw [he]
    apply norm_integral_le_of_norm_le (hint x z)
    exact ae_of_all _ (fun y => by
      rw [norm_smul]
      exact mul_le_of_le_one_right (norm_nonneg _) ((f.norm_coe_le_norm y).trans hf))
  let A := P '' closedBall (0 : X →ᵇ 𝕜) 1
  have hcompact : IsCompact (closure A) := by
    apply BoundedContinuousFunction.arzela_ascoli (closedBall (0 : 𝕜) ‖P‖)
      (isCompact_closedBall (0 : 𝕜) ‖P‖)
    · intro u x hu
      change u ∈ P '' closedBall (0 : X →ᵇ 𝕜) 1 at hu
      obtain ⟨f, hf, rfl⟩ := hu
      apply mem_closedBall_zero_iff.mpr
      exact ((P f).norm_coe_le_norm x).trans
        ((P.le_opNorm f).trans (mul_le_of_le_one_right (norm_nonneg P)
          (mem_closedBall_zero_iff.mp hf)))
    · intro x
      apply Metric.equicontinuousAt_iff_right.mpr
      intro ε hε
      have hz : (∫ y, ‖q (x, y) - q (x, y)‖ ∂σ) < ε := by simpa using hε
      have he := (hcont x).continuousAt.eventually (gt_mem_nhds hz)
      filter_upwards [he] with z hz
      intro u
      have hu : u.val ∈ P '' closedBall (0 : X →ᵇ 𝕜) 1 := u.property
      obtain ⟨f, hf, hfu⟩ := hu
      change dist (u.val x) (u.val z) < ε
      rw [← hfu]
      exact (hbound f (mem_closedBall_zero_iff.mp hf) x z).trans_lt hz
  exact (isCompactOperator_iff_image_closedBall_subset_compact P.toLinearMap (r := 1) (by norm_num)).mpr
    ⟨closure A, hcompact, subset_closure⟩

end LeanShared.DensityCompactTransfer
