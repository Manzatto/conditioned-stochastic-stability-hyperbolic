module
public import LeanShared.Geometry.SupportedChartHolderRegularity
public import LeanShared.Geometry.BoundedHolderCore
public import Mathlib.Analysis.Normed.Operator.Basic

/-! A concrete supported chart Hölder space and its actual inverse-chart
realization on the manifold. The realization has norm at most one; its
fractional regularity and support follow from the proved chart transport. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.SupportedHolderChartSpace
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
  {a : ℝ} (K : Set E)

@[expose] def space : Submodule ℂ (BoundedHolderSpace.graph E a) where
  carrier := {v | ∀ y ∉ K, BoundedHolderSpace.physical E a v y = 0}
  zero_mem' := by intro y _; simp
  add_mem' hf hg := by intro y hy; simp only [map_add, BoundedContinuousFunction.add_apply, hf y hy, hg y hy, add_zero]
  smul_mem' c f hf := by intro y hy; simp only [map_smul, BoundedContinuousFunction.smul_apply, hf y hy, smul_zero]

local instance holderGraphSeminormed : SeminormedAddCommGroup (BoundedHolderSpace.graph E a) :=
  (inferInstance : NormedAddCommGroup (BoundedHolderSpace.graph E a)).toSeminormedAddCommGroup

local instance supportedSeminormed : SeminormedAddCommGroup (space (a := a) K) :=
  (inferInstance : NormedAddCommGroup (space (a := a) K)).toSeminormedAddCommGroup

omit [NormedSpace ℝ E] in
theorem closed : IsClosed (space (a := a) K : Set (BoundedHolderSpace.graph E a)) := by
  have identity : (space (a := a) K : Set (BoundedHolderSpace.graph E a)) =
      ⋂ y, ⋂ (_ : y ∉ K), {v | BoundedHolderSpace.physical E a v y = 0} := by
    ext v
    simp [space]
  rw [identity]
  apply isClosed_iInter
  intro y
  apply isClosed_iInter
  intro _
  exact isClosed_eq ((BoundedContinuousFunction.evalCLM ℂ y).continuous.comp
    (BoundedHolderSpace.physical E a).continuous) continuous_const

instance complete : CompleteSpace (space (a := a) K) := (closed K).completeSpace_coe

variable {K} (hK : IsCompact K)

include hK in
omit [NormedSpace ℝ E] in
theorem support (v : space (a := a) K) :
    tsupport (fun y => BoundedHolderSpace.physical E a v.val y) ⊆ K := by
  apply closure_minimal _ hK.isClosed
  intro y hy
  by_contra hn
  exact hy (v.property y hn)

include hK in
omit [NormedSpace ℝ E] in
theorem compact_support (v : space (a := a) K) :
    HasCompactSupport (fun y => BoundedHolderSpace.physical E a v.val y) :=
  hK.of_isClosed_subset (isClosed_tsupport _) (support hK v)

variable (e : OpenPartialHomeomorph M E) (target : K ⊆ e.target)

@[expose] def physical (v : space (a := a) K) : M →ᵇ ℂ :=
  ofCompactSupport
    (SupportedChartExtension.function e (fun y => BoundedHolderSpace.physical E a v.val y))
    (SupportedChartExtension.continuous e (BoundedHolderSpace.physical E a v.val).continuous
      (compact_support hK v) ((support hK v).trans target))
    (SupportedChartExtension.compact_support e (compact_support hK v) ((support hK v).trans target))

omit [NormedSpace ℝ E] [ChartedSpace E M] in
theorem norm_physical (v : space (a := a) K) : ‖physical hK e target v‖ ≤ ‖v‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg v)).mpr
  intro x
  change ‖SupportedChartExtension.function e _ x‖ ≤ ‖v‖
  by_cases hx : x ∈ e.source
  · rw [SupportedChartExtension.function, ite_eq_left hx]
    exact ((BoundedHolderSpace.physical E a v.val).norm_coe_le_norm (e x)).trans
      (BoundedHolderSpace.physical_norm_le E a v.val)
  · rw [SupportedChartExtension.function, ite_eq_right hx, norm_zero]
    exact norm_nonneg v

@[expose] def realization : space (a := a) K →L[ℂ] (M →ᵇ ℂ) :=
  LinearMap.mkContinuous
    { toFun := physical hK e target
      map_add' := by
        classical
        intro v w
        ext x
        change (if x ∈ e.source then BoundedHolderSpace.physical E a (v.val + w.val) (e x) else 0) =
          (if x ∈ e.source then BoundedHolderSpace.physical E a v.val (e x) else 0) +
          (if x ∈ e.source then BoundedHolderSpace.physical E a w.val (e x) else 0)
        split_ifs <;> simp only [map_add, BoundedContinuousFunction.add_apply, zero_add]
      map_smul' := by
        classical
        intro c v
        ext x
        change (if x ∈ e.source then BoundedHolderSpace.physical E a (c • v.val) (e x) else 0) =
          c • (if x ∈ e.source then BoundedHolderSpace.physical E a v.val (e x) else 0)
        split_ifs <;> simp only [map_smul, BoundedContinuousFunction.smul_apply, smul_zero] }
    1 (fun v => by
      change ‖physical hK e target v‖ ≤ 1 * ‖v‖
      simpa only [one_mul] using norm_physical hK e target v)

omit [NormedSpace ℝ E] [ChartedSpace E M] in
theorem realization_norm : ‖realization (E := E) (M := M) (a := a) hK e target‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun v => by
      change ‖physical hK e target v‖ ≤ 1 * ‖v‖
      simpa only [one_mul] using norm_physical hK e target v)

omit [NormedSpace ℝ E] [ChartedSpace E M] in
theorem realization_support (v : space (a := a) K) :
    tsupport (fun x => realization hK e target v x) ⊆ e.symm '' K :=
  (SupportedChartExtension.support_subset e (compact_support hK v)
    ((support hK v).trans target)).trans (image_mono (support hK v))

theorem realization_regular [IsManifold (𝓘(ℝ,E)) ∞ M]
    (he : e ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (ha : 0 < a) (ha1 : a < 1)
    (v : space (a := a) K) :
    FractionalManifoldRegularity.Regular (E := E) (F := ℂ) a
      (fun x => realization hK e target v x) :=
  SupportedChartExtension.graph_regular e he ha ha1 v.val
    (compact_support hK v) ((support hK v).trans target)
end LeanShared.SupportedHolderChartSpace
