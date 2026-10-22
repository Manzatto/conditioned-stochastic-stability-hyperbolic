module
public import LeanShared.Geometry.BoundedRiemannianFunctionLipschitz
public import LeanShared.Geometry.SmoothSupportedManifoldCore
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The smooth-core Holder certificate for the constructed bounded
Riemannian length metric is proved from actual smoothness. It need not be
supplied as a separate regularity assumption. -/
public noncomputable section
namespace LeanShared.BoundedRiemannianMetric
open Set Bundle IsManifold
open scoped Topology Manifold ContDiff Bundle NNReal

theorem smooth_core_holder
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T3Space M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    (u : ℝ) (hu : u ≤ 1) :
    let _ : MetricSpace M := metric (E := E)
    ∀ c : SmoothSupportedManifoldCore.core (E := E) (Set.univ : Set M),
      ∃ C : ℝ, ∀ x y,
        ‖SmoothSupportedManifoldCore.functions Set.univ c x-
          SmoothSupportedManifoldCore.functions Set.univ c y‖ ≤ C*dist x y^u := by
  let _ : MetricSpace M := metric (E := E)
  change ∀ c : SmoothSupportedManifoldCore.core (E := E) (Set.univ : Set M), _
  intro c
  obtain ⟨L,lip⟩ := function_exists_lipschitz (E := E) (SmoothSupportedManifoldCore.functions Set.univ c)
    ((SmoothSupportedManifoldCore.smooth Set.univ c).of_le (by simp))
  refine ⟨L,fun x y => ?_⟩
  have extended : edist x y ≤ (1 : ℝ≥0) := by
    rw [metric_edist (E := E) x y]
    exact min_le_right _ _
  have bounded : dist x y ≤ 1 := by exact_mod_cast (edist_le_coe.mp extended)
  have increment := lip.dist_le_mul x y
  have actual : ‖SmoothSupportedManifoldCore.functions Set.univ c x-
      SmoothSupportedManifoldCore.functions Set.univ c y‖ ≤ L*dist x y := by
    simpa only [dist_eq_norm] using increment
  exact actual.trans (mul_le_mul_of_nonneg_left
    (Real.self_le_rpow_of_le_one dist_nonneg bounded hu) L.coe_nonneg)

end LeanShared.BoundedRiemannianMetric
