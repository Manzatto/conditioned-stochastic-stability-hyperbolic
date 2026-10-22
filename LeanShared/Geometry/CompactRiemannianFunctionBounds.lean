module
public import LeanShared.Geometry.CompactRiemannianBundleMaps
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.Riemannian.Basic

/-! Actual compact derivative bounds for vector-valued C1 functions,
with the native continuous Riemannian norm on the source tangent fibers. -/
public noncomputable section
namespace LeanShared.CompactRiemannianFunctionBounds
open Set Bundle IsManifold
open scoped Topology Manifold ContDiff Bundle

theorem exists_norm_bound
    {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    (f : M → F) (smooth : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,F)) 1 f)
    (K : Set M) (compact : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ‖mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x‖ ≤ C := by
  let A := fun x => (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)).toContinuousLinearMap.comp
    (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x)
  have continuous : Continuous (fun v : TotalSpace E (TangentSpace (𝓘(ℝ,E))) => A v.proj v.2) := by
    have out := (tangentBundleModelSpaceHomeomorph (𝓘(ℝ,F))).continuous.snd.comp
      (smooth.continuous_tangentMap (by simp))
    exact out
  obtain ⟨C,hC,bound⟩ := CompactRiemannianBundleMaps.to_fixed (F := E) (TangentSpace (𝓘(ℝ,E)))
    K compact A continuous.continuousOn
  refine ⟨C,hC,fun x hx => ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ hC.le
  intro v
  have actual := ((A x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (bound x hx) (norm_nonneg v))
  have same : ‖(mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x) v‖ = ‖A x v‖ := by
    rw [norm_tangentSpace_vectorSpace]
    rfl
  rw [same]
  exact actual

end LeanShared.CompactRiemannianFunctionBounds
