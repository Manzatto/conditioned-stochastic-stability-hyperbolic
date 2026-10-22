module
public import LeanShared.Geometry.ConstructedManifoldLocalization
public import LeanShared.Geometry.LinearRechartedIdentity
public import LeanShared.Geometry.SmoothSupportedManifoldCore

/-! The actual finite smooth localization partition is retained under a
genuine linear model change. Its physical cutoffs and reconstruction are
unchanged, and local coordinates are the literal inverse composition. -/
@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace LeanShared.ConstructedManifoldLocalization
variable {E F M J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [T2Space M] [CompactSpace M]
  {S : Set M} (c : J → OpenPartialHomeomorph M E) (D : Data c S) (e : E ≃L[ℝ] F)

def Data.linearRechart :
    letI := LinearRechartedManifold.charts (M := M) e;
    Data (fun j => LinearRechartedManifold.chartImage e (c j)) S := by
  let := LinearRechartedManifold.charts (M := M) e
  refine { indices := D.indices
           cutoff := D.cutoff
           smooth := ?_
           support := ?_
           compact := D.compact
           partition := D.partition }
  · intro i
    exact (D.smooth i).comp (LinearRechartedManifold.identity_backward (M := M) e)
  · intro i x hx
    change x ∈ (c i).source ∧ e (c i x) ∈ (univ : Set F)
    exact ⟨D.support i hx,mem_univ _⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold (𝓘(ℝ,E)) ∞ M] [T2Space M] [CompactSpace M] [ChartedSpace E M] in
theorem coordinate_linearRechart (j : J) (θ f : M → ℂ) (z : F) :
    ChartLocalization.coordinate (LinearRechartedManifold.chartImage e (c j)) θ f z =
      ChartLocalization.coordinate (c j) θ f (e.symm z) := by
  classical
  simp only [ChartLocalization.coordinate,LinearRechartedManifold.chartImage,mfld_simps,ContinuousLinearEquiv.coe_symm_toHomeomorph]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold (𝓘(ℝ,E)) ∞ M] [T2Space M] [CompactSpace M] [ChartedSpace E M] in
theorem localSupport_linearRechart (j : J) (θ : M → ℂ) :
    ChartLocalization.localSupport (LinearRechartedManifold.chartImage e (c j)) θ =
      e '' ChartLocalization.localSupport (c j) θ := by
  change (fun x => e (c j x)) '' tsupport θ = e '' ((c j) '' tsupport θ)
  rw [image_image]

def rechartCore (V : Set M) :
    letI := LinearRechartedManifold.charts (M := M) e;
    SmoothSupportedManifoldCore.core (E := E) V →ₗ[ℂ]
      SmoothSupportedManifoldCore.core (E := F) V := by
  let := LinearRechartedManifold.charts (M := M) e
  exact {
    toFun := fun f => ⟨f.val,f.property.1.comp (LinearRechartedManifold.identity_backward (M := M) e),f.property.2⟩
    map_add' := fun f g => Subtype.ext rfl
    map_smul' := fun z f => Subtype.ext rfl }

end LeanShared.ConstructedManifoldLocalization
