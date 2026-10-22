module
public import LeanShared.Geometry.SmoothImmersionReferenceMetric

/-! A canonical reference inner product is constructed from Mathlib's actual
compact-manifold Whitney immersion. No Euclidean immersion or metric is
an input. The original supplied metric is retained separately. -/
public noncomputable section
namespace LeanShared.CanonicalSmoothReferenceMetric
open Set Manifold Bundle
open scoped Topology Manifold ContDiff Bundle
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold (𝓘(ℝ,E)) ∞ M]

structure Data where
  dimension : ℕ
  map : M → EuclideanSpace ℝ (Fin dimension)
  smooth : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,EuclideanSpace ℝ (Fin dimension))) ∞ map
  injective : ∀ x, Function.Injective
    (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,EuclideanSpace ℝ (Fin dimension))) map x)

/-- The immersion and its differential rank are proved by Mathlib's
finite smooth bump construction on the actual compact manifold. -/
def canonicalData : Data (E := E) (M := M) := Classical.choice (by
  obtain ⟨n,f,smooth,_embedding,injective⟩ :=
    exists_embedding_euclidean_of_compact (I := 𝓘(ℝ,E)) (M := M)
  exact ⟨⟨n,f,smooth,injective⟩⟩)

variable [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

/-- The genuine Euclidean pullback reference metric with its original
fiber topology, computed from the internally constructed immersion. -/
def metric : RiemannianMetric (fun x : M => TangentSpace (𝓘(ℝ,E)) x) :=
  SmoothImmersionReferenceMetric.pullbackMetric
    (canonicalData (E := E) (M := M)).map
    (canonicalData (E := E) (M := M)).injective

end LeanShared.CanonicalSmoothReferenceMetric
