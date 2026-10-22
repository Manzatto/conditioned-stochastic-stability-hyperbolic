module
public import LeanShared.Geometry.ImmersionPullbackInner
public import Mathlib.Geometry.Manifold.WhitneyEmbedding
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! Euclidean pullback inner products of genuine manifold immersions.
The differential is normalized to the Euclidean vector space explicitly;
positivity and compatibility with the original fiber topology are proved. -/
public noncomputable section
namespace LeanShared.SmoothImmersionReferenceMetric
open Bundle Manifold Set
open scoped Topology Manifold ContDiff Bundle
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) 1 M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

@[expose] def differential (f : M → F) (x : M) : TangentSpace (𝓘(ℝ,E)) x →L[ℝ] F :=
  (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)).toContinuousLinearMap.comp
    (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x)

/-- A genuine injective differential pulls the Euclidean inner product
back to a positive definite form with bounded original-topology unit ball. -/
@[expose] def pullbackMetric (f : M → F)
    (injective : ∀ x, Function.Injective (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x)) :
    RiemannianMetric (fun x : M => TangentSpace (𝓘(ℝ,E)) x) where
  inner x := ImmersionPullbackInner.form (H := TangentSpace (𝓘(ℝ,E)) x) (differential f x)
  symm x := ImmersionPullbackInner.symm (H := TangentSpace (𝓘(ℝ,E)) x) (differential f x)
  pos x := ImmersionPullbackInner.positive (H := TangentSpace (𝓘(ℝ,E)) x) (differential f x)
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)).injective.comp (injective x))
  continuousAt x := ((ImmersionPullbackInner.form (H := TangentSpace (𝓘(ℝ,E)) x) (differential f x)).continuous.clm_apply continuous_id).continuousAt
  isVonNBounded x := ImmersionPullbackInner.unit_isVonNBounded (H := TangentSpace (𝓘(ℝ,E)) x) (differential f x)
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)).injective.comp (injective x))

omit [IsManifold (𝓘(ℝ,E)) 1 M] in
/-- The actual reference inner product, without any unspecified metric
or supplied completed norm identity. -/
theorem pullbackMetric_inner (f : M → F)
    (injective : ∀ x, Function.Injective (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x))
    (x : M) (v w : TangentSpace (𝓘(ℝ,E)) x) :
    (pullbackMetric f injective).inner x v w =
      inner ℝ (differential f x v) (differential f x w) := rfl

end LeanShared.SmoothImmersionReferenceMetric
