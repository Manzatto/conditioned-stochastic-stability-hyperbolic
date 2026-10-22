module

public import LeanShared.Dynamics.HyperbolicReferenceVolume
public import LeanShared.Geometry.CanonicalSmoothReferenceMetric
public import Mathlib.Topology.TietzeExtension
import Mathlib.Tactic.Ring

/-! The genuine supplied-metric potential is cohomologous to the genuine
smooth-reference potential. The transfer function is constructed by the
actual unstable volume ratio and Tietze extension; no volume coboundary or
reference immersion is supplied as background data. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set Bundle IsManifold
open scoped Topology Manifold ContDiff BoundedContinuousFunction
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

set_option maxHeartbeats 1600000 in
omit [CompactSpace M] in
theorem HyperbolicData.exists_reference_volume_coboundary (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (f : M → F) (smooth : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,F)) 1 f)
    (injective : ∀ x, Function.Injective (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x)) (g : M → ℝ) :
    ∃ u : M → ℝ, Continuous u ∧
      (∀ x ∈ Λ, u x = - Real.log (h.referenceUnstableVolume f x)) ∧
      ∀ x ∈ Λ, h.potential g x =
        (Real.log (g x) - Real.log (h.referenceUnstableJacobian f x)) + u x - u (T x) := by
  let _ : CompactSpace Λ := isCompact_iff_compactSpace.mp h.compact
  have volumeContinuous := h.continuousOn_referenceUnstableVolume f smooth
  have logContinuous : ContinuousOn (fun x => Real.log (h.referenceUnstableVolume f x)) Λ :=
    volumeContinuous.log (fun x _ => (h.referenceUnstableVolume_positive f injective x).ne')
  let v : Λ →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨(fun x => -Real.log (h.referenceUnstableVolume f x.val)), logContinuous.neg.domRestrict⟩
  obtain ⟨u, _, extension⟩ := v.exists_extension_norm_eq_of_isClosedEmbedding
    h.compact.isClosed.isClosedEmbedding_subtypeVal
  have same (x : M) (hx : x ∈ Λ) : u x = -Real.log (h.referenceUnstableVolume f x) :=
    congrFun extension ⟨x, hx⟩
  refine ⟨u, u.continuous, same, ?_⟩
  intro x hx
  have image : T x ∈ Λ := h.invariant ▸ mem_image_of_mem T hx
  change Real.log (g x) - Real.log (h.unstableJacobian x) = _
  rw [same x hx, same (T x) image, h.log_referenceUnstableJacobian forward inverse f injective x hx]
  ring

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
theorem HyperbolicData.exists_canonical_reference_coboundary (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm) (g : M → ℝ) :
    ∃ u : M → ℝ, Continuous u ∧ ∀ x ∈ Λ, h.potential g x =
      (Real.log (g x) - Real.log (h.referenceUnstableJacobian
        (CanonicalSmoothReferenceMetric.canonicalData (E := E) (M := M)).map x)) + u x - u (T x) := by
  let d := CanonicalSmoothReferenceMetric.canonicalData (E := E) (M := M)
  obtain ⟨u, continuous, _, same⟩ := h.exists_reference_volume_coboundary forward inverse
    d.map (d.smooth.of_le (by simp)) d.injective g
  exact ⟨u, continuous, same⟩

end LeanShared.HyperbolicBasicSet
