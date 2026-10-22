module

public import LeanShared.Geometry.RetainedRegularTests
public import LeanShared.Probability.OpenEmbeddingReference

/-! Exact restriction of the actual integral distribution pairing to the
retained open set, with faithfulness from its genuine smooth tests. -/

@[expose] public noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.RetainedRegularTests
open SmoothSupportedManifoldCore DyadicCompletion
variable {E M Reg : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  (U : Opens M) (V K : Set M) [CompactSpace K]
  (q : core (E := E) V →ₗ[ℂ] Reg) (hUV : (U : Set M) ⊆ V)
  (hUK : (U : Set M) ⊆ K) (p : Reg →L[ℂ] (K →ᵇ ℂ))
  (σ : Measure K) [IsFiniteMeasure σ]

def reference : Measure U := σ.comap (intoK U K hUK)

instance reference_finite : IsFiniteMeasure (reference U K hUK σ) := by
  unfold reference
  infer_instance

def retainedEmbedding : (retained U K →ᵇ ℂ) →L[ℂ] (space U V q hUV →L[ℂ] ℂ) :=
  (SupportedRegularPairing.embedding (reference U K hUK σ) (physical U V K q hUV hUK p)).comp
    (BoundedContinuousFunction.compContinuousCLM ℂ ℂ (⟨retainedHomeomorph U K hUK, (retainedHomeomorph U K hUK).continuous_toFun⟩ : C(U, retained U K)))

include hUK in
omit [FiniteDimensional ℝ E] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [CompactSpace M] [CompactSpace K] [IsFiniteMeasure σ] in
theorem reference_positive
    (positive : ∀ x : K, x.val ∈ (U : Set M) → x ∈ σ.support) :
    ∀ x : U, x ∈ (reference U K hUK σ).support :=
  OpenEmbeddingReference.support_comap σ (intoK_openEmbedding U K hUK)
    (fun x => positive (intoK U K hUK x) x.property)

variable (hp : ∀ c, p (q c) = physicalCore V K c)

include hp in
theorem retainedEmbedding_injective
    (positive : ∀ x : K, x.val ∈ (U : Set M) → x ∈ σ.support) :
    Function.Injective (retainedEmbedding U V K q hUV hUK p σ) := by
  let _ := (𝓘(ℝ, E)).locallyCompactSpace
  let _ := ChartedSpace.locallyCompactSpace E M
  let _ := (𝓘(ℝ, E)).secondCountableTopology
  let _ := ChartedSpace.secondCountable_of_sigmaCompact E M
  let _ := U.isOpen.locallyCompactSpace
  have faithful := SupportedRegularPairing.faithful_of_smooth_compact_tests
    (reference U K hUK σ) (reference_positive U K hUK σ positive)
    (physical U V K q hUV hUK p)
    (contains_smooth_compact_tests U V K q hUV hUK p hp)
  intro f g hfg
  have h := faithful hfg
  ext x
  obtain ⟨u, rfl⟩ := (retainedHomeomorph U K hUK).surjective x
  exact congrArg (fun k : U →ᵇ ℂ => k u) h

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M] in
include hp in
theorem pairing_restriction :
    (restriction U V q hUV).comp (SupportedRegularPairing.embedding σ p) =
      (retainedEmbedding U V K q hUV hUK p σ).comp
        (BoundedContinuousFunction.compContinuousCLM ℂ ℂ
          (⟨Subtype.val, continuous_subtype_val⟩ : C(retained U K, K))) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ContinuousLinearMap.ext
  intro v
  change (∫ x : K, f x * p v.val x ∂σ) =
    ∫ x : U, f (intoK U K hUK x) * p v.val (intoK U K hUK x) ∂σ.comap (intoK U K hUK)
  rw [OpenEmbeddingReference.integral_comap σ (intoK_openEmbedding U K hUK).measurableEmbedding
    (fun x : K => f x * p v.val x)]
  have image : range (intoK U K hUK) = retained U K := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact u.property
    · intro hx
      exact ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩
  rw [image]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  change f x * p v.val x = 0
  rw [zero_outside U V K q hUV p hp v x hx, mul_zero]

end LeanShared.RetainedRegularTests
