module

public import LeanShared.Geometry.RetainedRegularPairing

/-! Faithful distribution pairing on the closed retained region. Boundary values
are determined by continuity from the open region; reference mass on the boundary
is not required. -/

@[expose] public noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.RetainedRegularTests
variable {E M Reg : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  (U : Opens M) (V K : Set M) [CompactSpace K]

def closedRetained : Set K := {x | x.val ∈ closure (U : Set M)}

def closureHomeomorph (hcl : closure (U : Set M) ⊆ K) :
    closure (U : Set M) ≃ₜ closedRetained U K where
  toFun x := ⟨⟨x.val, hcl x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def intoClosed (hcl : closure (U : Set M) ⊆ K) : C(U, closedRetained U K) :=
  ⟨fun x => ⟨⟨x.val, hcl (subset_closure x.property)⟩, subset_closure x.property⟩,
    by fun_prop⟩

omit [FiniteDimensional ℝ E] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace K] in
theorem intoClosed_dense (hcl : closure (U : Set M) ⊆ K) :
    DenseRange (intoClosed U K hcl) := by
  exact (closureHomeomorph U K hcl).surjective.denseRange.comp
    ((denseRange_inclusion_iff (subset_closure : (U : Set M) ⊆ closure (U : Set M))).2
      Subset.rfl)
    (closureHomeomorph U K hcl).continuous_toFun

variable (q : SmoothSupportedManifoldCore.core (E := E) V →ₗ[ℂ] Reg)
  (hUV : (U : Set M) ⊆ V) (hcl : closure (U : Set M) ⊆ K)
  (p : Reg →L[ℂ] (K →ᵇ ℂ)) (σ : Measure K) [IsFiniteMeasure σ]

def closedRetainedEmbedding :
    (closedRetained U K →ᵇ ℂ) →L[ℂ] (space U V q hUV →L[ℂ] ℂ) :=
  (SupportedRegularPairing.embedding
    (reference U K (subset_closure.trans hcl) σ)
    (physical U V K q hUV (subset_closure.trans hcl) p)).comp
    (BoundedContinuousFunction.compContinuousCLM ℂ ℂ (intoClosed U K hcl))

variable (hp : ∀ c, p (q c) = SmoothSupportedManifoldCore.physicalCore V K c)
include hp in
theorem closedRetainedEmbedding_injective
    (positive : ∀ x : K, x.val ∈ (U : Set M) → x ∈ σ.support) :
    Function.Injective (closedRetainedEmbedding U V K q hUV hcl p σ) := by
  let _ := (𝓘(ℝ, E)).locallyCompactSpace
  let _ := ChartedSpace.locallyCompactSpace E M
  let _ := (𝓘(ℝ, E)).secondCountableTopology
  let _ := ChartedSpace.secondCountable_of_sigmaCompact E M
  let _ := U.isOpen.locallyCompactSpace
  have faithful := SupportedRegularPairing.faithful_of_smooth_compact_tests
    (reference U K (subset_closure.trans hcl) σ)
    (reference_positive U K (subset_closure.trans hcl) σ positive)
    (physical U V K q hUV (subset_closure.trans hcl) p)
    (contains_smooth_compact_tests U V K q hUV (subset_closure.trans hcl) p hp)
  intro f g hfg
  have hh := faithful hfg
  apply BoundedContinuousFunction.ext
  intro x
  exact congrFun ((intoClosed_dense U K hcl).equalizer f.continuous g.continuous
    (funext (fun y => congrArg (fun k : U →ᵇ ℂ => k y) hh))) x

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M] in
include hp in
theorem closed_pairing_restriction :
    (restriction U V q hUV).comp (SupportedRegularPairing.embedding σ p) =
      (closedRetainedEmbedding U V K q hUV hcl p σ).comp
        (BoundedContinuousFunction.compContinuousCLM ℂ ℂ
          (⟨Subtype.val, continuous_subtype_val⟩ : C(closedRetained U K, K))) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ContinuousLinearMap.ext
  intro v
  change (∫ x : K, f x * p v.val x ∂σ) =
    ∫ x : U, f (intoK U K (subset_closure.trans hcl) x) *
      p v.val (intoK U K (subset_closure.trans hcl) x) ∂σ.comap (intoK U K (subset_closure.trans hcl))
  rw [OpenEmbeddingReference.integral_comap σ
    (intoK_openEmbedding U K (subset_closure.trans hcl)).measurableEmbedding
    (fun x : K => f x * p v.val x)]
  have image : range (intoK U K (subset_closure.trans hcl)) = retained U K := by
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
