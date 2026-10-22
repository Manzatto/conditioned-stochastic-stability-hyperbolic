module

public import LeanShared.Geometry.SupportedSmoothDensity

/-! Ambient smooth real observables form a constructed dense test set on any
closed live set. This concerns uniform C0 approximation, including boundary
values, and asserts no density in a big Hölder space. -/

@[expose] public noncomputable section
open Set Function
open scoped Manifold ContDiff BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.SmoothPhysicalTests
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  (K : Set M) [CompactSpace K]

def tests : Set (K →ᵇ ℝ) := {h | ∃ f : M → ℝ,
  ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) ∞ f ∧ ∀ x : K, h x = f x.val}

include E in
theorem dense (hK : IsClosed K) : Dense (tests (E := E) K) := by
  intro f
  let fc : C(K, ℝ) := ⟨f, f.continuous⟩
  obtain ⟨F, hF⟩ := fc.exists_restrict_eq hK
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨g, happrox, _⟩ := F.continuous.exists_contMDiff_approx
    (𝓘(ℝ, E)) (⊤ : ℕ∞) (ε := fun _ => ε / 2) continuous_const (fun _ => half_pos hε)
  let b : K →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x : K => g x.val, g.contMDiff.continuous.comp continuous_subtype_val⟩
  refine ⟨b, ⟨g, g.contMDiff, fun _ => rfl⟩, ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt ((BoundedContinuousFunction.norm_le (le_of_lt (half_pos hε))).mpr ?_)
    (half_lt_self hε)
  intro x
  have hx := congrArg (fun q : C(K, ℝ) => q x) hF
  change F x.val = f x at hx
  change ‖f x - g x.val‖ ≤ ε / 2
  rw [← hx, ← dist_eq_norm, dist_comm]
  exact (happrox x.val).le

def extension (h : tests (E := E) K) : M → ℝ := Classical.choose h.property

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] [CompactSpace K] in
theorem extension_smooth (h : tests (E := E) K) :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) ∞ (extension K h) := (Classical.choose_spec h.property).1

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] [CompactSpace K] in
theorem extension_live (h : tests (E := E) K) (x : K) : extension K h x.val = h.val x :=
  ((Classical.choose_spec h.property).2 x).symm

def complexExtension (h : tests (E := E) K) : M → ℂ := fun x => (extension K h x : ℂ)

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] [CompactSpace K] in
theorem complexExtension_smooth (h : tests (E := E) K) :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ (complexExtension K h) := by
  exact Complex.ofRealCLM.contMDiff.comp (extension_smooth K h)

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] [CompactSpace K] in
theorem complexExtension_live (h : tests (E := E) K) (x : K) :
    complexExtension K h x.val = (h.val x : ℂ) := by rw [complexExtension, extension_live]

end ConditionedStochasticStabilityHyperbolic.SmoothPhysicalTests
