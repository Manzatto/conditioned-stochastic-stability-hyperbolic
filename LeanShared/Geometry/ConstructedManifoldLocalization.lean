module

public import LeanShared.Geometry.CompactChartPartition
public import LeanShared.Analysis.FiniteChartCompletion

/-!
# Genuine finite manifold localization and its literal completed chart norm

A covering smooth atlas on a compact manifold selects a finite subcover and
constructs a subordinate smooth partition. Its cutoff coordinate formula
produces the supported Schwartz core maps used by the physical local
compact-embedding theorem. The resulting global completed norm is exactly
the maximum of the specified local norms, applied to these genuine
coordinates. No global localization map or norm identity is assumed.
-/

@[expose] public noncomputable section

open Set IsManifold
open scoped Manifold ContDiff SchwartzMap BigOperators NNReal
attribute [local instance] Classical.propDecidable

namespace LeanShared.ConstructedManifoldLocalization

variable {E M J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]

/-- All finite partition fields are produced from compactness and the
smooth partition theorem; only the genuine adapted chart cover is input. -/
structure Data (e : J → OpenPartialHomeomorph M E) (S : Set M) where
  indices : Finset J
  cutoff : indices → M → ℂ
  smooth : ∀ i, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ (cutoff i)
  support : ∀ i, tsupport (cutoff i) ⊆ (e i).source
  compact : ∀ i, HasCompactSupport (cutoff i)
  partition : ∀ x ∈ S, ∑ i, cutoff i x = 1

variable (e : J → OpenPartialHomeomorph M E) {S : Set M}

def data (compact : IsCompact S) (cover : S ⊆ ⋃ j, (e j).source) : Data e S := Classical.choice (by
  classical
  obtain ⟨s, θ, hθ, hs, hc, hp⟩ := CompactChartPartition.exists_finite_partition
    e S compact cover
  exact ⟨⟨s, θ, hθ, hs, hc, hp⟩⟩)

variable (D : Data e S) (he : ∀ j, e j ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
  {Core : Type*} [AddCommGroup Core] [Module ℂ Core]
  (functions : Core →ₗ[ℂ] (M → ℂ))
  (smooth : ∀ f : Core, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ (functions f))

/-- The compact local support is the actual chart image of the chosen cutoff. -/
def support (i : D.indices) : Set E := ChartLocalization.localSupport (e i) (D.cutoff i)

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
theorem support_compact (i : D.indices) : IsCompact (support e D i) :=
  ChartLocalization.localSupport_isCompact (e i) (D.cutoff i) (D.support i) (D.compact i)

/-- The literal supported smooth coordinates, with zero extension proved
smooth across each genuine chart boundary. -/
def localize (i : D.indices) : Core →ₗ[ℂ] SchwartzJetSpace.supportedCore (support e D i) :=
  FiniteChartLocalization.localize (fun i : D.indices => e i) D.cutoff D.support
    (fun i => he i) D.smooth functions smooth D.compact i

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
@[simp] theorem localize_apply (i : D.indices) (f : Core) (x : M)
    (hx : x ∈ (e i).source) :
    (localize e D he functions smooth i f).val (e i x) = D.cutoff i x * functions f x :=
  FiniteChartLocalization.localize_chart (fun i : D.indices => e i) D.cutoff D.support
    (fun i => he i) D.smooth functions smooth D.compact i f x hx

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
/-- The actual cutoff partition reconstructs every supported global smooth function. -/
theorem reconstruct (f : Core) (x : M) (hx : x ∈ S) :
    (∑ i : D.indices, if x ∈ (e i).source then
      (localize e D he functions smooth i f).val (e i x) else 0) = functions f x :=
  FiniteChartLocalization.reconstruct (fun i : D.indices => e i) D.cutoff D.support
    (fun i => he i) D.smooth functions smooth D.compact S D.partition f x hx

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
/-- In particular the genuine Schwartz chart coordinates faithfully
represent the global smooth core before completion. -/
theorem localize_injective (hfunctions : Function.Injective functions)
    (hzero : ∀ f : Core, ∀ x ∉ S, functions f x = 0) :
    Function.Injective (LinearMap.pi (localize e D he functions smooth)) :=
  FiniteChartLocalization.chartMap_injective (fun i : D.indices => e i) D.cutoff D.support
    (fun i => he i) D.smooth functions smooth D.compact S D.partition hzero hfunctions

variable {B : D.indices → Type*} [∀ i, NormedAddCommGroup (B i)] [∀ i, NormedSpace ℂ (B i)]
  (blocks : ∀ i, SchwartzJetSpace.supportedCore (support e D i) →ₗ[ℂ] B i)

/-- Applying the literal local physical Fourier/leaf blocks gives the
manuscript's global finite maximum chart norm on the common smooth core. -/
def chartCore : Core →ₗ[ℂ] (∀ i, B i) :=
  LinearMap.pi fun i => (blocks i).comp (localize e D he functions smooth i)

abbrev Space := DyadicCompletion.closedCore (chartCore e D he functions smooth blocks)

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
theorem norm_core (f : Core) :
    ‖DyadicCompletion.coreLift (chartCore e D he functions smooth blocks) f‖ =
      ((Finset.univ.sup (fun i => ‖blocks i (localize e D he functions smooth i f)‖₊) : ℝ≥0) : ℝ) := rfl

end LeanShared.ConstructedManifoldLocalization
