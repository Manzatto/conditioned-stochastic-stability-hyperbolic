module

public import LeanShared.Geometry.ChartLocalization

/-!
# Finite adapted-chart core map and reconstruction

The common smooth core is localized by the literal cutoff/coordinate
formula. A partition of unity reconstructs it on the region covered, and
the chart core map is injective for functions supported in that region.
The charts and smooth cutoffs are genuine manifold objects, not arbitrary
linear localization maps.
-/

@[expose] public noncomputable section

open Set IsManifold
open scoped Manifold ContDiff SchwartzMap BigOperators
attribute [local instance] Classical.propDecidable

namespace LeanShared.FiniteChartLocalization

variable {E M Chart Core : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [Fintype Chart]
  [AddCommGroup Core] [Module ℂ Core]
  (e : Chart → OpenPartialHomeomorph M E) (θ : Chart → M → ℂ)
  (hsupp : ∀ i, tsupport (θ i) ⊆ (e i).source)
  (he : ∀ i, e i ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
  (hθ : ∀ i, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ (θ i))
  (functions : Core →ₗ[ℂ] (M → ℂ))
  (smooth : ∀ f : Core, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ (functions f))
  (hcompact : ∀ i, HasCompactSupport (θ i))

/-- Constructed supported smooth coordinates for each actual atlas member. -/
def localize (i : Chart) : Core →ₗ[ℂ]
    SchwartzJetSpace.supportedCore (ChartLocalization.localSupport (e i) (θ i)) :=
  ChartLocalization.linearMap (e i) (θ i) (hsupp i) (he i) (hθ i) functions smooth (hcompact i)

/-- The genuine finite chart map of the global smooth core. -/
def chartMap : Core →ₗ[ℂ]
    (∀ i, SchwartzJetSpace.supportedCore (ChartLocalization.localSupport (e i) (θ i))) :=
  LinearMap.pi (localize e θ hsupp he hθ functions smooth hcompact)

omit [Fintype Chart] in
@[simp]
theorem localize_chart (i : Chart) (f : Core) (x : M) (hx : x ∈ (e i).source) :
    (localize e θ hsupp he hθ functions smooth hcompact i f).val (e i x) =
      θ i x * functions f x :=
  ChartLocalization.coordinate_chart (e i) (θ i) (functions f) x hx

omit [Fintype Chart] in
/-- Zero extension back into the manifold reconstructs every localized term,
including points outside its chart source. -/
theorem reconstructed_term (i : Chart) (f : Core) (x : M) :
    (if x ∈ (e i).source then
      (localize e θ hsupp he hθ functions smooth hcompact i f).val (e i x) else 0) =
      θ i x * functions f x := by
  classical
  by_cases hx : x ∈ (e i).source
  · rw [ite_eq_left hx, localize_chart e θ hsupp he hθ functions smooth hcompact i f x hx]
  · have hzero : θ i x = 0 := by
      by_contra hn
      exact hx (hsupp i (subset_tsupport (θ i) hn))
    simp only [ite_eq_right hx, hzero, zero_mul]

/-- The finite partition of unity gives the paper's exact global recovery. -/
theorem reconstruct (V : Set M) (hpartition : ∀ x ∈ V, ∑ i, θ i x = 1)
    (f : Core) (x : M) (hx : x ∈ V) :
    (∑ i, if x ∈ (e i).source then
      (localize e θ hsupp he hθ functions smooth hcompact i f).val (e i x) else 0) =
      functions f x := by
  classical
  simp_rw [reconstructed_term e θ hsupp he hθ functions smooth hcompact]
  rw [← Finset.sum_mul, hpartition x hx, one_mul]

/-- Supported global functions cannot disappear in all chart coordinates.
This establishes faithfulness of the common core before norm completion. -/
theorem chartMap_injective (V : Set M)
    (hpartition : ∀ x ∈ V, ∑ i, θ i x = 1)
    (hzero : ∀ f : Core, ∀ x ∉ V, functions f x = 0)
    (hfunctions : Function.Injective functions) :
    Function.Injective (chartMap e θ hsupp he hθ functions smooth hcompact) := by
  classical
  intro f g hfg
  apply hfunctions
  funext x
  by_cases hx : x ∈ V
  · rw [← reconstruct e θ hsupp he hθ functions smooth hcompact V hpartition f x hx,
      ← reconstruct e θ hsupp he hθ functions smooth hcompact V hpartition g x hx]
    apply Finset.sum_congr rfl
    intro i _
    have hi : localize e θ hsupp he hθ functions smooth hcompact i f =
        localize e θ hsupp he hθ functions smooth hcompact i g := congrFun hfg i
    rw [hi]
  · rw [hzero f x hx, hzero g x hx]

end LeanShared.FiniteChartLocalization
