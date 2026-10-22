module

public import LeanShared.Geometry.ConstructedManifoldLocalization
public import LeanShared.Analysis.FiniteRegularTransferRealization

/-!
# Literal finite chart-pair decomposition of the weighted transfer

Each chart-pair map is the actual transition `chart_j ∘ F ∘ chart_i⁻¹`
with its valid-domain guard and output weight `cutoff_i * g`. Summing its
action on the constructed source Schwartz coordinates gives exactly the
output coordinate of the global weighted composition. The global map may
have finite fractional regularity; the identity makes no assertion that its
output preserves the smooth core.

This connects local microlocal chart estimates to the same actual global
operator. No global Euclidean conjugacy or supplied matrix decomposition
is assumed.
-/

@[expose] public noncomputable section

open Set IsManifold
open scoped Manifold ContDiff SchwartzMap BigOperators
attribute [local instance] Classical.propDecidable

namespace LeanShared.ChartPairTransfer

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- The actual partial chart transition, with the exact global weight. -/
def pair (out inp : OpenPartialHomeomorph M E) (θ : M → ℂ)
    (F : M → M) (g : M → ℝ) : (E → ℂ) →ₗ[ℂ] (E → ℂ) where
  toFun f y := if y ∈ out.target then
    θ (out.symm y) * (g (out.symm y) : ℂ) *
      (if F (out.symm y) ∈ inp.source then f (inp (F (out.symm y))) else 0) else 0
  map_add' f h := by
    funext y
    split_ifs <;> simp_all [mul_add]
  map_smul' c f := by
    funext y
    split_ifs <;> simp_all [mul_left_comm, mul_assoc]


omit [NormedSpace ℝ E] [ChartedSpace E M] in
@[simp] theorem pair_apply (out inp : OpenPartialHomeomorph M E) (θ : M → ℂ)
    (F : M → M) (g : M → ℝ) (f : E → ℂ) (y : E) :
    pair out inp θ F g f y = if y ∈ out.target then
      θ (out.symm y) * (g (out.symm y) : ℂ) *
        (if F (out.symm y) ∈ inp.source then f (inp (F (out.symm y))) else 0) else 0 := rfl

omit [TopologicalSpace M] in
@[simp] theorem weighted_apply (F : M → M) (g : M → ℝ) (f : M → ℂ) (x : M) :
    FiniteRegularTransferRealization.weightedComposition F g f x = (g x : ℂ) * f (F x) := rfl

variable {AtlasIndex Core : Type*} [AddCommGroup Core] [Module ℂ Core]
  (e : AtlasIndex → OpenPartialHomeomorph M E) {S : Set M}
  (D : ConstructedManifoldLocalization.Data e S)
  (he : ∀ j, e j ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
  (functions : Core →ₗ[ℂ] (M → ℂ))
  (smooth : ∀ f : Core, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ (functions f))
  (zero : ∀ f : Core, ∀ x ∉ S, functions f x = 0)

include zero in
/-- Source coordinates reconstruct at every point, including points
outside the live region where the actual input is zero. -/
theorem reconstruct_all (f : Core) (x : M) :
    (∑ j : D.indices, if x ∈ (e j).source then
      (ConstructedManifoldLocalization.localize e D he functions smooth j f).val (e j x) else 0) =
      functions f x := by
  by_cases hx : x ∈ S
  · exact ConstructedManifoldLocalization.reconstruct e D he functions smooth f x hx
  · change (∑ j : D.indices, if x ∈ (e j).source then
      (FiniteChartLocalization.localize (fun j : D.indices => e j) D.cutoff D.support
        (fun j => he j) D.smooth functions smooth D.compact j f).val (e j x) else 0) = functions f x
    simp_rw [FiniteChartLocalization.reconstructed_term (fun j : D.indices => e j)
      D.cutoff D.support (fun j => he j) D.smooth functions smooth D.compact,
      zero f x hx, mul_zero]
    exact Finset.sum_const_zero

include zero in
/-- The genuine finite local operator matrix equals the output coordinate
of the exact weighted manifold transfer on every supported smooth input. -/
theorem coordinate_decomposition (F : M → M) (g : M → ℝ)
    (i : D.indices) (f : Core) (y : E) :
    ChartLocalization.coordinate (e i) (D.cutoff i)
      (FiniteRegularTransferRealization.weightedComposition F g (functions f)) y =
      ∑ j : D.indices, pair (e i) (e j) (D.cutoff i) F g
        (ConstructedManifoldLocalization.localize e D he functions smooth j f).val y := by
  by_cases hy : y ∈ (e i).target
  · simp only [ChartLocalization.coordinate, pair_apply, weighted_apply, hy, ite_true]
    rw [← Finset.mul_sum, reconstruct_all e D he functions smooth zero]
    exact (mul_assoc _ _ _).symm
  · simp only [ChartLocalization.coordinate, pair_apply, hy, ite_false, Finset.sum_const_zero]

end LeanShared.ChartPairTransfer
