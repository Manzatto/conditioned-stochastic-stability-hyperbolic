module

public import LeanShared.Analysis.DualRestrictionCompactness
public import LeanShared.Analysis.SchwartzLeafComponent

/-!
# Compact fixed-kernel components on kernel/jet subspace duals

The tuple subspace need only contain the actual translated kernel sections.
The compact smoothing component descends to its dual by norm-preserving
Hahn--Banach extensions, without a linear extension-selection assumption.

For the paper, the tuple subspace must still be identified with the finite
derivative jets of compactly supported test functions. Neither that concrete
derivative construction nor the anisotropic norm equivalence is assumed here.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped SchwartzMap BoundedContinuousFunction

namespace LeanShared.SchwartzLeafComponent

variable {E I U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]
  {K : Set E} (hK : IsCompact K) (ψ : I → 𝓢(E, ℂ)) (a : I → K →ᵇ ℂ)
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)
  (k : ℕ) (hk : (Module.finrank ℝ U : ℝ) < (k : ℝ))
  (V : Submodule ℂ (I → K →ᵇ ℂ)) (hsection : ∀ x, kernelSection ψ a x ∈ V)

include hsection in
/-- The true Schwartz component depends only on functional values on the
kernel sections, hence only on restriction to the containing tuple subspace. -/
theorem operator_restriction_compatible (f g : Source (K := K) (I := I))
    (hfg : ∀ v : V, f v = g v) :
    operator hK ψ a μ hJ k hk f = operator hK ψ a μ hJ k hk g := by
  apply lp.ext
  funext L
  apply Lp.ext
  filter_upwards [operator_ae hK ψ a μ hJ k hk f L,
    operator_ae hK ψ a μ hJ k hk g L] with y hf hg
  rw [hf, hg]
  exact hfg ⟨kernelSection ψ a (L.graph y), hsection (L.graph y)⟩

/-- The actual compact smoothing operator on the dual of a kernel/jet
subspace. It is independent of individual Hahn--Banach extension choices. -/
def subspaceOperator : (V →L[ℂ] ℂ) →L[ℂ] GraphLeafNorm.LeafSpace (E := E) μ (J := J) :=
  DualRestrictionCompactness.descend V (operator hK ψ a μ hJ k hk)
    (operator_restriction_compatible hK ψ a μ hJ k hk V hsection)

theorem subspaceOperator_isCompact :
    IsCompactOperator (subspaceOperator hK ψ a μ hJ k hk V hsection) :=
  DualRestrictionCompactness.descend_isCompact V (operator hK ψ a μ hJ k hk)
    (operator_restriction_compatible hK ψ a μ hJ k hk V hsection)
    (operator_isCompact hK ψ a μ hJ k hk)

/-- Exact smoothing pairing on every genuine graph measure. -/
theorem subspaceOperator_ae (f : V →L[ℂ] ℂ) (L : GraphLeafNorm.GraphLeaf U E J) :
    subspaceOperator hK ψ a μ hJ k hk V hsection f L =ᵐ[L.sourceMeasure μ]
      (fun y => f ⟨kernelSection ψ a (L.graph y), hsection (L.graph y)⟩) := by
  change operator hK ψ a μ hJ k hk (DualRestrictionCompactness.extension V f) L =ᵐ[_] _
  apply (operator_ae hK ψ a μ hJ k hk (DualRestrictionCompactness.extension V f) L).trans
  exact ae_of_all _ fun y => DualRestrictionCompactness.extension_apply V f
    ⟨kernelSection ψ a (L.graph y), hsection (L.graph y)⟩

end LeanShared.SchwartzLeafComponent
