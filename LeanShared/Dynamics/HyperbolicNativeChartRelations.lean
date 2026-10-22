module

public import LeanShared.Dynamics.HyperbolicFiniteInverseChartBlocks
public import LeanShared.Dynamics.HyperbolicProjectionCocycle
public import LeanShared.Dynamics.HyperbolicProjectionCoordinates

/-! All matrix identities used by finite-atlas projection comparison follow
from the actual hyperbolic invariant splitting and actual differential
inverse. There are no additional coordinate cocycle certificates. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

omit [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] in
private theorem member (i : Λ) (x : M) (inside : x ∈ (chartAt E i.val).source) :
    x ∈ (trivializationAt E (TangentSpace (𝓘(ℝ,E))) i.val).baseSet := by
  rw [TangentChartTrivialization.baseSet]
  exact inside

theorem HyperbolicData.chartProjection_idempotent (h : HyperbolicData (E := E) T Λ)
    (i : Λ) (x : M) (hx : x ∈ Λ) (source : x ∈ (chartAt E i.val).source) :
    (h.chartProjection i x).comp (h.chartProjection i x) = h.chartProjection i x := by
  ext v
  exact h.projection_coordinates_idempotent _ x ⟨hx, member i x source⟩ v

omit [FiniteDimensional ℝ E] in
theorem HyperbolicData.chartBlock_intertwines (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (n : ℕ) (i j : Λ) (x : M) (hx : x ∈ Λ)
    (source : x ∈ (chartAt E i.val).source)
    (target : (T : M → M)^[n] x ∈ (chartAt E j.val).source) :
    (h.chartProjection j ((T : M → M)^[n] x)).comp (h.chartBlock n i j x) =
      (h.chartBlock n i j x).comp (h.chartProjection i x) :=
  BundleProjectionCocycleCoordinates.intertwines (TangentSpace (𝓘(ℝ,E)))
    _ _ h.projection x _ (member i x source) (member j _ target) _
    (h.projection_iterate_commutes forward n x hx)

omit [FiniteDimensional ℝ E] in
theorem HyperbolicData.chartInverseBlock_intertwines (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (n : ℕ) (i j : Λ) (x : M) (hx : x ∈ Λ)
    (source : x ∈ (chartAt E i.val).source)
    (target : (T.symm : M → M)^[n] x ∈ (chartAt E j.val).source) :
    (ContinuousLinearMap.id ℝ E - h.chartProjection j ((T.symm : M → M)^[n] x)).comp
        (h.chartInverseBlock n i j x) =
      (h.chartInverseBlock n i j x).comp (ContinuousLinearMap.id ℝ E - h.chartProjection i x) := by
  have same := BundleProjectionCocycleCoordinates.intertwines (TangentSpace (𝓘(ℝ,E)))
    (trivializationAt E (TangentSpace (𝓘(ℝ,E))) i.val)
    (trivializationAt E (TangentSpace (𝓘(ℝ,E))) j.val) h.projection x _
    (member i x source) (member j _ target) _
    (h.projection_inverse_iterate_commutes forward inverse n x hx)
  ext v
  have evaluation := congrArg (fun L : E →L[ℝ] E => L v) same
  simp only [ContinuousLinearMap.comp_apply] at evaluation
  simp only [ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.id_apply, map_sub]
  exact congrArg (fun w => h.chartInverseBlock n i j x v - w) evaluation

omit [FiniteDimensional ℝ E] in
theorem inverseChartMap_left (S : M ≃ₜ M)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) S)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) S.symm)
    (i j x : M) (source : x ∈ (chartAt E i).source) (target : S x ∈ (chartAt E j).source) :
    (inverseChartMap S forward inverse i j x).comp
      (BundleProjectionCocycleCoordinates.map (TangentSpace (𝓘(ℝ,E)))
        (trivializationAt E (TangentSpace (𝓘(ℝ,E))) i)
        (trivializationAt E (TangentSpace (𝓘(ℝ,E))) j) x (S x)
        (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) S x)) = ContinuousLinearMap.id ℝ E := by
  have source' : x ∈ (trivializationAt E (TangentSpace (𝓘(ℝ,E))) i).baseSet := by
    rw [TangentChartTrivialization.baseSet]; exact source
  have target' : S x ∈ (trivializationAt E (TangentSpace (𝓘(ℝ,E))) j).baseSet := by
    rw [TangentChartTrivialization.baseSet]; exact target
  have result := BundleProjectionCocycleCoordinates.inverse_left (TangentSpace (𝓘(ℝ,E)))
    (trivializationAt E (TangentSpace (𝓘(ℝ,E))) i)
    (trivializationAt E (TangentSpace (𝓘(ℝ,E))) j) x (S x) source' target'
    (DiffeomorphismDifferential.differential S forward inverse x)
  have differential : (DiffeomorphismDifferential.differential S forward inverse x).toContinuousLinearMap =
      mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) S x := by ext v; rfl
  rw [differential] at result
  exact result

end LeanShared.HyperbolicBasicSet
