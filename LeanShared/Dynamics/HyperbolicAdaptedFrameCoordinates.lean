module
public import LeanShared.Dynamics.HyperbolicAdaptedFramePatches
public import LeanShared.Dynamics.HyperbolicAdaptedUniformComparison
public import LeanShared.Analysis.OrthogonalBilinearFrame

/-! Actual local adapted frames give invertible coordinate maps with
uniform quadratic bounds in the original tangent norm. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff BigOperators
namespace LeanShared.HyperbolicAdaptedFramePatches
open HyperbolicAdaptedForms HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

namespace LocalFrame
variable {h : HyperbolicData (E := E) T Λ}
  {S : ∀ x : M, Submodule ℝ (TangentSpace (𝓘(ℝ, E)) x)}
  {d : ℕ} {a : ℝ} {N : ℕ} {x : Λ}

@[expose] def coordinateMap (F : LocalFrame h S d a N x)
    (y : ↥(Λ ∩ F.neighborhood)) : (Fin d → ℝ) →ₗ[ℝ] S y.val where
  toFun c := ⟨∑ i, c i • F.vector y i,
    (S y.val).sum_mem (fun i _ => (S y.val).smul_mem (c i) (F.member y i))⟩
  map_add' c b := Subtype.ext (by simp [add_smul, Finset.sum_add_distrib])
  map_smul' r c := Subtype.ext (by simp [Finset.smul_sum, mul_smul])

omit [FiniteDimensional ℝ E]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)] in
theorem coordinateMap_bijective (F : LocalFrame h S d a N x)
    (y : ↥(Λ ∩ F.neighborhood)) : Function.Bijective (F.coordinateMap y) := by
  constructor
  · intro c b equal
    apply OrthogonalBilinearFrame.combination_injective
      (splitForm T T.symm h.projection a N y.val) (F.vector y) (F.orthonormal y)
    exact congrArg Subtype.val equal
  · intro v
    obtain ⟨c, equal⟩ := F.spans y v.val v.property
    exact ⟨c, Subtype.ext equal.symm⟩

@[expose] def coordinates (F : LocalFrame h S d a N x)
    (y : ↥(Λ ∩ F.neighborhood)) : (Fin d → ℝ) ≃L[ℝ] S y.val :=
  (LinearEquiv.ofBijective (F.coordinateMap y) (F.coordinateMap_bijective y)).toContinuousLinearEquiv

omit [FiniteDimensional ℝ E]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)] in
theorem quadratic (F : LocalFrame h S d a N x)
    (y : ↥(Λ ∩ F.neighborhood)) (c : Fin d → ℝ) :
    splitForm T T.symm h.projection a N y.val
      (F.coordinates y c).val (F.coordinates y c).val = ∑ i, (c i) ^ 2 :=
  OrthogonalBilinearFrame.quadratic _ _ (F.orthonormal y) c

end LocalFrame

/-- One comparison constant works for every local adapted frame and all of its points, at the same
chosen adapted time. -/
theorem uniform_coordinate_comparison (h : HyperbolicData (E := E) T Λ)
    (a : ℝ) (N : ℕ) (length : 0 < N) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (S : ∀ x : M, Submodule ℝ (TangentSpace (𝓘(ℝ, E)) x)) (d : ℕ)
        (x : Λ) (F : LocalFrame h S d a N x) (y : ↥(Λ ∩ F.neighborhood))
        (c : Fin d → ℝ),
        ‖(F.coordinates y c).val‖ ^ 2 ≤ 2 * ∑ i, (c i) ^ 2 ∧
          (∑ i, (c i) ^ 2) ≤ B * ‖(F.coordinates y c).val‖ ^ 2 := by
  obtain ⟨B, positiveB, bound⟩ :=
    HyperbolicAdaptedUniformComparison.uniform_comparison h a N length
  refine ⟨B, positiveB, ?_⟩
  intro S d x F y c
  have comparisons := bound y.val y.property.1 (F.coordinates y c).val
  simpa only [F.quadratic y c] using comparisons

end LeanShared.HyperbolicAdaptedFramePatches
