module
public import LeanShared.Geometry.CenteredTangentJacobianComparison
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Actual compact Riemannian chart estimates give common bounds for all
bounded affine-normalized endpoint encodings, with independent model types. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff BigOperators
namespace LeanShared.CenteredTangentJacobianComparison
variable {E P M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

theorem exists_encoding_bounds (c : OpenPartialHomeomorph M E)
    (hc : c∈maximalAtlas (𝓘(ℝ,E)) ∞ M) (K : Set M) (compact : IsCompact K)
    (inside : K⊆c.source) {B : ℝ} (positiveB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : M) (hx : x∈K) (L : P ≃L[ℝ] E),
      ‖L.toContinuousLinearMap‖ ≤ B → ‖L.symm.toContinuousLinearMap‖ ≤ B →
      ‖(encoding c (CompactRiemannianChartBounds.chart_differentiable c hc) x
        (inside hx) L).toContinuousLinearMap‖ ≤ C ∧
      ‖(encoding c (CompactRiemannianChartBounds.chart_differentiable c hc) x
        (inside hx) L).symm.toContinuousLinearMap‖ ≤ C := by
  obtain ⟨A, positiveA, forward⟩ := CompactRiemannianChartBounds.forward c hc K compact inside
  obtain ⟨D, positiveD, backward⟩ := CompactRiemannianChartBounds.inverse c hc K compact inside
  refine ⟨B*max A D, mul_pos positiveB (positiveA.trans_le (le_max_left _ _)), ?_⟩
  intro x hx L boundL boundInv
  constructor
  · have actual : (encoding c (CompactRiemannianChartBounds.chart_differentiable c hc) x
        (inside hx) L).toContinuousLinearMap = L.symm.toContinuousLinearMap.comp
          ((NormedSpace.fromTangentSpace (𝕜:=ℝ) (c x)).toContinuousLinearMap.comp
            (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) c x)) := by
      apply ContinuousLinearMap.ext
      intro v
      rfl
    rw [actual]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul boundInv ((forward x hx).trans (le_max_left _ _)) (norm_nonneg _) positiveB.le)
  · have actual : (encoding c (CompactRiemannianChartBounds.chart_differentiable c hc) x
        (inside hx) L).symm.toContinuousLinearMap =
          (((CompactRiemannianChartBounds.chart_differentiable c hc).mfderiv
            (inside hx)).symm.toContinuousLinearMap.comp
              (NormedSpace.fromTangentSpace (𝕜:=ℝ) (c x)).symm.toContinuousLinearMap).comp
                L.toContinuousLinearMap := rfl
    rw [actual]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul ((backward x hx).trans (le_max_right _ _)) boundL (norm_nonneg _)
        ((positiveA.trans_le (le_max_left _ _)).le)).trans_eq (mul_comm _ _))

/-- The endpoint atlas is fixed before the derivative word. -/
theorem exists_finite_encoding_bounds {ι : Type*} (indices : Finset ι)
    (charts : ι → OpenPartialHomeomorph M E)
    (smooth : ∀ i ∈ indices, charts i ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (patch : ι → Set M) (compact : ∀ i ∈ indices, IsCompact (patch i))
    (inside : ∀ i ∈ indices, patch i ⊆ (charts i).source)
    {B : ℝ} (positiveB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ i (hi : i∈indices) (x : M) (hx : x∈patch i) (L : P ≃L[ℝ] E),
      ‖L.toContinuousLinearMap‖ ≤ B → ‖L.symm.toContinuousLinearMap‖ ≤ B →
      ‖(encoding (charts i) (CompactRiemannianChartBounds.chart_differentiable (charts i) (smooth i hi)) x
        (inside i hi hx) L).toContinuousLinearMap‖ ≤ C ∧
      ‖(encoding (charts i) (CompactRiemannianChartBounds.chart_differentiable (charts i) (smooth i hi)) x
        (inside i hi hx) L).symm.toContinuousLinearMap‖ ≤ C := by
  classical
  have localBounds (i : indices) := exists_encoding_bounds (P := P) (charts i.val)
    (smooth i.val i.property) (patch i.val) (compact i.val i.property) (inside i.val i.property) positiveB
  choose costs positive bounds using localBounds
  let C := 1+∑ i : indices, costs i
  have nonnegativeSum : 0 ≤ ∑ i : indices, costs i :=
    Finset.sum_nonneg (fun i _ => (positive i).le)
  refine ⟨C, by dsimp only [C]; linarith, ?_⟩
  intro i hi x hx L boundL boundInv
  have below : costs ⟨i,hi⟩ ≤ ∑ j : indices, costs j :=
    Finset.single_le_sum (fun j _ => (positive j).le) (Finset.mem_univ _)
  have facts := bounds ⟨i,hi⟩ x hx L boundL boundInv
  exact ⟨facts.1.trans (by dsimp only [C]; linarith), facts.2.trans (by dsimp only [C]; linarith)⟩

end LeanShared.CenteredTangentJacobianComparison
