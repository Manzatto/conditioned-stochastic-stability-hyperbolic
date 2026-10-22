module
public import LeanShared.Geometry.FiniteSmoothCapturePartition
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Literal products of the constructed spatial cutoffs give a partition
on every finite tracked word. Nonzero products force every observed point
into its selected open set. Their values stay in [0,1]. -/
@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff BigOperators
attribute [local instance] Classical.propDecidable
namespace LeanShared.FiniteSmoothCapturePartition
variable {E M I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [Fintype I] [Fintype J]
  {K : Set M} {v : I → Set M}

def wordCutoff (p : Data (E := E) K v) (points : J → M) (labels : J → I) : ℝ :=
  ∏ j, p.beta (labels j) (points j)

theorem wordCutoff_nonneg (p : Data (E := E) K v) (points : J → M) (labels : J → I) :
    0 ≤ wordCutoff p points labels :=
  Finset.prod_nonneg (fun j _ => (p.bounds (labels j) (points j)).1)

theorem wordCutoff_le_one (p : Data (E := E) K v) (points : J → M) (labels : J → I) :
    wordCutoff p points labels ≤ 1 :=
  Finset.prod_le_one₀ (fun j _ => (p.bounds (labels j) (points j)).1)
    (fun j _ => (p.bounds (labels j) (points j)).2)

theorem wordCutoff_nonzero_mem (p : Data (E := E) K v) (points : J → M) (labels : J → I)
    (nonzero : wordCutoff p points labels ≠ 0) (j : J) : points j ∈ v (labels j) := by
  classical
  have factor : p.beta (labels j) (points j) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp nonzero) j (Finset.mem_univ j)
  exact p.support (labels j) (subset_tsupport (p.beta (labels j)) factor)

theorem wordCutoff_sum (p : Data (E := E) K v) (points : J → M)
    (capture : ∀ j, points j ∈ p.capture) :
    ∑ labels : J → I, wordCutoff p points labels = 1 := by
  classical
  unfold wordCutoff
  rw [← Fintype.prod_sum (fun j i => p.beta i (points j))]
  simp only [p.one _ (capture _), Finset.prod_const_one]

theorem wordCutoff_continuous (p : Data (E := E) K v) (points : J → M → M)
    (continuousPoints : ∀ j, Continuous (points j)) (labels : J → I) :
    Continuous (fun m => wordCutoff p (fun j => points j m) labels) := by
  exact continuous_finsetProd _ (fun j _ =>
    (p.smooth (labels j)).continuous.comp (continuousPoints j))

end LeanShared.FiniteSmoothCapturePartition
