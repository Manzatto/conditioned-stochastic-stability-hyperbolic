module
public import LeanShared.Geometry.FiniteCaptureWordCutoffs

/-! The entire topological support of a literal word cutoff stays in the
selected open cylinders, including boundary points of its nonzero set.
Continuity of the actual prefix maps supplies the closed pullbacks needed
for this stronger support statement. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff BigOperators
namespace LeanShared.FiniteSmoothCapturePartition
variable {E M X I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace X]
  [Fintype I] [Fintype J] {K : Set M} {v : I → Set M}

theorem wordCutoff_tsupport_subset (p : Data (E := E) K v) (points : J → X → M)
    (continuousPoints : ∀ j, Continuous (points j)) (labels : J → I) :
    tsupport (fun x => wordCutoff p (fun j => points j x) labels) ⊆
      ⋂ j, (points j) ⁻¹' v (labels j) := by
  classical
  intro x hx
  apply mem_iInter.mpr
  intro j
  apply p.support (labels j)
  have nonzeroSubset : Function.support (fun y => wordCutoff p (fun k => points k y) labels) ⊆
      (points j) ⁻¹' tsupport (p.beta (labels j)) := by
    intro y hy
    have factor : p.beta (labels j) (points j y) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hy) j (Finset.mem_univ j)
    exact subset_tsupport (p.beta (labels j)) factor
  exact (closure_minimal nonzeroSubset ((isClosed_tsupport _).preimage (continuousPoints j))) hx

end LeanShared.FiniteSmoothCapturePartition
