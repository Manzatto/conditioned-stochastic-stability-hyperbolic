module
public import Mathlib.Topology.VectorBundle.Riemannian

/-! Finite linear combinations of continuous sections over a varying base.
The scalar coefficients may vary continuously as well. -/
public noncomputable section
open Set Bundle Filter
open scoped Topology BigOperators
namespace LeanShared.FiniteBundleSectionCombination
variable {X B F ι : Type*} [TopologicalSpace X] [TopologicalSpace B]
  [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

theorem continuous_combination (b : X → B) (cb : Continuous b)
    (v : ∀ x, ι → E (b x))
    (sections : ∀ i, Continuous (fun x => (⟨b x, v x i⟩ : TotalSpace F E)))
    (c : X → ι → ℝ) (coefficients : ∀ i, Continuous (fun x => c x i)) :
    Continuous (fun x => (⟨b x, ∑ i, c x i • v x i⟩ : TotalSpace F E)) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨cb.continuousAt, ?_⟩
  let e := trivializationAt F E (b x)
  have center : b x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
  have each (i : ι) : ContinuousAt
      (fun y => e.continuousLinearMapAt ℝ (b y) (v y i)) x := by
    have actual := (sections i).continuousAt (x := x)
    rw [FiberBundle.continuousAt_totalSpace] at actual
    apply actual.2.congr_of_eventuallyEq
    filter_upwards [cb.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds center)] with y hy
    exact e.continuousLinearMapAt_apply_of_mem ℝ hy (v y i)
  have sum : ContinuousAt
      (fun y => ∑ i, c y i • e.continuousLinearMapAt ℝ (b y) (v y i)) x := by
    apply tendsto_finsetSum
    intro i _
    exact (coefficients i).continuousAt.smul (each i)
  apply sum.congr_of_eventuallyEq
  filter_upwards [cb.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds center)] with y hy
  rw [← e.continuousLinearMapAt_apply_of_mem ℝ hy]
  simp only [map_sum, map_smul]

end LeanShared.FiniteBundleSectionCombination
