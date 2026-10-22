module
public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Actual finite sums of bundle-valued functions over a common base map
are continuous; the statement applies directly to endomorphism actions. -/
public section
namespace LeanShared.ContinuousBundleFiniteSum
open Bundle Filter Set
open scoped Topology BigOperators
variable {B F X ι : Type*} [TopologicalSpace B] [TopologicalSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

theorem continuous (s : Finset ι) (b : X → B) (f : ι → ∀ x : X, E (b x))
    (base : Continuous b)
    (hf : ∀ i ∈ s, Continuous (fun x => (⟨b x,f i x⟩ : TotalSpace F E))) :
    Continuous (fun x => (⟨b x,∑ i ∈ s, f i x⟩ : TotalSpace F E)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨base.continuousAt,?_⟩
  let e := trivializationAt F E (b x)
  have individual (i : ι) (hi : i ∈ s) :
      ContinuousAt (fun y => (e ⟨b y,f i y⟩).2) x :=
    ((FiberBundle.continuousAt_totalSpace F _).mp (hf i hi).continuousAt).2
  have sumContinuous : ContinuousAt (fun y => ∑ i ∈ s, (e ⟨b y,f i y⟩).2) x :=
    tendsto_finsetSum s individual
  apply sumContinuous.congr_of_eventuallyEq
  have inside := base.continuousAt.preimage_mem_nhds
    (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' (b x)))
  filter_upwards [inside] with y hy
  simpa only [Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hy] using
    map_sum (e.continuousLinearMapAt ℝ (b y)) (fun i => f i y) s
end LeanShared.ContinuousBundleFiniteSum
