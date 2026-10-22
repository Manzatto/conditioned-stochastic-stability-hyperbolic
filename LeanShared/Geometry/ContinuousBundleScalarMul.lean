module
public import Mathlib.Topology.VectorBundle.Basic

/-! Scalar multiplication of genuine continuous bundle-valued maps is
continuous, including the varying base point. -/
public section
namespace LeanShared.ContinuousBundleScalarMul
open Bundle Filter Set
open scoped Topology
variable {B F X : Type*} [TopologicalSpace B] [TopologicalSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

theorem continuous (b : X → B) (f : ∀ x, E (b x)) (a : X → ℝ)
    (continuousSection : Continuous (fun x => (⟨b x,f x⟩ : TotalSpace F E)))
    (scalar : Continuous a) :
    Continuous (fun x => (⟨b x,a x • f x⟩ : TotalSpace F E)) := by
  have base : Continuous b := (FiberBundle.continuous_proj F E).comp continuousSection
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨base.continuousAt,?_⟩
  let e := trivializationAt F E (b x)
  have coordinate : ContinuousAt (fun y => (e ⟨b y,f y⟩).2) x :=
    ((FiberBundle.continuousAt_totalSpace F _).mp continuousSection.continuousAt).2
  apply (scalar.continuousAt.smul coordinate).congr_of_eventuallyEq
  have inside := base.continuousAt.preimage_mem_nhds
    (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' (b x)))
  filter_upwards [inside] with y hy
  change (e (⟨b y,a y • f y⟩ : TotalSpace F E)).2 =
    a y • (e (⟨b y,f y⟩ : TotalSpace F E)).2
  simpa only [Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hy] using
    map_smul (e.continuousLinearMapAt ℝ (b y)) (a y) (f y)

end LeanShared.ContinuousBundleScalarMul
