module
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.Normed.Group.Bounded

/-! Continuous compactly supported functions with arbitrary normed target
have a constructed bounded realization; no target ring is required. -/
public noncomputable section
open Set
open scoped BoundedContinuousFunction
namespace LeanShared.CompactSupportBoundedFunction
variable {X F : Type*} [TopologicalSpace X] [NormedAddCommGroup F]

theorem exists_bound (f : X → F) (continuous : Continuous f) (compact : HasCompactSupport f) :
    ∃ R : ℝ, 0≤R ∧ ∀x,‖f x‖≤R := by
  obtain ⟨R,hR,bound⟩ := (compact.isCompact_range continuous).isBounded.exists_pos_norm_le
  exact ⟨R,hR.le,fun x => bound (f x) (mem_range_self x)⟩

@[expose] def bounded (f : X → F) (continuous : Continuous f) (compact : HasCompactSupport f) : X →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup f continuous
    (Classical.choose (exists_bound f continuous compact))
    (Classical.choose_spec (exists_bound f continuous compact)).2

theorem bounded_apply (f : X → F) (continuous : Continuous f) (compact : HasCompactSupport f) (x : X) :
    bounded f continuous compact x=f x := rfl
end LeanShared.CompactSupportBoundedFunction
