module

public import LeanShared.Dynamics.PeriodicSymbolicFiberTuples
public import LeanShared.Dynamics.TupleMatchingMonodromy
public import LeanShared.Dynamics.TupleMatchingCodingCompatibility
public import LeanShared.Dynamics.MarkovCodingProperties
public import LeanShared.Dynamics.TupleProjectionFiberSubset

/-! Every nonempty invariant subset of the actual periodic return fiber
produces a literal periodic signed matching walk, with the exact original
coded point and the sign of the restricted return permutation.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function MarkovFinitePathRealization
variable {A X : Type*} [MetricSpace X] [TopologicalSpace A] [Fintype A] [DecidableEq A]

theorem periodic_fiber_subset_matching_exact (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (properties : MarkovCodingProperties T rectangles code)
    (x : X) [DecidableEq (code ⁻¹' {x})] (period : ℕ) (positive : 0 < period)
    (fixed : (T : X → X)^[period] x = x)
    (P : Equiv.Perm (code ⁻¹' {x}))
    (returns : ∀ a, (P a).val = (shift (Transition T rectangles) : _ → _)^[period] a.val)
    (s : Finset (code ⁻¹' {x})) (invariant : ∀ a, P a ∈ s ↔ a ∈ s)
    (k : ℕ) (card : s.card = k + 1) :
    ∃ walk : Path (SubsetMatchingEdgeTransition (Transition T rectangles) (Affiliated rectangles) (k + 1)),
      ∃ inside : matchingCode T rectangles code k walk = x,
      matchingFiberSubset T rectangles code properties.geometry k x ⟨walk, inside⟩ = s ∧
      Function.Periodic walk.val (period : ℤ) ∧
      (∏ i ∈ Finset.range period, matchingEdgeSign (walk.val i)) = Equiv.Perm.sign (P.subtypePerm invariant) := by
  let enum : Fin (k + 1) ≃ s := (s.equivFinOfCardEq card).symm
  let lifts : Fin (k + 1) → code ⁻¹' {x} := fun i => (enum i).val
  have distinct : Injective lifts := Subtype.val_injective.comp enum.injective
  obtain ⟨a, coordinates⟩ := exists_periodic_fiber_tuple T rectangles code properties.intertwines
    properties.finiteFibers properties.geometry x period positive fixed (k + 1) lifts distinct
  let restriction := P.subtypePerm invariant
  let q : Equiv.Perm (Fin (k + 1)) := (enum.trans restriction).trans enum.symm
  have indexed (i : Fin (k + 1)) : lifts (q i) = P (lifts i) := by
    have identity := enum.apply_symm_apply (restriction (enum i))
    exact congrArg (fun z : s => z.val) identity
  have monodromy (j : ℤ) : a.val (j + period) = a.val j ∘ q := by
    funext i
    have first := congrArg (fun p : Path (Transition T rectangles) => p.val (j + period)) (coordinates i)
    have last := congrArg (fun p : Path (Transition T rectangles) => p.val j) (coordinates (q i))
    calc
      a.val (j + period) i = (lifts i).val.val (j + period) := first
      _ = ((shift (Transition T rectangles) : _ → _)^[period] (lifts i).val).val j :=
        (shift_iterate_val (lifts i).val period j).symm
      _ = (P (lifts i)).val.val j := congrArg
        (fun p : Path (Transition T rectangles) => p.val j) (returns (lifts i)).symm
      _ = (lifts (q i)).val.val j := by rw [indexed i]
      _ = a.val j (q i) := last.symm
  have inside : matchingCode T rectangles code k (tupleToMatchingPath a) = x := by
    rw [matchingCode_tuple_projection T rectangles code properties.geometry k a 0, coordinates 0]
    exact (lifts 0).property
  refine ⟨tupleToMatchingPath a, inside, ?_,
    tupleMatching_periodic_of_monodromy a period q monodromy, ?_⟩
  · rw [matchingFiberSubset_tuple_projection T rectangles code properties x period positive fixed k a lifts coordinates inside]
    ext p
    constructor
    · intro member
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp member
      exact (enum i).property
    · intro member
      refine Finset.mem_image.mpr ⟨enum.symm ⟨p, member⟩, Finset.mem_univ _, ?_⟩
      exact congrArg (fun z : s => z.val) (enum.apply_symm_apply ⟨p, member⟩)
  · rw [tupleMatching_sign_monodromy a period q monodromy]
    exact Equiv.Perm.sign_trans_trans_symm restriction enum

end LeanShared.BilateralShadowingCoding
