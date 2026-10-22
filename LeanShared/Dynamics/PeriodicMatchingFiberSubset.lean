module

public import LeanShared.Dynamics.MatchingFiberSubsets
public import LeanShared.Dynamics.SignedMatchingLiftMonodromy

/-! A periodic matching walk yields an invariant subset of the actual
return fiber, and its edge-sign product equals the sign of the return
permutation restricted to that exact extracted subset.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function MarkovFinitePathRealization
variable {A X : Type*} [MetricSpace X] [TopologicalSpace A] [Fintype A]

omit [TopologicalSpace A] [Fintype A] in
theorem mem_matchingFiberSubset_iff (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (geometry : HasSymbolicFiberGeometry T rectangles code) (k : ℕ) (x : X)
    (a : (matchingCode T rectangles code k) ⁻¹' {x}) (p : code ⁻¹' {x}) :
    p ∈ matchingFiberSubset T rectangles code geometry k x a ↔
      ∃ i, matchingFiberCoordinate T rectangles code geometry k x a i = p := by
  classical
  simp only [matchingFiberSubset, Finset.mem_image, Finset.mem_univ, true_and]

theorem periodic_matching_fiber_subset (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (properties : MarkovCodingProperties T rectangles code) (k : ℕ) (x : X)
    [DecidableEq (code ⁻¹' {x})] (period : ℕ)
    (P : Equiv.Perm (code ⁻¹' {x}))
    (returns : ∀ a, (P a).val = (shift (Transition T rectangles) : _ → _)^[period] a.val)
    (a : (matchingCode T rectangles code k) ⁻¹' {x})
    (periodic : Function.Periodic a.val.val (period : ℤ)) :
    ∃ invariant : ∀ p, P p ∈ matchingFiberSubset T rectangles code properties.geometry k x a ↔
        p ∈ matchingFiberSubset T rectangles code properties.geometry k x a,
      (∏ i ∈ Finset.range period, matchingEdgeSign (a.val.val i)) =
        Equiv.Perm.sign (P.subtypePerm invariant) := by
  classical
  let c := matchingFiberCoordinate T rectangles code properties.geometry k x a
  let q := indexTransport (matchingPathPermutation a.val) period
  let s := matchingFiberSubset T rectangles code properties.geometry k x a
  have moves (i : Fin (k + 1)) : P (c i) = c (q i) := by
    apply Subtype.ext
    apply Subtype.ext
    funext j
    have monodromy := congrArg (fun u : Fin (k + 1) → A => u i)
      (matching_lift_monodromy a.val period periodic j)
    have returned := congrArg (fun p : Path (Transition T rectangles) => p.val j) (returns (c i))
    exact returned.trans ((shift_iterate_val (c i).val period j).trans monodromy)
  have invariant : ∀ p, P p ∈ s ↔ p ∈ s := by
    intro p
    constructor
    · intro inside
      obtain ⟨i, equal⟩ := (mem_matchingFiberSubset_iff T rectangles code properties.geometry k x a (P p)).mp inside
      have original : c (q.symm i) = p := P.injective
        ((moves (q.symm i)).trans (by simpa only [Equiv.apply_symm_apply] using equal))
      exact (mem_matchingFiberSubset_iff T rectangles code properties.geometry k x a p).mpr ⟨q.symm i, original⟩
    · intro inside
      obtain ⟨i, rfl⟩ := (mem_matchingFiberSubset_iff T rectangles code properties.geometry k x a p).mp inside
      exact (mem_matchingFiberSubset_iff T rectangles code properties.geometry k x a (P (c i))).mpr ⟨q i, (moves i).symm⟩
  let f : Fin (k + 1) → s := fun i => ⟨c i, (mem_matchingFiberSubset_iff T rectangles code properties.geometry k x a (c i)).mpr ⟨i, rfl⟩⟩
  have bijective : Bijective f := by
    constructor
    · intro i j equal
      exact matchingFiberCoordinate_injective T rectangles code properties.geometry k x a
        (congrArg (fun p : s => p.val) equal)
    · intro p
      obtain ⟨i, equal⟩ := (mem_matchingFiberSubset_iff T rectangles code properties.geometry k x a p.val).mp p.property
      exact ⟨i, Subtype.ext equal⟩
  let e := Equiv.ofBijective f bijective
  have conjugacy : P.subtypePerm invariant = (e.symm.trans q).trans e := by
    apply Equiv.ext
    intro p
    obtain ⟨i, rfl⟩ := e.surjective p
    apply Subtype.ext
    change P (c i) = c (q (e.symm (e i)))
    simpa only [Equiv.symm_apply_apply] using moves i
  refine ⟨invariant, ?_⟩
  rw [matching_path_sign_product, conjugacy]
  exact (Equiv.Perm.sign_symm_trans_trans q e).symm

end LeanShared.BilateralShadowingCoding
