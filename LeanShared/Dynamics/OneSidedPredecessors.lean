module

public import LeanShared.Dynamics.OneSidedGraphPaths
public import Mathlib.Topology.Piecewise
public import Mathlib.Topology.Clopen

/-! Literal admissible predecessor branches of the one-sided graph.
Every branch is constructed from the chosen admissible past and the
given future; the resulting finite alphabet enumerates exactly the
preimages of the one-sided shift.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} {R : A → A → Prop}

@[expose] def AdmittedSymbol (R : A → A → Prop) :=
  {j : A // ∃ a : Path R, a.val 0 = j}

@[expose] def prependBilateral (j : AdmittedSymbol R) (a : FuturePath R)
    (edge : R j.val (a.val 0)) : Path R := by
  let ref := referencePath j.val j.property
  refine ⟨fun n => if n ≤ 0 then ref.val n else (futureExtension a).val (n - 1), ?_⟩
  intro n
  by_cases negative : n < 0
  · simp only [ite_eq_left (by omega : n ≤ 0), ite_eq_left (by omega : n + 1 ≤ 0)]
    exact ref.property n
  · by_cases zero : n = 0
    · subst n
      simp only [ite_eq_left le_rfl, zero_add, ite_eq_right (by omega : ¬ (1 : ℤ) ≤ 0), sub_self]
      rw [show ref.val 0 = j.val from referencePath_zero _ _]
      have atZero : (futureExtension a).val (0 : ℤ) = a.val 0 := futureExtension_future a 0
      rw [atZero]
      exact edge
    · simp only [ite_eq_right (by omega : ¬ n ≤ 0), ite_eq_right (by omega : ¬ n + 1 ≤ 0)]
      simpa only [add_sub_cancel_right, sub_add_cancel] using (futureExtension a).property (n - 1)

@[expose] def futurePrepend (j : AdmittedSymbol R) (a : FuturePath R)
    (edge : R j.val (a.val 0)) : FuturePath R :=
  futureRestriction (prependBilateral j a edge)

theorem futurePrepend_zero (j : AdmittedSymbol R) (a : FuturePath R) (edge : R j.val (a.val 0)) :
    (futurePrepend j a edge).val 0 = j.val := by
  change (if (0 : ℤ) ≤ 0 then (referencePath j.val j.property).val 0
    else (futureExtension a).val (0 - 1)) = j.val
  exact (ite_eq_left le_rfl).trans (referencePath_zero _ _)

theorem futurePrepend_succ (j : AdmittedSymbol R) (a : FuturePath R) (edge : R j.val (a.val 0)) (n : ℕ) :
    (futurePrepend j a edge).val (n + 1) = a.val n := by
  change (if ((n + 1 : ℕ) : ℤ) ≤ 0 then (referencePath j.val j.property).val (n + 1 : ℕ)
    else (futureExtension a).val (((n + 1 : ℕ) : ℤ) - 1)) = a.val n
  rw [ite_eq_right (by omega)]
  simpa only [Int.natCast_add, Int.cast_ofNat_Int, add_sub_cancel_right] using futureExtension_future a n

theorem futurePrepend_prefix (j : AdmittedSymbol R) (a b : FuturePath R)
    (edgeA : R j.val (a.val 0)) (edgeB : R j.val (b.val 0)) (n : ℕ)
    (same : PrefixAgreement a b n) :
    PrefixAgreement (futurePrepend j a edgeA) (futurePrepend j b edgeB) (n + 1) := by
  intro k bound
  cases k with
  | zero => rw [futurePrepend_zero, futurePrepend_zero]
  | succ k => rw [futurePrepend_succ, futurePrepend_succ]; exact same k (by omega)

variable [TopologicalSpace A]

theorem futureShift_prepend (j : AdmittedSymbol R) (a : FuturePath R) (edge : R j.val (a.val 0)) :
    futureShift (futurePrepend j a edge) = a := by
  apply Subtype.ext
  funext n
  exact futurePrepend_succ j a edge n

@[expose] def initialSymbol (a : FuturePath R) : AdmittedSymbol R :=
  ⟨a.val 0, futureExtension a, futureExtension_future a 0⟩

theorem futurePrepend_shift (a : FuturePath R) :
    futurePrepend (initialSymbol a) (futureShift a) (futurePath_edge a 0) = a := by
  apply Subtype.ext
  funext n
  cases n with
  | zero => exact futurePrepend_zero _ _ _
  | succ n => exact futurePrepend_succ _ _ _ n

@[expose] def prependOrStay (j : AdmittedSymbol R) (a : FuturePath R) : FuturePath R := by
  classical
  exact if edge : R j.val (a.val 0) then futurePrepend j a edge else a

variable [DiscreteTopology A]

theorem predecessorDomain_clopen (j : AdmittedSymbol R) :
    IsClopen {a : FuturePath R | R j.val (a.val 0)} :=
  (isClopen_discrete {i : A | R j.val i}).preimage
    ((continuous_apply 0).comp continuous_subtype_val)

theorem prependOrStay_continuous (j : AdmittedSymbol R) :
    Continuous (prependOrStay j : FuturePath R → FuturePath R) := by
  classical
  have values : Continuous (fun a : FuturePath R => (prependOrStay j a).val) := by
    apply continuous_pi
    intro n
    have emptyBoundary : frontier {a : FuturePath R | R j.val (a.val 0)} = ∅ :=
      isClopen_iff_frontier_eq_empty.mp (predecessorDomain_clopen j)
    cases n with
    | zero =>
      have formula (a : FuturePath R) : (prependOrStay j a).val 0 =
          if R j.val (a.val 0) then j.val else a.val 0 := by
        dsimp only [prependOrStay]
        split <;> simp only [futurePrepend_zero]
      simp only [formula]
      apply continuous_if (by simp only [emptyBoundary, notMem_empty, IsEmpty.forall_iff, implies_true])
      · exact continuousOn_const
      · exact ((continuous_apply 0).comp continuous_subtype_val).continuousOn
    | succ n =>
      have formula (a : FuturePath R) : (prependOrStay j a).val (n + 1) =
          if R j.val (a.val 0) then a.val n else a.val (n + 1) := by
        dsimp only [prependOrStay]
        split <;> simp only [futurePrepend_succ]
      simp only [formula]
      apply continuous_if (by simp only [emptyBoundary, notMem_empty, IsEmpty.forall_iff, implies_true])
      · exact ((continuous_apply n).comp continuous_subtype_val).continuousOn
      · exact ((continuous_apply (n + 1)).comp continuous_subtype_val).continuousOn
  exact values.subtype_mk _

end LeanShared.BilateralShadowingCoding
