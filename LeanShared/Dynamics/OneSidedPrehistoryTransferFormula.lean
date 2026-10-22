module

public import LeanShared.Dynamics.OneSidedFinitePrehistories
public import LeanShared.Dynamics.ComplexOneSidedWeightedTransfer
public import LeanShared.Dynamics.OrbitEnergyConcatenation

/-! Exact weighted sums over the literal finite fibers of the one-sided
shift.  The graph-branch operator is identified with the actual inverse
orbit sum, retaining every potential weight.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function ThermodynamicDefinitions
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  {R : A → A → Prop}

omit [DiscreteTopology A] in
theorem complexWeightedTransfer_prehistory_one (ψ : FuturePath R → ℝ) (f : FuturePath R → ℂ)
    (a : FuturePath R) :
    complexWeightedTransfer ψ f a =
      ∑ b : FuturePrehistory 1 a, (Real.exp (ψ b.val) : ℂ) * f b.val := by
  classical
  let weight (j : AdmittedSymbol R) : ℂ :=
    (Real.exp (ψ (prependOrStay j a)) : ℂ) * f (prependOrStay j a)
  have branchSum : complexWeightedTransfer ψ f a =
      ∑ j : {j : AdmittedSymbol R // R j.val (a.val 0)}, weight j.val := by
    change (∑ j : AdmittedSymbol R, if R j.val (a.val 0) then weight j else 0) = _
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by intro j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]) weight
  let e : FuturePrehistory 1 a ≃ {j : AdmittedSymbol R // R j.val (a.val 0)} := shiftPreimageEquiv a
  have correspondence : (∑ b : FuturePrehistory 1 a, (Real.exp (ψ b.val) : ℂ) * f b.val) =
      ∑ j : {j : AdmittedSymbol R // R j.val (a.val 0)}, weight j.val := by
    apply Fintype.sum_equiv e
    intro b
    have tail : futureShift b.val = a := b.property
    have branch : prependOrStay (initialSymbol b.val) a = b.val := by
      apply (congrArg (prependOrStay (initialSymbol b.val)) tail.symm).trans
      have edge : R (initialSymbol b.val).val ((futureShift b.val).val 0) := futurePath_edge b.val 0
      rw [prependOrStay, dite_eq_left edge]
      exact futurePrepend_shift b.val
    change (Real.exp (ψ b.val) : ℂ) * f b.val =
      (Real.exp (ψ (prependOrStay (initialSymbol b.val) a)) : ℂ) * f (prependOrStay (initialSymbol b.val) a)
    rw [branch]
  exact branchSum.trans correspondence.symm

end LeanShared.BilateralShadowingCoding
