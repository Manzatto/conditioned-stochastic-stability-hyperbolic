module

public import LeanShared.Dynamics.OneSidedPredecessors
public import Mathlib.Topology.Algebra.Indicator
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! The actual weighted one-sided graph transfer operator: a finite sum
over precisely the admitted predecessor symbols, using literal prepend
branches.  It is positive and defines a bounded linear operator on
continuous functions; no spectral or zeta conclusion is supplied here.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  {R : A → A → Prop}

instance admittedSymbolFintype : Fintype (AdmittedSymbol R) := by
  classical
  exact inferInstanceAs (Fintype {j : A // ∃ a : Path R, a.val 0 = j})

@[expose] def weightedTransfer (ψ f : FuturePath R → ℝ) (a : FuturePath R) : ℝ :=
  ∑ j : AdmittedSymbol R, {b : FuturePath R | R j.val (b.val 0)}.indicator
    (fun b => Real.exp (ψ (prependOrStay j b)) * f (prependOrStay j b)) a

theorem weightedTransfer_continuous (ψ f : FuturePath R → ℝ)
    (continuousψ : Continuous ψ) (continuousF : Continuous f) : Continuous (weightedTransfer ψ f) := by
  classical
  apply continuous_finsetSum
  intro j _
  exact (predecessorDomain_clopen j).continuous_indicator
    ((Real.continuous_exp.comp (continuousψ.comp (prependOrStay_continuous j))).mul
      (continuousF.comp (prependOrStay_continuous j)))

omit [TopologicalSpace A] [DiscreteTopology A] in
theorem weightedTransfer_nonnegative (ψ f : FuturePath R → ℝ) (positiveF : ∀ a, 0 ≤ f a)
    (a : FuturePath R) : 0 ≤ weightedTransfer ψ f a := by
  classical
  apply Finset.sum_nonneg
  intro j _
  exact Set.indicator_nonneg (fun b _ => mul_nonneg (Real.exp_pos _).le (positiveF _)) _

omit [TopologicalSpace A] [DiscreteTopology A] in
theorem weightedTransfer_add (ψ f g : FuturePath R → ℝ) :
    weightedTransfer ψ (fun a => f a + g a) = fun a => weightedTransfer ψ f a + weightedTransfer ψ g a := by
  classical
  funext a
  dsimp only [weightedTransfer]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases edge : R j.val (a.val 0) <;> simp only [Set.indicator, mem_ofPred_eq, edge,
    ite_true, ite_false, mul_add, add_zero]

omit [TopologicalSpace A] [DiscreteTopology A] in
theorem weightedTransfer_smul (ψ f : FuturePath R → ℝ) (c : ℝ) :
    weightedTransfer ψ (fun a => c * f a) = fun a => c * weightedTransfer ψ f a := by
  classical
  funext a
  dsimp only [weightedTransfer]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases edge : R j.val (a.val 0) <;>
    simp only [Set.indicator, mem_ofPred_eq, edge, ite_true, ite_false, mul_zero]
  ring

variable [CompactSpace A]

@[expose] def weightedTransferLinear (ψ : C(FuturePath R, ℝ)) :
    C(FuturePath R, ℝ) →ₗ[ℝ] C(FuturePath R, ℝ) where
  toFun f := ⟨weightedTransfer ψ f, weightedTransfer_continuous ψ f ψ.continuous f.continuous⟩
  map_add' f g := by
    apply ContinuousMap.ext
    exact congrFun (weightedTransfer_add ψ f g)
  map_smul' c f := by
    apply ContinuousMap.ext
    exact congrFun (weightedTransfer_smul ψ f c)

theorem weightedTransfer_norm_bound (ψ f : C(FuturePath R, ℝ)) :
    ‖weightedTransferLinear ψ f‖ ≤
      ((Fintype.card (AdmittedSymbol R) : ℝ) * Real.exp ‖ψ‖) * ‖f‖ := by
  classical
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro a
  change ‖weightedTransfer ψ f a‖ ≤ _
  have term (j : AdmittedSymbol R) :
      ‖{b : FuturePath R | R j.val (b.val 0)}.indicator
        (fun b => Real.exp (ψ (prependOrStay j b)) * f (prependOrStay j b)) a‖ ≤
        Real.exp ‖ψ‖ * ‖f‖ := by
    by_cases edge : R j.val (a.val 0)
    · have member : a ∈ {b : FuturePath R | R j.val (b.val 0)} := edge
      rw [Set.indicator_of_mem member, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (Real.exp_le_exp.mpr (ContinuousMap.apply_le_norm ψ _))
        (f.norm_coe_le_norm _) (norm_nonneg _) (Real.exp_pos _).le
    · have member : a ∉ {b : FuturePath R | R j.val (b.val 0)} := edge
      rw [Set.indicator_of_notMem member, norm_zero]
      positivity
  calc
    _ ≤ ∑ j : AdmittedSymbol R, ‖{b : FuturePath R | R j.val (b.val 0)}.indicator
        (fun b => Real.exp (ψ (prependOrStay j b)) * f (prependOrStay j b)) a‖ := norm_sum_le _ _
    _ ≤ ∑ _j : AdmittedSymbol R, Real.exp ‖ψ‖ * ‖f‖ := Finset.sum_le_sum (fun j _ => term j)
    _ = ((Fintype.card (AdmittedSymbol R) : ℝ) * Real.exp ‖ψ‖) * ‖f‖ := by simp; ring

@[expose] def weightedTransferOperator (ψ : C(FuturePath R, ℝ)) :
    C(FuturePath R, ℝ) →L[ℝ] C(FuturePath R, ℝ) :=
  (weightedTransferLinear ψ).mkContinuous
    ((Fintype.card (AdmittedSymbol R) : ℝ) * Real.exp ‖ψ‖) (weightedTransfer_norm_bound ψ)

end LeanShared.BilateralShadowingCoding
