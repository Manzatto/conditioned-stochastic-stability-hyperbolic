module

public import LeanShared.Dynamics.OneSidedTransferGrowth
public import Mathlib.Analysis.Complex.Basic

/-! The literal complex-linear weighted graph transfer, using precisely
the same admitted branches and real potential as the constructed real
operator.  Its real and imaginary parts are the literal real transfer.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  {R : A → A → Prop}

@[expose] def complexWeightedTransfer (ψ : FuturePath R → ℝ) (f : FuturePath R → ℂ)
    (a : FuturePath R) : ℂ :=
  ∑ j : AdmittedSymbol R, {b : FuturePath R | R j.val (b.val 0)}.indicator
    (fun b => (Real.exp (ψ (prependOrStay j b)) : ℂ) * f (prependOrStay j b)) a

theorem complexWeightedTransfer_continuous (ψ : FuturePath R → ℝ) (f : FuturePath R → ℂ)
    (continuousψ : Continuous ψ) (continuousF : Continuous f) : Continuous (complexWeightedTransfer ψ f) := by
  classical
  apply continuous_finsetSum
  intro j _
  exact (predecessorDomain_clopen j).continuous_indicator
    (((Complex.continuous_ofReal.comp Real.continuous_exp).comp
      (continuousψ.comp (prependOrStay_continuous j))).mul (continuousF.comp (prependOrStay_continuous j)))

omit [TopologicalSpace A] [DiscreteTopology A] in
theorem complexWeightedTransfer_add (ψ : FuturePath R → ℝ) (f g : FuturePath R → ℂ) :
    complexWeightedTransfer ψ (fun a => f a + g a) =
      fun a => complexWeightedTransfer ψ f a + complexWeightedTransfer ψ g a := by
  classical
  funext a
  dsimp only [complexWeightedTransfer]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases edge : R j.val (a.val 0) <;> simp only [Set.indicator, mem_ofPred_eq, edge,
    ite_true, ite_false, mul_add, add_zero]

omit [TopologicalSpace A] [DiscreteTopology A] in
theorem complexWeightedTransfer_smul (ψ : FuturePath R → ℝ) (f : FuturePath R → ℂ) (c : ℂ) :
    complexWeightedTransfer ψ (fun a => c * f a) = fun a => c * complexWeightedTransfer ψ f a := by
  classical
  funext a
  dsimp only [complexWeightedTransfer]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases edge : R j.val (a.val 0) <;>
    simp only [Set.indicator, mem_ofPred_eq, edge, ite_true, ite_false, mul_zero]
  ring

omit [TopologicalSpace A] [DiscreteTopology A] in
theorem complexWeightedTransfer_re (ψ : FuturePath R → ℝ) (f : FuturePath R → ℂ) (a : FuturePath R) :
    (complexWeightedTransfer ψ f a).re = weightedTransfer ψ (fun b => (f b).re) a := by
  classical
  dsimp only [complexWeightedTransfer, weightedTransfer]
  change Complex.reCLM (∑ j : AdmittedSymbol R, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases edge : R j.val (a.val 0) <;>
    simp only [Set.indicator, mem_ofPred_eq, edge, ite_true, ite_false,
      Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, map_zero]

omit [TopologicalSpace A] [DiscreteTopology A] in
theorem complexWeightedTransfer_im (ψ : FuturePath R → ℝ) (f : FuturePath R → ℂ) (a : FuturePath R) :
    (complexWeightedTransfer ψ f a).im = weightedTransfer ψ (fun b => (f b).im) a := by
  classical
  dsimp only [complexWeightedTransfer, weightedTransfer]
  change Complex.imCLM (∑ j : AdmittedSymbol R, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases edge : R j.val (a.val 0) <;>
    simp only [Set.indicator, mem_ofPred_eq, edge, ite_true, ite_false,
      Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, map_zero]

variable [CompactSpace A]

@[expose] def complexWeightedTransferLinear (ψ : C(FuturePath R, ℝ)) :
    C(FuturePath R, ℂ) →ₗ[ℂ] C(FuturePath R, ℂ) where
  toFun f := ⟨complexWeightedTransfer ψ f, complexWeightedTransfer_continuous ψ f ψ.continuous f.continuous⟩
  map_add' f g := by
    apply ContinuousMap.ext
    exact congrFun (complexWeightedTransfer_add ψ f g)
  map_smul' c f := by
    apply ContinuousMap.ext
    exact congrFun (complexWeightedTransfer_smul ψ f c)

theorem complexWeightedTransfer_norm_bound (ψ : C(FuturePath R, ℝ)) (f : C(FuturePath R, ℂ)) :
    ‖complexWeightedTransferLinear ψ f‖ ≤
      ((Fintype.card (AdmittedSymbol R) : ℝ) * Real.exp ‖ψ‖) * ‖f‖ := by
  classical
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro a
  change ‖complexWeightedTransfer ψ f a‖ ≤ _
  have term (j : AdmittedSymbol R) :
      ‖{b : FuturePath R | R j.val (b.val 0)}.indicator
        (fun b => (Real.exp (ψ (prependOrStay j b)) : ℂ) * f (prependOrStay j b)) a‖ ≤
        Real.exp ‖ψ‖ * ‖f‖ := by
    by_cases edge : R j.val (a.val 0)
    · have member : a ∈ {b : FuturePath R | R j.val (b.val 0)} := edge
      rw [Set.indicator_of_mem member, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (Real.exp_le_exp.mpr (ContinuousMap.apply_le_norm ψ _))
        (f.norm_coe_le_norm _) (norm_nonneg _) (Real.exp_pos _).le
    · have member : a ∉ {b : FuturePath R | R j.val (b.val 0)} := edge
      rw [Set.indicator_of_notMem member, norm_zero]
      positivity
  calc
    _ ≤ ∑ j : AdmittedSymbol R, ‖{b : FuturePath R | R j.val (b.val 0)}.indicator
        (fun b => (Real.exp (ψ (prependOrStay j b)) : ℂ) * f (prependOrStay j b)) a‖ := norm_sum_le _ _
    _ ≤ ∑ _j : AdmittedSymbol R, Real.exp ‖ψ‖ * ‖f‖ := Finset.sum_le_sum (fun j _ => term j)
    _ = ((Fintype.card (AdmittedSymbol R) : ℝ) * Real.exp ‖ψ‖) * ‖f‖ := by simp; ring

@[expose] def complexWeightedTransferOperator (ψ : C(FuturePath R, ℝ)) :
    C(FuturePath R, ℂ) →L[ℂ] C(FuturePath R, ℂ) :=
  (complexWeightedTransferLinear ψ).mkContinuous
    ((Fintype.card (AdmittedSymbol R) : ℝ) * Real.exp ‖ψ‖) (complexWeightedTransfer_norm_bound ψ)

end LeanShared.BilateralShadowingCoding
