module

public import LeanShared.Dynamics.ComplexOneSidedRealImag
public import LeanShared.Dynamics.OneSidedBackwardApproximation
public import LeanShared.Dynamics.OneSidedTransferBranchLower

/-! The literal positive transfer dominates the complex transfer modulus.
Actual graph prehistories give a strong maximum principle for real
superharmonic functions.  Every unit-modulus complex eigenfunction of
the unital transfer therefore has constant pointwise modulus.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function Filter Topology
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop}

omit [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] in
theorem complexWeightedTransfer_norm_domination (ψ : FuturePath R → ℝ) (f : FuturePath R → ℂ)
    (a : FuturePath R) :
    ‖complexWeightedTransfer ψ f a‖ ≤ weightedTransfer ψ (fun b => ‖f b‖) a := by
  classical
  dsimp only [complexWeightedTransfer, weightedTransfer]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  by_cases edge : R j.val (a.val 0)
  · have member : a ∈ {b : FuturePath R | R j.val (b.val 0)} := edge
    rw [Set.indicator_of_mem member, Set.indicator_of_mem member, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  · have member : a ∉ {b : FuturePath R | R j.val (b.val 0)} := edge
    rw [Set.indicator_of_notMem member, Set.indicator_of_notMem member, norm_zero]

theorem nonnegative_superharmonic_zero_predecessor (ψ g : C(FuturePath R, ℝ))
    (nonnegative : ∀ a, 0 ≤ g a) (superharmonic : ∀ a, weightedTransferOperator ψ g a ≤ g a)
    (b : FuturePath R) (zero : g (futureShift b) = 0) : g b = 0 := by
  have branch := weightedTransfer_branch_lower ψ g nonnegative b
  have bound := superharmonic (futureShift b)
  change weightedTransfer ψ g (futureShift b) ≤ g (futureShift b) at bound
  rw [zero] at bound
  have nonpositive : g b ≤ 0 := by nlinarith [Real.exp_pos (ψ b)]
  exact le_antisymm nonpositive (nonnegative b)

theorem nonnegative_superharmonic_zero_prehistory (ψ g : C(FuturePath R, ℝ))
    (nonnegative : ∀ a, 0 ≤ g a) (superharmonic : ∀ a, weightedTransferOperator ψ g a ≤ g a)
    (n : ℕ) (b : FuturePath R) (zero : g ((futureShift : FuturePath R → FuturePath R)^[n] b) = 0) :
    g b = 0 := by
  induction n generalizing b with
  | zero => exact zero
  | succ n induction =>
    rw [iterate_succ_apply] at zero
    exact nonnegative_superharmonic_zero_predecessor ψ g nonnegative superharmonic b
      (induction (futureShift b) zero)

theorem nonnegative_superharmonic_zero_everywhere (ψ g : C(FuturePath R, ℝ))
    (nonnegative : ∀ a, 0 ≤ g a) (superharmonic : ∀ a, weightedTransferOperator ψ g a ≤ g a)
    (N : ℕ) (connections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val N = j)
    (b : FuturePath R) (zero : g b = 0) : ∀ a, g a = 0 := by
  intro a
  obtain ⟨c, convergence, preimages⟩ := exists_convergent_future_prehistories N connections a b
  have zeros (m : ℕ) : g (c m) = 0 :=
    nonnegative_superharmonic_zero_prehistory ψ g nonnegative superharmonic (m + N) (c m)
      (by rw [preimages m, zero])
  have limit := g.continuous.continuousAt.tendsto.comp convergence
  have same : Tendsto (fun m => g (c m)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zeros] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique limit same

@[expose] def complexFunctionNorm (f : C(FuturePath R, ℂ)) : C(FuturePath R, ℝ) :=
  ⟨fun a => ‖f a‖, f.continuous.norm⟩

variable [Nonempty (FuturePath R)]

theorem complex_unital_eigenfunction_constant_modulus (ψ : C(FuturePath R, ℝ)) (f : C(FuturePath R, ℂ))
    (eigenvalue : ℂ) (unit : ‖eigenvalue‖ = 1)
    (unital : weightedTransferOperator ψ 1 = 1)
    (eigen : complexWeightedTransferOperator ψ f = eigenvalue • f)
    (N : ℕ) (connections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val N = j) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a, ‖f a‖ = M := by
  obtain ⟨b, _, maximal⟩ := isCompact_univ.exists_isMaxOn (s := (univ : Set (FuturePath R)))
    univ_nonempty (complexFunctionNorm f).continuous.continuousOn
  let M := ‖f b‖
  let g : C(FuturePath R, ℝ) := M • 1 - complexFunctionNorm f
  have nonnegative (a : FuturePath R) : 0 ≤ g a := by
    have bound := maximal (mem_univ a)
    change ‖f a‖ ≤ M at bound
    change 0 ≤ M * 1 - ‖f a‖
    linarith
  have superharmonic (a : FuturePath R) : weightedTransferOperator ψ g a ≤ g a := by
    have domination := complexWeightedTransfer_norm_domination ψ f a
    have eigenpoint := congrArg (fun v : C(FuturePath R, ℂ) => v a) eigen
    change complexWeightedTransfer ψ f a = eigenvalue * f a at eigenpoint
    rw [eigenpoint, norm_mul, unit, one_mul] at domination
    change ‖f a‖ ≤ weightedTransferOperator ψ (complexFunctionNorm f) a at domination
    have image : weightedTransferOperator ψ g = M • 1 - weightedTransferOperator ψ (complexFunctionNorm f) := by
      dsimp only [g]
      rw [map_sub, map_smul, unital]
    rw [image]
    change M * 1 - weightedTransferOperator ψ (complexFunctionNorm f) a ≤ M * 1 - ‖f a‖
    linarith
  have zero : g b = 0 := by change ‖f b‖ * 1 - ‖f b‖ = 0; ring
  have allZero := nonnegative_superharmonic_zero_everywhere ψ g nonnegative superharmonic N connections b zero
  refine ⟨M, norm_nonneg _, ?_⟩
  intro a
  have identity := allZero a
  change M * 1 - ‖f a‖ = 0 at identity
  linarith

end LeanShared.BilateralShadowingCoding
