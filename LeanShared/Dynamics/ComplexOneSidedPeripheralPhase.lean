module

public import LeanShared.Dynamics.ComplexOneSidedModulusMaximum

/-! Equality in the actual positive branch average propagates the phase
of every peripheral eigenfunction through every literal predecessor.
Two consecutive actual graph connection lengths then force the
peripheral eigenvalue to equal one.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function Filter Topology
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop}

private theorem complex_phase_unique (z d : ℂ) (equalNorm : ‖z‖ = ‖d‖)
    (realInner : (star d * z).re = ‖d‖ ^ 2) : z = d := by
  have square : ‖z - d‖ ^ 2 = ‖z‖ ^ 2 + ‖d‖ ^ 2 - 2 * (star d * z).re := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  have zero : ‖z - d‖ ^ 2 = 0 := by rw [square, equalNorm, realInner]; ring
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp zero))

theorem complex_unital_eigenfunction_predecessor_phase (ψ : C(FuturePath R, ℝ)) (f : C(FuturePath R, ℂ))
    (eigenvalue : ℂ) (unit : ‖eigenvalue‖ = 1)
    (unital : weightedTransferOperator ψ 1 = 1)
    (eigen : complexWeightedTransferOperator ψ f = eigenvalue • f)
    (M : ℝ) (constantModulus : ∀ a, ‖f a‖ = M) (b : FuturePath R) :
    f b = eigenvalue * f (futureShift b) := by
  let a := futureShift b
  let d := eigenvalue * f a
  have normD : ‖d‖ = M := by dsimp only [d]; rw [norm_mul, unit, one_mul, constantModulus]
  let projected := complexFunctionReal ((star d) • f)
  let g : C(FuturePath R, ℝ) := (‖d‖ ^ 2) • 1 - projected
  have nonnegative (c : FuturePath R) : 0 ≤ g c := by
    have realBound : (star d * f c).re ≤ ‖d‖ ^ 2 := by
      calc
        _ ≤ ‖star d * f c‖ := Complex.re_le_norm _
        _ = ‖d‖ * ‖f c‖ := by rw [norm_mul, norm_star]
        _ = ‖d‖ ^ 2 := by rw [constantModulus, ← normD]; ring
    change 0 ≤ ‖d‖ ^ 2 * 1 - (star d * f c).re
    linarith
  have projectedImage : weightedTransferOperator ψ projected a =
      (star d * complexWeightedTransferOperator ψ f a).re := by
    have identity := congrArg (fun q : C(FuturePath R, ℝ) => q a)
      (complexWeightedTransfer_power_real ψ ((star d) • f) 1)
    rw [pow_one, pow_one] at identity
    change (complexWeightedTransferOperator ψ ((star d) • f) a).re =
      weightedTransferOperator ψ projected a at identity
    rw [map_smul] at identity
    exact identity.symm
  have imageZero : weightedTransferOperator ψ g a = 0 := by
    have image : weightedTransferOperator ψ g = (‖d‖ ^ 2) • 1 - weightedTransferOperator ψ projected := by
      dsimp only [g]
      rw [map_sub, map_smul, unital]
    rw [image]
    change ‖d‖ ^ 2 * 1 - weightedTransferOperator ψ projected a = 0
    rw [projectedImage, eigen]
    change ‖d‖ ^ 2 * 1 - (star d * d).re = 0
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  have branch := weightedTransfer_branch_lower ψ g nonnegative b
  change Real.exp (ψ b) * g b ≤ weightedTransferOperator ψ g a at branch
  rw [imageZero] at branch
  have zero : g b = 0 := by nlinarith [nonnegative b, Real.exp_pos (ψ b)]
  have realInner : (star d * f b).re = ‖d‖ ^ 2 := by
    change ‖d‖ ^ 2 * 1 - (star d * f b).re = 0 at zero
    linarith
  exact complex_phase_unique (f b) d ((constantModulus b).trans normD.symm) realInner

omit [DiscreteTopology A] [CompactSpace A] [Fintype A] in
theorem future_phase_prehistory (f : FuturePath R → ℂ) (eigenvalue : ℂ)
    (phase : ∀ b, f b = eigenvalue * f (futureShift b)) (n : ℕ) (b : FuturePath R) :
    f b = eigenvalue ^ n * f ((futureShift : FuturePath R → FuturePath R)^[n] b) := by
  induction n generalizing b with
  | zero => simp only [pow_zero, iterate_zero_apply, one_mul]
  | succ n induction =>
    rw [iterate_succ_apply, pow_succ']
    calc
      f b = eigenvalue * f (futureShift b) := phase b
      _ = eigenvalue * (eigenvalue ^ n * f ((futureShift : FuturePath R → FuturePath R)^[n] (futureShift b))) :=
        congrArg (eigenvalue * ·) (induction (futureShift b))
      _ = _ := by ring

variable [Nonempty (FuturePath R)]

theorem complex_unital_peripheral_eigenvalue_eq_one (ψ : C(FuturePath R, ℝ)) (f : C(FuturePath R, ℂ))
    (eigenvalue : ℂ) (unit : ‖eigenvalue‖ = 1) (nonzero : f ≠ 0)
    (unital : weightedTransferOperator ψ 1 = 1)
    (eigen : complexWeightedTransferOperator ψ f = eigenvalue • f)
    (N : ℕ)
    (connections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val N = j)
    (nextConnections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val (N + 1) = j) :
    eigenvalue = 1 := by
  obtain ⟨M, _, modulus⟩ := complex_unital_eigenfunction_constant_modulus ψ f eigenvalue unit unital eigen N connections
  have phase := complex_unital_eigenfunction_predecessor_phase ψ f eigenvalue unit unital eigen M modulus
  have witness : ∃ b, f b ≠ 0 := by
    by_contra! allZero
    apply nonzero
    apply ContinuousMap.ext
    exact allZero
  obtain ⟨b, nonzeroB⟩ := witness
  obtain ⟨c, convergeC, preimagesC⟩ := exists_convergent_future_prehistories N connections b b
  obtain ⟨d, convergeD, preimagesD⟩ := exists_convergent_future_prehistories (N + 1) nextConnections b b
  have relation (m : ℕ) : f (d m) = eigenvalue * f (c m) := by
    have first := future_phase_prehistory f eigenvalue phase (m + N) (c m)
    have second := future_phase_prehistory f eigenvalue phase (m + (N + 1)) (d m)
    rw [preimagesC m] at first
    rw [preimagesD m] at second
    rw [first, second, show m + (N + 1) = (m + N) + 1 by omega, pow_succ']
    ring
  have firstLimit := f.continuous.continuousAt.tendsto.comp convergeD
  have secondLimit : Tendsto (fun m => f (d m)) atTop (𝓝 (eigenvalue * f b)) := by
    simpa only [relation, Function.comp_def] using tendsto_const_nhds.mul (f.continuous.continuousAt.tendsto.comp convergeC)
  have identity := tendsto_nhds_unique firstLimit secondLimit
  have equality : (1 : ℂ) * f b = eigenvalue * f b := by simpa only [one_mul] using identity
  exact (mul_right_cancel₀ nonzeroB equality).symm

end LeanShared.BilateralShadowingCoding
