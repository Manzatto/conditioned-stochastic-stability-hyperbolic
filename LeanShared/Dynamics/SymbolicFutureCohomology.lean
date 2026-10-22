module

public import LeanShared.Dynamics.SymbolicPastReset
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! An actual exponentially varying bilateral potential is continuously
cohomologous to a future-dependent potential.  The transfer function is
the literal summable series of canonical past-reset differences.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Function
variable {A : Type*} [TopologicalSpace A] {R : A → A → Prop}

@[expose] def resetDifference (φ : Path R → ℝ) (a : Path R) (n : ℕ) : ℝ :=
  φ ((shift R : _ → _)^[n] a) - φ ((shift R : _ → _)^[n] (pastReset a))

@[expose] def resetTransfer (φ : Path R → ℝ) (a : Path R) : ℝ := ∑' n : ℕ, resetDifference φ a n

@[expose] def futurePotential (φ : Path R → ℝ) (a : Path R) : ℝ :=
  φ a + resetTransfer φ (shift R a) - resetTransfer φ a

theorem resetDifference_bound (φ : Path R → ℝ) (C θ : ℝ)
    (bound : ∀ radius : ℕ, ∀ a b : Path R, WindowAgreement a b radius → |φ b - φ a| ≤ C * θ ^ radius)
    (a : Path R) (n : ℕ) : ‖resetDifference φ a n‖ ≤ C * θ ^ n := by
  simpa only [resetDifference, Real.norm_eq_abs, abs_sub_comm] using
    bound n ((shift R : _ → _)^[n] a) ((shift R : _ → _)^[n] (pastReset a)) (shift_pastReset_window a n)

theorem resetDifference_summable (φ : Path R → ℝ) (variation : HasExponentialVariations φ) (a : Path R) :
    Summable (resetDifference φ a) := by
  obtain ⟨θ, positive, small, C, _nonnegative, bound⟩ := variation
  exact Summable.of_norm_bounded ((summable_geometric_of_lt_one positive.le small).mul_left C)
    (resetDifference_bound φ C θ bound a)

theorem resetTransfer_sub_of_future (φ : Path R → ℝ) (variation : HasExponentialVariations φ)
    (a b : Path R) (same : FutureAgreement a b) :
    resetTransfer φ a - resetTransfer φ b =
      ∑' n : ℕ, (φ ((shift R : _ → _)^[n] a) - φ ((shift R : _ → _)^[n] b)) := by
  rw [resetTransfer, resetTransfer, ← (resetDifference_summable φ variation a).tsum_sub (resetDifference_summable φ variation b)]
  apply tsum_congr
  intro n
  dsimp only [resetDifference]
  rw [pastReset_eq_of_future a b same]
  ring

theorem future_difference_summable (φ : Path R → ℝ) (variation : HasExponentialVariations φ)
    (a b : Path R) (same : FutureAgreement a b) :
    Summable (fun n : ℕ => φ ((shift R : _ → _)^[n] a) - φ ((shift R : _ → _)^[n] b)) := by
  apply ((resetDifference_summable φ variation a).sub (resetDifference_summable φ variation b)).congr
  intro n
  dsimp only [resetDifference]
  rw [pastReset_eq_of_future a b same]
  ring

theorem futurePotential_cohomology (φ : Path R → ℝ) (a : Path R) :
    φ a = futurePotential φ a + resetTransfer φ a - resetTransfer φ (shift R a) := by
  dsimp only [futurePotential]
  ring

theorem futurePotential_depends_on_future (φ : Path R → ℝ) (variation : HasExponentialVariations φ)
    (a b : Path R) (same : FutureAgreement a b) : futurePotential φ a = futurePotential φ b := by
  have sameShift : FutureAgreement (shift R a) (shift R b) := fun n nonnegative => same (n + 1) (by omega)
  have transfer := resetTransfer_sub_of_future φ variation a b same
  have shifted := resetTransfer_sub_of_future φ variation (shift R a) (shift R b) sameShift
  have tail := (future_difference_summable φ variation a b same).tsum_eq_zero_add
  have tailIdentity : (∑' n : ℕ, (φ ((shift R : _ → _)^[n] (shift R a)) - φ ((shift R : _ → _)^[n] (shift R b)))) =
      ∑' n : ℕ, (φ ((shift R : _ → _)^[n + 1] a) - φ ((shift R : _ → _)^[n + 1] b)) := by
    apply tsum_congr
    intro n
    rw [iterate_succ_apply, iterate_succ_apply]
  rw [tailIdentity] at shifted
  simp only [iterate_zero_apply] at tail
  dsimp only [futurePotential]
  linarith

theorem resetTransfer_continuous [DiscreteTopology A] (φ : Path R → ℝ)
    (continuousφ : Continuous φ) (variation : HasExponentialVariations φ) : Continuous (resetTransfer φ) := by
  obtain ⟨θ, positive, small, C, _nonnegative, bound⟩ := variation
  apply continuous_tsum
  · intro n
    exact (continuousφ.comp ((shift R).continuous.iterate n)).sub
      (continuousφ.comp (((shift R).continuous.iterate n).comp pastReset_continuous))
  · exact (summable_geometric_of_lt_one positive.le small).mul_left C
  · exact fun n a => resetDifference_bound φ C θ bound a n

theorem futurePotential_continuous [DiscreteTopology A] (φ : Path R → ℝ)
    (continuousφ : Continuous φ) (variation : HasExponentialVariations φ) : Continuous (futurePotential φ) :=
  (continuousφ.add ((resetTransfer_continuous φ continuousφ variation).comp (shift R).continuous)).sub
    (resetTransfer_continuous φ continuousφ variation)

end LeanShared.BilateralShadowingCoding
