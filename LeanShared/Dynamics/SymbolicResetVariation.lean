module

public import LeanShared.Dynamics.SymbolicFutureCohomology
public import LeanShared.Analysis.GeometricSeriesWindowVariation

/-! The canonical cohomology transfer has actual exponential cylinder
variations.  Uniform geometric tails and the retained past-reset window
geometry give a three-block estimate; no regular transfer is assumed.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Function
variable {A : Type*} [TopologicalSpace A] {R : A → A → Prop}

theorem shift_windowAgreement (a b : Path R) (radius n : ℕ) (bound : n ≤ radius)
    (same : WindowAgreement a b radius) :
    WindowAgreement ((shift R : _ → _)^[n] a) ((shift R : _ → _)^[n] b) (radius - n) := by
  intro k lower upper
  rw [MarkovFinitePathRealization.shift_iterate_val, MarkovFinitePathRealization.shift_iterate_val]
  exact same (k + n) (by omega) (by omega)

theorem resetTransfer_hasExponentialVariations (φ : Path R → ℝ)
    (variation : HasExponentialVariations φ) : HasExponentialVariations (resetTransfer φ) := by
  obtain ⟨θ, positive, small, C, nonnegativeC, bound⟩ := variation
  have uniform (n : ℕ) (a : Path R) : ‖resetDifference φ a n‖ ≤ C * θ ^ n :=
    resetDifference_bound φ C θ bound a n
  have head (m : ℕ) (a b : Path R) (same : WindowAgreement a b (3 * m))
      (n : ℕ) (early : n < m) :
      ‖resetDifference φ b n - resetDifference φ a n‖ ≤ 2 * C * θ ^ (2 * m) := by
    have indexBound : n ≤ 3 * m := by omega
    have first := bound (3 * m - n) ((shift R : _ → _)^[n] a) ((shift R : _ → _)^[n] b)
      (shift_windowAgreement a b (3 * m) n indexBound same)
    have second := bound (3 * m - n) ((shift R : _ → _)^[n] (pastReset a))
      ((shift R : _ → _)^[n] (pastReset b))
      (shift_windowAgreement (pastReset a) (pastReset b) (3 * m) n indexBound
        (pastReset_windowAgreement a b (3 * m) same))
    have powerBound : C * θ ^ (3 * m - n) ≤ C * θ ^ (2 * m) :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one positive.le small.le (by omega : 2 * m ≤ 3 * m - n)) nonnegativeC
    have identity : resetDifference φ b n - resetDifference φ a n =
        (φ ((shift R : _ → _)^[n] b) - φ ((shift R : _ → _)^[n] a)) -
        (φ ((shift R : _ → _)^[n] (pastReset b)) - φ ((shift R : _ → _)^[n] (pastReset a))) := by
      dsimp only [resetDifference]
      ring
    rw [identity]
    calc
      _ ≤ ‖φ ((shift R : _ → _)^[n] b) - φ ((shift R : _ → _)^[n] a)‖ +
          ‖φ ((shift R : _ → _)^[n] (pastReset b)) - φ ((shift R : _ → _)^[n] (pastReset a))‖ := norm_sub_le _ _
      _ ≤ C * θ ^ (3 * m - n) + C * θ ^ (3 * m - n) :=
        add_le_add (by simpa only [Real.norm_eq_abs] using first) (by simpa only [Real.norm_eq_abs] using second)
      _ ≤ 2 * C * θ ^ (2 * m) := by linarith
  obtain ⟨D, nonnegativeD, estimate⟩ := GeometricSeriesWindowVariation.exists_bound
    (fun n a => resetDifference φ a n) (fun m a b => WindowAgreement a b (3 * m))
    C θ nonnegativeC positive small uniform head
  apply hasExponentialVariations_of_block (resetTransfer φ) 3 (by omega) θ D positive small nonnegativeD
  intro n a b same
  simpa only [resetTransfer, Real.norm_eq_abs] using estimate n a b same

end LeanShared.BilateralShadowingCoding
