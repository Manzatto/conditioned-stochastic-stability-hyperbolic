module

public import LeanShared.Dynamics.SymbolicResetVariation
public import LeanShared.Analysis.UniformGeometricTailBound
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-! The actual future-dependent potential retains exponential cylinder
variations.  This closes the regularity step in the explicit bilateral
cohomology construction, before one-sided transfer theory is used.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Function
open scoped BoundedContinuousFunction
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A]
  {R : A → A → Prop}

theorem futurePotential_hasExponentialVariations (φ : Path R → ℝ)
    (continuous : Continuous φ) (variation : HasExponentialVariations φ) :
    HasExponentialVariations (futurePotential φ) := by
  obtain ⟨θ₁, positive₁, small₁, C₁, nonnegative₁, bound₁⟩ := variation
  have original : HasExponentialVariations φ :=
    ⟨θ₁, positive₁, small₁, C₁, nonnegative₁, bound₁⟩
  obtain ⟨θ₂, positive₂, small₂, C₂, nonnegative₂, bound₂⟩ :=
    resetTransfer_hasExponentialVariations φ original
  let θ := max θ₁ θ₂
  have positive : 0 < θ := lt_of_lt_of_le positive₁ (le_max_left _ _)
  have small : θ < 1 := max_lt small₁ small₂
  let L := C₁ + C₂ + C₂ / θ₂
  have nonnegativeL : 0 ≤ L := by dsimp only [L]; positivity
  let bounded : Path R →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨futurePotential φ, futurePotential_continuous φ continuous original⟩
  have tail (n : ℕ) (large : 1 ≤ n) (a b : Path R) (same : WindowAgreement a b n) :
      ‖futurePotential φ b - futurePotential φ a‖ ≤ L * θ ^ n := by
    have first : |φ b - φ a| ≤ C₁ * θ ^ n :=
      (bound₁ n a b same).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ positive₁.le (le_max_left _ _) _) nonnegative₁)
    have second : |resetTransfer φ b - resetTransfer φ a| ≤ C₂ * θ ^ n :=
      (bound₂ n a b same).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ positive₂.le (le_max_right _ _) _) nonnegative₂)
    have shifted := bound₂ (n - 1) (shift R a) (shift R b)
      (by simpa only [iterate_one] using shift_windowAgreement a b n 1 large same)
    have cancel : C₂ * θ₂ ^ (n - 1) = (C₂ / θ₂) * θ₂ ^ n := by
      have identity : n = (n - 1) + 1 := by omega
      nth_rw 2 [identity]
      rw [pow_succ]
      field_simp
    have third : |resetTransfer φ (shift R b) - resetTransfer φ (shift R a)| ≤
        (C₂ / θ₂) * θ ^ n := by
      rw [cancel] at shifted
      exact shifted.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ positive₂.le (le_max_right _ _) _) (div_nonneg nonnegative₂ positive₂.le))
    have identity : futurePotential φ b - futurePotential φ a =
        (φ b - φ a) + (resetTransfer φ (shift R b) - resetTransfer φ (shift R a)) -
          (resetTransfer φ b - resetTransfer φ a) := by
      dsimp only [futurePotential]
      ring
    rw [identity, Real.norm_eq_abs]
    calc
      _ ≤ |φ b - φ a| + |resetTransfer φ (shift R b) - resetTransfer φ (shift R a)| +
          |resetTransfer φ b - resetTransfer φ a| := (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ C₁ * θ ^ n + (C₂ / θ₂) * θ ^ n + C₂ * θ ^ n := add_le_add (add_le_add first third) second
      _ = L * θ ^ n := by dsimp only [L]; ring
  obtain ⟨D, nonnegativeD, estimate⟩ := UniformGeometricTailBound.exists_bound
    (futurePotential φ) (fun n a b => WindowAgreement a b n) ‖bounded‖ L θ
    (norm_nonneg _) nonnegativeL positive small.le
    (fun a => bounded.norm_coe_le_norm a) 1 tail
  refine ⟨θ, positive, small, D, nonnegativeD, ?_⟩
  intro n a b same
  simpa only [Real.norm_eq_abs] using estimate n a b same

end LeanShared.BilateralShadowingCoding
