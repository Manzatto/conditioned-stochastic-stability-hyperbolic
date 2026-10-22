module
public import LeanShared.Analysis.ConeFourierLocalizedTransferResolution
public import LeanShared.Analysis.PhysicalRowLimitBound
public import Mathlib.MeasureTheory.Integral.Prod

/-! Actual physical rows are reconstructed from the finite Fourier resolution.
The passage to the full localized transfer uses pointwise convergence and
Fatou, so no convergence of a formal block matrix is an input. -/
public noncomputable section
open MeasureTheory Filter
open scoped SchwartzMap ENNReal Topology BigOperators
namespace LeanShared.ConeFourierPhysicalRowReconstruction
open ConeDyadicSymbols ConeFourierPairingResolution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Cp Cm : Set E}

theorem bound (χ : RadialCutoff) (Φ : AngularCutoff Cp Cm)
    (f output : 𝓢(E,ℂ)) (G : E → E) (continuousG : Continuous G)
    (g : E → ℂ) (continuousg : Continuous g) (compactg : HasCompactSupport g)
    (μ : Measure E) (row : ℕ → Bool → ℝ≥0∞) (B : ℝ≥0∞)
    (blocks : ∀ n s, (∫⁻ x,‖∫ w,FourierSchwartzKernel.kernel output (x-w)*g w*
      ConeFourierBlocks.block (symbols χ Φ (n,s)) f (G w)‖ₑ ∂μ) ≤ row n s)
    (rows : ∀ N, ∑ n ∈ Finset.range (N+1),∑ s : Bool,row n s ≤ B) :
    (∫⁻ x,‖∫ w,FourierSchwartzKernel.kernel output (x-w)*g w*f (G w)‖ₑ ∂μ) ≤ B := by
  let action (v : 𝓢(E,ℂ)) (x : E) : ℂ :=
    ∫ w,FourierSchwartzKernel.kernel output (x-w)*g w*v (G w)
  have measurable (v : 𝓢(E,ℂ)) : Measurable (action v) := by
    have joint : Continuous (fun p : E × E =>
        FourierSchwartzKernel.kernel output (p.1-p.2)*g p.2*v (G p.2)) := by fun_prop
    exact joint.stronglyMeasurable.integral_prod_right'.measurable
  apply PhysicalRowLimitBound.bound μ (fun N => action (partialSum χ Φ N f)) (action f)
    (fun N => measurable _) (ConeFourierLocalizedTransferResolution.converges
      χ Φ f output G continuousG g continuousg compactg) B
  intro N
  have expansion := ConeFourierLocalizedTransferResolution.finite_expansion
    χ Φ f output G continuousG g continuousg compactg N
  calc
    _ = ∫⁻ x,‖∑ n ∈ Finset.range (N+1),∑ s : Bool,
        action (ConeFourierBlocks.block (symbols χ Φ (n,s)) f) x‖ₑ ∂μ := by
      congr 1; funext x; rw [show action (partialSum χ Φ N f) x = _ from expansion x]
    _ ≤ ∫⁻ x,∑ n ∈ Finset.range (N+1),∑ s : Bool,
        ‖action (ConeFourierBlocks.block (symbols χ Φ (n,s)) f) x‖ₑ ∂μ := by
      apply lintegral_mono
      intro x
      exact (enorm_sum_le _ _).trans (Finset.sum_le_sum (fun n _ => enorm_sum_le _ _))
    _ = ∑ n ∈ Finset.range (N+1),∑ s : Bool,
        ∫⁻ x,‖action (ConeFourierBlocks.block (symbols χ Φ (n,s)) f) x‖ₑ ∂μ := by
      rw [lintegral_finsetSum _ (fun n _ => Finset.measurable_sum _ (fun s _ => (measurable _).enorm))]
      apply Finset.sum_congr rfl
      intro n _
      exact lintegral_finsetSum _ (fun s _ => (measurable _).enorm)
    _ ≤ ∑ n ∈ Finset.range (N+1),∑ s : Bool,row n s :=
      Finset.sum_le_sum (fun n _ => Finset.sum_le_sum (fun s _ => blocks n s))
    _ ≤ B := rows N

end LeanShared.ConeFourierPhysicalRowReconstruction
