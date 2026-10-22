module

public import AbsorbingMarkovChains.SpectralPowerBound
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Analysis.Normed.Operator.Banach

/-! Generic Banach-space conversion of constructed analytic eigenvectors.
Keeping the carrier abstract avoids normalizing concrete chart topologies. -/
public section
namespace ConditionedStochasticStabilityHyperbolic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem subordinate_spectrum_of_analytic_eigenvectors
    (P : E →L[ℂ] E) (Q : F →L[ℂ] F) (principal : ℝ)
    (witness : ∀ f : F, f ≠ 0 → ∀ z : ℂ, Q f = z • f → principal < ‖z‖ →
      ∃ v : E, v ≠ 0 ∧ P v = z • v) :
    ∀ f : F, f ≠ 0 → ∀ z : ℂ, Q f = z • f → principal < ‖z‖ → z ∈ spectrum ℂ P := by
  intro f hf z he hz
  obtain ⟨v, hv, hve⟩ := witness f hf z he hz
  rw [ContinuousLinearMap.spectrum_eq]
  exact (Module.End.hasEigenvalue_of_hasEigenvector
    (show Module.End.HasEigenvector (P : Module.End ℂ E) z v from
      ⟨Module.End.mem_eigenspace_iff.mpr hve, hv⟩)).mem_spectrum

end ConditionedStochasticStabilityHyperbolic
