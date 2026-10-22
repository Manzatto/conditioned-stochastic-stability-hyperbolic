module
public import LeanShared.Geometry.FiniteSmoothCapturePartition
public import LeanShared.Geometry.SmoothWeightCutoff
public import LeanShared.Geometry.SupportedChartExtension

/-! Auxiliary terminal cutoffs are one on the support of each input
partition function and remain supported inside the same controlled open
tube. They track Fourier blocks without duplicating the terminal beta
already contained in the actual localized input. -/
@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace LeanShared.FiniteSmoothCapturePartition
variable {E M I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M] [T2Space M] [CompactSpace M] [Fintype I]
  {K : Set M} {v : I → Set M} (d : Data (E := E) K v) (openV : ∀ i, IsOpen (v i))

include openV in
theorem Data.exists_terminal_cutoffs : ∃ τ : I → M → ℝ,
    (∀ i, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ)) ∞ (τ i)) ∧
    (∀ i x, 0 ≤ τ i x ∧ τ i x ≤ 1) ∧
    (∀ i, tsupport (τ i) ⊆ v i) ∧
    (∀ i, ∀ x ∈ tsupport (d.beta i), τ i x = 1) := by
  classical
  choose τ smooth bounds support one using (fun i => SmoothWeightCutoff.exists_cutoff (E := E)
    (tsupport (d.beta i)) (v i) (isClosed_tsupport _).isCompact (openV i) (d.support i))
  exact ⟨τ, smooth, bounds, support, one⟩

def Data.terminalCutoffs : I → M → ℝ := Classical.choose (d.exists_terminal_cutoffs openV)

theorem Data.terminalCutoffs_smooth (i : I) :
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ)) ∞ (d.terminalCutoffs openV i) :=
  (Classical.choose_spec (d.exists_terminal_cutoffs openV)).1 i

theorem Data.terminalCutoffs_bounds (i : I) (x : M) :
    0 ≤ d.terminalCutoffs openV i x ∧ d.terminalCutoffs openV i x ≤ 1 :=
  (Classical.choose_spec (d.exists_terminal_cutoffs openV)).2.1 i x

theorem Data.terminalCutoffs_support (i : I) : tsupport (d.terminalCutoffs openV i) ⊆ v i :=
  (Classical.choose_spec (d.exists_terminal_cutoffs openV)).2.2.1 i

theorem Data.terminalCutoffs_one (i : I) (x : M) (hx : x ∈ tsupport (d.beta i)) :
    d.terminalCutoffs openV i x = 1 :=
  (Classical.choose_spec (d.exists_terminal_cutoffs openV)).2.2.2 i x hx

theorem Data.terminalCutoffs_fix_beta (i : I) (x : M) :
    (d.terminalCutoffs openV i x : ℂ) * (d.beta i x : ℂ) = (d.beta i x : ℂ) := by
  by_cases zero : d.beta i x = 0
  · simp only [zero, Complex.ofReal_zero, mul_zero]
  · rw [d.terminalCutoffs_one openV i x (subset_tsupport _ zero), Complex.ofReal_one, one_mul]

end LeanShared.FiniteSmoothCapturePartition

namespace LeanShared.SupportedChartExtension
variable {Z M : Type*} [NormedAddCommGroup Z] [TopologicalSpace M]

theorem terminal_fixes_supported_input (c : OpenPartialHomeomorph M Z) (β τ : M → ℝ)
    (source : tsupport β ⊆ c.source) (one : ∀ x ∈ tsupport β, τ x = 1)
    (f : Z → ℂ) (supported : ∀ z ∉ c '' tsupport β, f z = 0) (x : M) :
    (τ x : ℂ) * function c f x = function c f x := by
  classical
  by_cases inside : x ∈ c.source
  · simp only [function, ite_eq_left inside]
    by_cases zero : f (c x) = 0
    · rw [zero, mul_zero]
    · have image : c x ∈ c '' tsupport β := by
        by_contra outside
        exact zero (supported _ outside)
      obtain ⟨y, hy, same⟩ := image
      have equal : y = x := c.injOn (source hy) inside same
      subst y
      rw [one x hy, Complex.ofReal_one, one_mul]
  · simp only [function, ite_eq_right inside, mul_zero]

end LeanShared.SupportedChartExtension
