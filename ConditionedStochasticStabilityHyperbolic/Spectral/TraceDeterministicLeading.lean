module
public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiverani1999
public import LeanShared.Analysis.TraceLeadingSpectrum

/-! The deterministic leading record from regularized traces. A compact two-norm operator with
strong rate below `λ`, spectral radius at most `λ` and `λ ∈ σ(T)`, whose normalized `N`-th power
has regularized traces close to a sequence tending to one, has a separated rank-one
deterministic leading projection at rate `λ`. -/
public noncomputable section
open Filter
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem DeterministicLeading.of_traces (T : E →L[ℂ] E) (i : E →L[ℂ] W)
    (hi : IsCompactOperator i) (α R C D : ℝ) (hα : 0 ≤ α) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (estimate : ∀ n x, ‖(T ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖)
    (lam : ℝ) (lam_pos : 0 < lam) (gap : α < lam)
    (radius : spectralRadius ℂ T ≤ ENNReal.ofReal lam)
    (positive : (lam : ℂ) ∈ spectrum ℂ T) (N : ℕ) (hN : 0 < N)
    {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y]
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (F : ι → LeanShared.RegularizedTraceFunctional.Family E Y)
    (weak : ∀ v : E, ∀ φ : E →L[ℂ] ℂ, Tendsto (fun j => φ ((F j).smoothing v)) l
      (𝓝 (φ ((((lam : ℂ) ^ N)⁻¹ • T ^ N) v))))
    (t : ℕ → ℂ) (periodic : Tendsto t atTop (𝓝 1)) (δ : ι → ℝ)
    (compare : ∀ j, ∀ᶠ k in atTop,
      ‖(F j).traceL ((((lam : ℂ) ^ N)⁻¹ • T ^ N) ^ k) - t k‖ ≤ δ j)
    (small : Tendsto δ l (𝓝 0)) :
    ∃ d : DeterministicLeading T, d.rate = lam := by
  obtain ⟨h, m, q, q0, qlt, mh, Th, mT, complementary, separation, simple⟩ :=
    LeanShared.TraceLeadingSpectrum.leading T i hi α R C D hα hR hC hD estimate lam lam_pos
      gap radius positive N hN F weak t periodic δ compare small
  exact ⟨⟨lam, lam_pos, q, q0, qlt, h, m, mh, Th, mT, complementary, separation, simple⟩, rfl⟩

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
