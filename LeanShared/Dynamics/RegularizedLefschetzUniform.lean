module
public import LeanShared.Dynamics.RegularizedLefschetzSetup

/-! Uniform moduli for the regularized Lefschetz trace: chart maps and their inverses on
the compact closed chart domains, finitely many iterates and the cutoffs are uniformly
continuous with one modulus, and the marked chart images have a uniform margin inside the
chart domains. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold Bundle Metric
open scoped Manifold ContDiff Topology NNReal
open LeanShared.PeriodicChartConstants
namespace LeanShared.HyperbolicBasicSet

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]

theorem uniform_chart_symm (F : ChartFamily E M) (τ : ℝ) (hτ : 0 < τ) :
    ∃ s : ℝ, 0 < s ∧ ∀ c : F.ι, ∀ y ∈ F.chart c '' closure (F.domain c),
      ∀ y' ∈ F.chart c '' closure (F.domain c), ‖y - y'‖ ≤ s →
        dist ((F.chart c).symm y) ((F.chart c).symm y') < τ := by
  let := F.fintype
  have each (c : F.ι) : ∃ s : ℝ, 0 < s ∧ ∀ y ∈ F.chart c '' closure (F.domain c),
      ∀ y' ∈ F.chart c '' closure (F.domain c), dist y y' < s →
        dist ((F.chart c).symm y) ((F.chart c).symm y') < τ := by
    have uc := (F.compact_image c).uniformContinuousOn_of_continuous
      ((F.chart c).continuousOn_symm.mono (F.image_target c))
    rw [Metric.uniformContinuousOn_iff] at uc
    exact uc τ hτ
  choose s hs bound using each
  obtain ⟨s0, hs0, hle⟩ := exists_uniform_lower s hs
  refine ⟨s0 / 2, by positivity, fun c y hy y' hy' close => bound c y hy y' hy' ?_⟩
  rw [dist_eq_norm]
  linarith [hle c]

theorem uniform_chart (F : ChartFamily E M) (τ : ℝ) (hτ : 0 < τ) :
    ∃ s : ℝ, 0 < s ∧ ∀ c : F.ι, ∀ u ∈ closure (F.domain c), ∀ v ∈ closure (F.domain c),
      dist u v < s → ‖F.chart c u - F.chart c v‖ ≤ τ := by
  let := F.fintype
  have each (c : F.ι) : ∃ s : ℝ, 0 < s ∧ ∀ u ∈ closure (F.domain c),
      ∀ v ∈ closure (F.domain c), dist u v < s → dist (F.chart c u) (F.chart c v) < τ := by
    have uc := isClosed_closure.isCompact.uniformContinuousOn_of_continuous
      ((F.chart c).continuousOn.mono (F.closure_domain c))
    rw [Metric.uniformContinuousOn_iff] at uc
    exact uc τ hτ
  choose s hs bound using each
  obtain ⟨s0, hs0, hle⟩ := exists_uniform_lower s hs
  refine ⟨s0, hs0, fun c u hu v hv close => ?_⟩
  have := bound c u hu v hv (close.trans_le (hle c))
  rw [dist_eq_norm] at this
  exact this.le

theorem uniform_iterates (T : M ≃ₜ M) (N : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ s : ℝ, 0 < s ∧ ∀ u v : M, dist u v < s → ∀ l < N,
      dist ((T : M → M)^[l] u) ((T : M → M)^[l] v) < τ := by
  have each (l : Fin N) : ∃ s : ℝ, 0 < s ∧ ∀ u v : M, dist u v < s →
      dist ((T : M → M)^[l] u) ((T : M → M)^[l] v) < τ := by
    have uc := CompactSpace.uniformContinuous_of_continuous (T.continuous.iterate l)
    rw [Metric.uniformContinuous_iff] at uc
    exact uc τ hτ
  choose s hs bound using each
  obtain ⟨s0, hs0, hle⟩ := exists_uniform_lower s hs
  exact ⟨s0, hs0, fun u v close l hl => bound ⟨l, hl⟩ u v (close.trans_le (hle _))⟩

theorem uniform_function (f : M → ℝ) (hf : Continuous f) (τ : ℝ) (hτ : 0 < τ) :
    ∃ s : ℝ, 0 < s ∧ ∀ u v : M, dist u v < s → |f u - f v| < τ := by
  have uc := CompactSpace.uniformContinuous_of_continuous hf
  rw [Metric.uniformContinuous_iff] at uc
  obtain ⟨s, hs, bound⟩ := uc τ hτ
  exact ⟨s, hs, fun u v close => by
    have := bound close
    rwa [Real.dist_eq] at this⟩

theorem marked_margin (F : ChartFamily E M) :
    ∃ εm : ℝ, 0 < εm ∧ ∀ c : F.ι,
      cthickening εm (F.chart c '' F.marked c) ⊆ F.chart c '' F.domain c := by
  let := F.fintype
  have each (c : F.ι) : ∃ ε : ℝ, 0 < ε ∧
      cthickening ε (F.chart c '' F.marked c) ⊆ F.chart c '' F.domain c := by
    have compact : IsCompact (F.chart c '' F.marked c) :=
      (F.compact_marked c).image_of_continuousOn ((F.chart c).continuousOn.mono
        ((F.marked_domain c).trans (subset_closure.trans (F.closure_domain c))))
    have openImage : IsOpen (F.chart c '' F.domain c) :=
      (F.chart c).isOpen_image_of_subset_source (F.isOpen_domain c)
        (subset_closure.trans (F.closure_domain c))
    exact compact.exists_cthickening_subset_open openImage (image_mono (F.marked_domain c))
  choose ε hε sub using each
  obtain ⟨ε0, hε0, hle⟩ := exists_uniform_lower ε hε
  exact ⟨ε0, hε0, fun c => (cthickening_mono (hle c) _).trans (sub c)⟩

end LeanShared.HyperbolicBasicSet
