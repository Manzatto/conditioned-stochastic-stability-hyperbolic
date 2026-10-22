module
public import LeanShared.Dynamics.PeriodicWeightProduct
public import LeanShared.Dynamics.PeriodicLocalization
public import LeanShared.Dynamics.BasicHyperbolicLefschetzPartition
public import LeanShared.Analysis.IntegralDisjointPieces

/-! Setup for the regularized Lefschetz trace of a weighted hyperbolic dynamics. A basic
set with a `C^r` diffeomorphism (`r > 1`), Euclidean splitting frames, a finite chart
family covering the basic set, cutoffs forming a partition of unity on the basic set with
supports well inside the marked chart sets, and a weight that is positive on the basic set,
supported in the closed isolating neighborhood and `q`-Hölder along iterates.
The regularized chart integrand with kernel `κ` at time `n` is
`z ↦ c_i(φ_i⁻¹ z) g_n(φ_i⁻¹ z) κ(φ_i(T^n(φ_i⁻¹ z)) - z)` on the chart target. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold Bundle Metric MeasureTheory
open scoped Manifold ContDiff Topology NNReal
open LeanShared.PeriodicChartConstants
namespace LeanShared.HyperbolicBasicSet

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M}

/-- Inputs of the regularized Lefschetz trace comparison. -/
structure TraceSetup (b : BasicData (E := E) T Λ V) where
  forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T
  inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm
  r : ℝ
  one_lt_r : 1 < r
  regular : FractionalManifoldRegularity.Regular (E := E) (F := E) r T
  frame : IsometricFraming b.hyperbolic
  charts : ChartFamily E M
  cover : Λ ⊆ ⋃ i, charts.domain i
  cutoff : charts.ι → M → ℝ
  cutoff_continuous : ∀ i, Continuous (cutoff i)
  cutoff_nonneg : ∀ i x, 0 ≤ cutoff i x
  cutoff_sum : ∀ x ∈ Λ, ∑ i ∈ (@Finset.univ _ charts.fintype), cutoff i x = 1
  margin : ℝ
  margin_pos : 0 < margin
  cutoff_margin : ∀ i, cthickening margin (tsupport (cutoff i)) ⊆ charts.marked i
  weight : M → ℝ
  weight_continuous : Continuous weight
  weight_nonneg : ∀ x, 0 ≤ weight x
  weight_pos : ∀ x ∈ Λ, 0 < weight x
  weight_support : ∀ x, weight x ≠ 0 → x ∈ closure V
  q : ℝ
  q_pos : 0 < q
  q_lt_one : q < 1
  weight_regular : ∀ l : ℕ, FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q
    (fun x => weight ((T : M → M)^[l] x))

namespace TraceSetup

variable {b : BasicData (E := E) T Λ V} (s : TraceSetup b)

/-- The regularized chart integrand at time `n` with kernel `κ`. -/
@[expose] def integrand (κ : E → ℝ) (n : ℕ) (i : s.charts.ι) (z : E) : ℝ :=
  Set.indicator (s.charts.chart i).target (fun z =>
    s.cutoff i ((s.charts.chart i).symm z) *
      PeriodicChartChains.weightProduct T s.weight n ((s.charts.chart i).symm z) *
      Set.indicator (s.charts.chart i).source (fun y => κ (s.charts.chart i y - z))
        ((T : M → M)^[n] ((s.charts.chart i).symm z))) z

/-- The regularized trace at time `n`. -/
@[expose] def trace [MeasurableSpace E] (μE : Measure E) (κ : E → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ (@Finset.univ _ s.charts.fintype), ∫ z, s.integrand κ n i z ∂μE

end TraceSetup
end LeanShared.HyperbolicBasicSet
