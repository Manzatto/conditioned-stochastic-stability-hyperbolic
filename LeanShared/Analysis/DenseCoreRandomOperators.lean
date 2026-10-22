module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Noise orbits on completed spaces from a genuine dense core

A uniformly bounded operator family extends continuous core noise orbits
to continuous orbits on the completion. Strong and AE strong measurability
need even less: fixed-state operator continuity and dense approximation
suffice, without a uniform bound or separability of the whole state space.
Continuity/measurability of the actual smooth-core noise orbits remains the
precise classical composition-regularity input.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace LeanShared.DenseCoreRandomOperators

variable {𝕜 Ω E Core : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Uniform boundedness makes convergence of the input uniform over all
noise parameters after applying the actual operators. -/
theorem tendstoUniformly_apply (A : Ω → E →L[𝕜] E) (L : ℝ)
    (hbound : ∀ ω, ‖A ω‖ ≤ L) (u : ℕ → E) (x : E)
    (hu : Tendsto u atTop (𝓝 x)) :
    TendstoUniformly (fun n ω => A ω (u n)) (fun ω => A ω x) atTop := by
  have hd : Tendsto (fun n => L * dist x (u n)) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => x) atTop (𝓝 x) := tendsto_const_nhds
    have hL : Tendsto (fun _ : ℕ => L) atTop (𝓝 L) := tendsto_const_nhds
    simpa using hL.mul (hc.dist hu)
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [hd (gt_mem_nhds hε)] with n hn
  intro ω
  calc
    dist (A ω x) (A ω (u n)) = ‖A ω (x - u n)‖ := by rw [dist_eq_norm, map_sub]
    _ ≤ ‖A ω‖ * ‖x - u n‖ := (A ω).le_opNorm _
    _ ≤ L * dist x (u n) := by
      rw [dist_eq_norm]
      exact mul_le_mul_of_nonneg_right (hbound ω) (norm_nonneg _)
    _ < ε := hn

/-- No operator-norm continuity is needed: continuous noise orbits on a
dense core and a common norm bound imply noise continuity everywhere. -/
theorem continuous_of_denseRange [TopologicalSpace Ω]
    (A : Ω → E →L[𝕜] E) (L : ℝ) (hbound : ∀ ω, ‖A ω‖ ≤ L)
    (q : Core → E) (hq : DenseRange q)
    (hcore : ∀ f : Core, Continuous (fun ω => A ω (q f))) (x : E) :
    Continuous (fun ω => A ω x) := by
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp (hq x)
  have hc : ∀ n : ℕ, Continuous (fun ω => A ω (u n)) := by
    intro n
    obtain ⟨f, hf⟩ := hu n
    rw [← hf]
    exact hcore f
  exact (tendstoUniformly_apply A L hbound u x hlim).continuous
    (Filter.Eventually.of_forall hc).frequently

/-- Strong measurability extends from a dense core by pointwise limits.
No uniform bound, noise topology, or separability of `E` is required. -/
theorem stronglyMeasurable_of_denseRange [MeasurableSpace Ω]
    (A : Ω → E →L[𝕜] E) (q : Core → E) (hq : DenseRange q)
    (hcore : ∀ f : Core, StronglyMeasurable (fun ω => A ω (q f))) (x : E) :
    StronglyMeasurable (fun ω => A ω x) := by
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp (hq x)
  have hm : ∀ n : ℕ, StronglyMeasurable (fun ω => A ω (u n)) := by
    intro n
    obtain ⟨f, hf⟩ := hu n
    rw [← hf]
    exact hcore f
  apply stronglyMeasurable_of_tendsto atTop hm
  apply tendsto_pi_nhds.mpr
  intro ω
  exact ((A ω).continuous.tendsto x).comp hlim

/-- The AE version directly supplies pointwise inputs for actual annealed
operator construction, even when only core AE measurability is known. -/
theorem aestronglyMeasurable_of_denseRange [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Ω → E →L[𝕜] E) (q : Core → E) (hq : DenseRange q)
    (hcore : ∀ f : Core, AEStronglyMeasurable (fun ω => A ω (q f)) μ) (x : E) :
    AEStronglyMeasurable (fun ω => A ω x) μ := by
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp (hq x)
  have hm : ∀ n : ℕ, AEStronglyMeasurable (fun ω => A ω (u n)) μ := by
    intro n
    obtain ⟨f, hf⟩ := hu n
    rw [← hf]
    exact hcore f
  apply aestronglyMeasurable_of_tendsto_ae atTop hm
  exact ae_of_all μ fun ω => ((A ω).continuous.tendsto x).comp hlim

/-- Second-countable noise suffices for strongly measurable core orbits;
the completed state space can remain nonseparable. -/
theorem stronglyMeasurable_of_continuous_core [TopologicalSpace Ω]
    [MeasurableSpace Ω] [OpensMeasurableSpace Ω] [SecondCountableTopology Ω]
    (A : Ω → E →L[𝕜] E) (q : Core → E) (hq : DenseRange q)
    (hcore : ∀ f : Core, Continuous (fun ω => A ω (q f))) (x : E) :
    StronglyMeasurable (fun ω => A ω x) :=
  stronglyMeasurable_of_denseRange A q hq (fun f => (hcore f).stronglyMeasurable) x

theorem aestronglyMeasurable_of_continuous_core [TopologicalSpace Ω]
    [MeasurableSpace Ω] [OpensMeasurableSpace Ω] [SecondCountableTopology Ω]
    (μ : Measure Ω) (A : Ω → E →L[𝕜] E) (q : Core → E) (hq : DenseRange q)
    (hcore : ∀ f : Core, Continuous (fun ω => A ω (q f))) (x : E) :
    AEStronglyMeasurable (fun ω => A ω x) μ :=
  (stronglyMeasurable_of_continuous_core A q hq hcore x).aestronglyMeasurable

end LeanShared.DenseCoreRandomOperators
