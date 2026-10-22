module

public import ConditionedStochasticStabilityHyperbolic.Paper.FixedCubeNoise

/-! The literal Whitney perturbation represented in the ordinary map space used
by the analytic model. Outside its small window we use the deterministic map;
this changes no positive-noise germ and imposes no continuity in ε. -/

@[expose] public noncomputable section
open Set
open scoped Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared
variable {E M ι Parameters : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MetricSpace Parameters] {T : M ≃ₜ M} {r : ℝ}
  {F : Maps (E := E) (ι := ι) T r} {evaluate : Parameters → M → M}
namespace Representation
variable (p : Representation F Parameters evaluate)

def fixedParameters (ε : ℝ≥0) (z : FixedControl (ι := ι)) : Parameters :=
  if h : 0 < ε ∧ ε ≤ p.window then
    p.represent ε h.1 h.2 (NoiseCubeRescaling.rescale (ε : ℝ) h.1 z)
  else p.reference

omit [FiniteDimensional ℝ E] in
theorem fixedParameters_close (ε : ℝ≥0) (z : FixedControl (ι := ι)) :
    dist (p.fixedParameters ε z) p.reference ≤ p.constant * (ε : ℝ) := by
  by_cases h : 0 < ε ∧ ε ≤ p.window
  · simp only [fixedParameters, dite_eq_left h]
    exact p.close ε h.1 h.2 _
  · simp only [fixedParameters, dite_eq_right h, dist_self]
    exact mul_nonneg p.constant_nonnegative ε.property

omit [FiniteDimensional ℝ E] in
theorem fixedParameters_continuous (ε : ℝ≥0) : Continuous (p.fixedParameters ε) := by
  change Continuous (fun z => p.fixedParameters ε z)
  by_cases h : 0 < ε ∧ ε ≤ p.window
  · simp only [fixedParameters, dite_eq_left h]
    exact (p.continuous ε h.1 h.2).comp (NoiseCubeRescaling.rescale (ε : ℝ) h.1).continuous
  · simp only [fixedParameters, dite_eq_right h]
    exact continuous_const

omit [FiniteDimensional ℝ E] in
theorem fixedParameters_zero (z : FixedControl (ι := ι)) :
    p.fixedParameters 0 z = p.reference := by
  simp only [fixedParameters, lt_self_iff_false, false_and, ↓reduceDIte]

omit [FiniteDimensional ℝ E] in
theorem actual_fixedMap (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ p.window)
    (x : M) (z : FixedControl (ι := ι)) :
    evaluate (p.fixedParameters ε z) x = F.fixedMap ε x z := by
  have h : 0 < ε ∧ ε ≤ p.window := ⟨hε, hw⟩
  simp only [fixedParameters, dite_eq_left h, Maps.fixedMap, dite_eq_left hε]
  exact congrFun (p.actual_map ε hε hw _) x

omit [FiniteDimensional ℝ E] in
theorem actual_reference (z : FixedControl (ι := ι)) :
    evaluate (p.fixedParameters 0 z) = T := by
  rw [p.fixedParameters_zero]
  exact p.reference_map

end Representation
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
