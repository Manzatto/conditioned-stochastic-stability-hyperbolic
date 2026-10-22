module
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualOriginalGlobalChain
public import ConditionedStochasticStabilityHyperbolic.Paper.FixedCubeNoise

/-! Fixed-control realization of the exact original global chain, including
the deterministic zero scale. No original anisotropic representation is used. -/
public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise.ActualOriginalGlobalChain
open LeanShared
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] {T : M ≃ₜ M} {r : ℝ}

@[expose] def fixedRawMap (F : Maps (E := E) (ι := ι) T r) (ε : ℝ≥0) :
    M × FixedControl (ι := ι) → M :=
  if _small : 0 < ε ∧ ε ≤ F.window then fun z => F.fixedMap ε z.1 z.2 else fun z => T z.1

theorem fixedRawMap_measurable (F : Maps (E := E) (ι := ι) T r) (ε : ℝ≥0) :
    Measurable (fixedRawMap F ε) := by
  unfold fixedRawMap
  split
  · rename_i small
    exact F.fixedMap_measurable ε small.1 small.2
  · exact T.continuous.measurable.comp measurable_fst

theorem rawChain_fixed (F : Maps (E := E) (ι := ι) T r) (L : Laws (ι := ι))
    (K : Set M) (hK : MeasurableSet K) (w : M → ℝ) (hw : Measurable w)
    (R : ℝ) (hR : 0 < R) (bound : ∀ x, w x ≤ R) (ε : ℝ≥0) :
    rawChain F L K hK w hw R hR bound ε =
      NoiseKernel.chain (L.fixedLaw ε) (fixedRawMap F ε) (fixedRawMap_measurable F ε)
        K hK w hw R hR bound := by
  by_cases small : 0 < ε ∧ ε ≤ F.window
  · rw [rawChain_eq F L K hK w hw R hR bound ε small.1 small.2]
    unfold NoiseKernel.chain
    congr 1
    simpa only [fixedRawMap, dite_eq_left small] using
      (F.killed_fixed_cube L ε small.1 small.2 K hK).symm
  · have same : RandomMapKernel.transition (L.law ε) (rawMap F ε) (rawMap_measurable F ε) =
        RandomMapKernel.transition (L.fixedLaw ε) (fixedRawMap F ε)
          (fixedRawMap_measurable F ε) := by
      ext x s hs
      simp only [RandomMapKernel.transition_apply, rawMap, fixedRawMap, dite_eq_right small]
      simp
    unfold rawChain NoiseKernel.chain
    congr 1
    exact congrArg (fun P => P.restrict hK) same

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise.ActualOriginalGlobalChain
