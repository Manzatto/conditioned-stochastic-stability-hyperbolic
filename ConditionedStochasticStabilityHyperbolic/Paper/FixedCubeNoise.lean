module

public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise

/-! The literal shrinking-cube family is reparametrized on one fixed cube.
Probability/full support and actual transition kernels are preserved separately
at every positive ε; no continuity of laws or maps in ε is introduced. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory IsManifold
open scoped Manifold ContDiff Topology NNReal ENNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]

abbrev FixedControl := NoiseCubeRescaling.cube (ι := ι) 1

def zeroFixed : FixedControl (ι := ι) := ⟨0, fun _ => by simp⟩

namespace Laws
variable (L : Laws (ι := ι))

instance law_probability (ε : ℝ≥0) : IsProbabilityMeasure (L.law ε) := L.probability ε

def fixedLaw (ε : ℝ≥0) : Measure (FixedControl (ι := ι)) :=
  if hε : 0 < ε then
    NoiseCubeRescaling.fixedLaw (NoiseCubeRescaling.rescale (ε : ℝ) hε) (L.law ε)
  else Measure.dirac zeroFixed

instance fixedLaw_probability (ε : ℝ≥0) : IsProbabilityMeasure (L.fixedLaw ε) := by
  let _ := L.probability ε
  by_cases hε : 0 < ε
  · simp only [fixedLaw, dite_eq_left hε]
    infer_instance
  · simp only [fixedLaw, dite_eq_right hε]
    infer_instance

theorem fixedLaw_full_support (ε : ℝ≥0) (hε : 0 < ε) : (L.fixedLaw ε).IsOpenPosMeasure := by
  let _ := L.full_support ε hε
  simp only [fixedLaw, dite_eq_left hε]
  infer_instance

end Laws

namespace Maps
variable {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r)

def fixedMap (ε : ℝ≥0) (x : M) (z : FixedControl (ι := ι)) : M :=
  if hε : 0 < ε then F.family ε ((NoiseCubeRescaling.rescale (ε : ℝ) hε) z).val x
  else T x

omit [FiniteDimensional ℝ E] in
theorem fixedMap_uniform_close (ε : ℝ≥0) (hε : 0 < ε) (hwindow : ε ≤ F.window)
    (x : M) (z : FixedControl (ι := ι)) :
    dist (F.fixedMap ε x z) (T x) ≤ F.constant * (ε : ℝ) := by
  simp only [fixedMap, dite_eq_left hε]
  exact F.uniform_close ε hε hwindow _ x

omit [FiniteDimensional ℝ E] in
theorem fixedMap_zero (x : M) (z : FixedControl (ι := ι)) : F.fixedMap 0 x z = T x := by
  simp only [fixedMap, lt_self_iff_false, ↓reduceDIte]

omit [FiniteDimensional ℝ E] in
theorem raw_continuous (ε : ℝ≥0) (hε : 0 < ε) (hwindow : ε ≤ F.window) :
    Continuous (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1) := by
  obtain ⟨O, _hO, hcube, hC⟩ := F.joint_C1 ε hε hwindow
  exact hC.continuousOn.comp_continuous
    ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)
    (fun z => ⟨hcube z.2.property, mem_univ _⟩)

omit [FiniteDimensional ℝ E] in
theorem fixedMap_continuous (ε : ℝ≥0) (hε : 0 < ε) (hwindow : ε ≤ F.window) :
    Continuous (fun z : M × FixedControl (ι := ι) => F.fixedMap ε z.1 z.2) := by
  have h := (F.raw_continuous ε hε hwindow).comp
    (continuous_fst.prodMk ((NoiseCubeRescaling.rescale (ε : ℝ) hε).continuous.comp continuous_snd))
  simpa only [Function.comp_def, fixedMap, dite_eq_left hε] using h

variable [MeasurableSpace M] [BorelSpace M]

omit [FiniteDimensional ℝ E] in
theorem raw_measurable (ε : ℝ≥0) (hε : 0 < ε) (hwindow : ε ≤ F.window) :
    Measurable (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1) :=
  (F.raw_continuous ε hε hwindow).measurable

omit [FiniteDimensional ℝ E] in
theorem fixedMap_measurable (ε : ℝ≥0) (hε : 0 < ε) (hwindow : ε ≤ F.window) :
    Measurable (fun z : M × FixedControl (ι := ι) => F.fixedMap ε z.1 z.2) :=
  (F.fixedMap_continuous ε hε hwindow).measurable

omit [FiniteDimensional ℝ E] in
theorem transition_fixed_cube (L : Laws (ι := ι))
    (ε : ℝ≥0) (hε : 0 < ε) (hwindow : ε ≤ F.window) :
    RandomMapKernel.transition (L.fixedLaw ε)
      (fun z : M × FixedControl (ι := ι) => F.fixedMap ε z.1 z.2)
      (F.fixedMap_measurable ε hε hwindow) =
    RandomMapKernel.transition (L.law ε)
      (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1)
      (F.raw_measurable ε hε hwindow) := by
  let _ := L.probability ε
  simpa only [Laws.fixedLaw, fixedMap, dite_eq_left hε] using NoiseCubeRescaling.transition_fixedLaw
    (NoiseCubeRescaling.rescale (ε : ℝ) hε) (L.law ε)
    (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1)
    (F.raw_measurable ε hε hwindow)

omit [FiniteDimensional ℝ E] in
theorem killed_fixed_cube (L : Laws (ι := ι))
    (ε : ℝ≥0) (hε : 0 < ε) (hwindow : ε ≤ F.window)
    (K : Set M) (hK : MeasurableSet K) :
    RandomMapKernel.killed (L.fixedLaw ε)
      (fun z : M × FixedControl (ι := ι) => F.fixedMap ε z.1 z.2)
      (F.fixedMap_measurable ε hε hwindow) K hK =
    RandomMapKernel.killed (L.law ε)
      (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1)
      (F.raw_measurable ε hε hwindow) K hK := by
  let _ := L.probability ε
  simpa only [Laws.fixedLaw, fixedMap, dite_eq_left hε] using NoiseCubeRescaling.killed_fixedLaw
    (NoiseCubeRescaling.rescale (ε : ℝ) hε) (L.law ε)
    (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1)
    (F.raw_measurable ε hε hwindow) K hK

end Maps
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
