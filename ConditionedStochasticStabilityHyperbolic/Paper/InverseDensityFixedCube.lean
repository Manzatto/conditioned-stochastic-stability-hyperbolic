module

public import ConditionedStochasticStabilityHyperbolic.Paper.InverseDensitySources
public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedFixedCubeNoise

/-! The constructed inverse-density source transports to the single fixed
cube and the literal analytic representation, with no extra noise hypothesis. -/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {T : M ≃ₜ M} {r : ℝ}

omit [FiniteDimensional ℝ E] in
def Maps.fixed_density_inputs (F : Maps (E := E) (ι := ι) T r) (L : Laws (ι := ι))
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ F.window)
    (V K G : Set M) (hK : IsCompact K) (w : K → ℝ) (hwt : Measurable w) (R δ : ℝ)
    (c : Global.NoFullSupportCollarDensityCertificate.Inputs T V K G hK (L.law ε)
      (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1)
      (F.raw_continuous ε hε hw).measurable w hwt R δ) :
    Global.NoFullSupportCollarDensityCertificate.Inputs T V K G hK (L.fixedLaw ε)
      (fun z : M × FixedControl (ι := ι) => F.fixedMap ε z.1 z.2)
      (F.fixedMap_measurable ε hε hw) w hwt R δ := by
  simpa only [Laws.fixedLaw, Maps.fixedMap, dite_eq_left hε] using
    c.reparametrize (NoiseCubeRescaling.rescale (ε : ℝ) hε)

variable {Parameters : Type*} [MetricSpace Parameters]
  {F : Maps (E := E) (ι := ι) T r} {evaluate : Parameters → M → M}

omit [FiniteDimensional ℝ E] in
def Representation.represented_density_inputs
    (p : Representation F Parameters evaluate) (L : Laws (ι := ι))
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ p.window)
    (V K G : Set M) (hK : IsCompact K) (w : K → ℝ) (hwt : Measurable w) (R δ : ℝ)
    (c : Global.NoFullSupportCollarDensityCertificate.Inputs T V K G hK (L.fixedLaw ε)
      (fun z : M × FixedControl (ι := ι) => F.fixedMap ε z.1 z.2)
      (F.fixedMap_measurable ε hε (hw.trans p.window_le)) w hwt R δ)
    (hF : Measurable (fun z : M × FixedControl (ι := ι) =>
      evaluate (p.fixedParameters ε z.2) z.1)) :
    Global.NoFullSupportCollarDensityCertificate.Inputs T V K G hK (L.fixedLaw ε)
      (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1)
      hF w hwt R δ := by
  have he : (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1) =
      (fun z : M × FixedControl (ι := ι) => F.fixedMap ε z.1 z.2) :=
    funext (fun z => p.actual_fixedMap ε hε hw z.1 z.2)
  revert hF
  rw [he]
  intro hF
  exact c

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
