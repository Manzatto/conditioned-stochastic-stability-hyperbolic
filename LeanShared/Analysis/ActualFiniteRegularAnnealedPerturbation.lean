module

public import LeanShared.Analysis.CommonFiniteRegularTransferCompatibility
public import LeanShared.Analysis.CompactAnnealedPerturbation

/-!
# Mixed-norm convergence for the constructed finite-regularity transfers

The operators are the literal weighted-function transfers constructed from
finite-regularity embeddings, not supplied random operator families. Common
smooth approximation derives strong/intermediate/weak compatibility.
Actual core interpolation supplies core convergence; boundedness and
compactness promote it to mixed operator-norm convergence. Pointwise core
noise continuity gives completed Bochner measurability. The actual metric
small-noise bound then yields convergence of the constructed averages.

The finite-regularity realization types can use exponents strictly between
the relevant positive anisotropic exponent and `r-1`; they must not be
identified with the highest fractional Hölder topology without the
interpolation proof. The physical compact two-loss inclusion and its
canonical core identities are supplied by the checked embedding producers.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal

namespace LeanShared.ActualFiniteRegularAnnealedPerturbation

open DyadicCompletion FiniteRegularTransferRealization AnnealedOperatorBounds

theorem exists_actual_averages_mixed_norm_tendsto
    {X G Ω Core VS VH VW High Low : Type*}
    [PseudoMetricSpace G] [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [SecondCountableTopology Ω]
    [AddCommGroup Core] [Module ℂ Core]
    [NormedAddCommGroup VS] [NormedSpace ℂ VS] [CompleteSpace VS]
    [NormedAddCommGroup VH] [NormedSpace ℂ VH]
    [NormedAddCommGroup VW] [NormedSpace ℂ VW] [CompleteSpace VW]
    [NormedAddCommGroup High] [NormedSpace ℂ High]
    [NormedAddCommGroup Low] [NormedSpace ℂ Low]
    (qS : Core →ₗ[ℂ] VS) (qH : Core →ₗ[ℂ] VH) (qW : Core →ₗ[ℂ] VW)
    (smooth : Core →ₗ[ℂ] (X → ℂ))
    (viewHigh : High →ₗ[ℂ] (X → ℂ)) (hinjHigh : Function.Injective viewHigh)
    (viewLow : Low →ₗ[ℂ] (X → ℂ)) (hinjLow : Function.Injective viewLow)
    (downgrade : High →L[ℂ] Low) (hview : ∀ f, viewLow (downgrade f) = viewHigh f)
    (F : G → X → X) (g : X → ℝ)
    (hhigh : ∀ a c, weightedComposition (F a) g (smooth c) ∈ viewHigh.range)
    (hlow : ∀ a c, weightedComposition (F a) g (smooth c) ∈ viewLow.range)
    (realizeStrong : High →L[ℂ] closedCore qS) (realizeWeak : Low →L[ℂ] closedCore qW)
    (i : closedCore qS →L[ℂ] closedCore qH) (hicompact : IsCompactOperator i)
    (j : closedCore qS →L[ℂ] closedCore qW)
    (hi : ∀ c, i (coreLift qS c) = coreLift qH c)
    (hj : ∀ c, j (coreLift qS c) = coreLift qW c)
    (approximation : High → ℕ → Core)
    (happroxStrong : ∀ f, Tendsto (fun n => coreLift qS (approximation f n)) atTop (𝓝 (realizeStrong f)))
    (happroxWeak : ∀ f, Tendsto (fun n => coreLift qW (approximation f n)) atTop
      (𝓝 (realizeWeak (downgrade f))))
    (LS LW : ℝ) (hLS : 0 ≤ LS) (hLW : 0 ≤ LW)
    (hstrong : ∀ a c, ‖targetCore qS smooth High viewHigh hinjHigh realizeStrong F g hhigh a c‖ ≤ LS * ‖qS c‖)
    (hweak : ∀ a c,
      ‖FiniteRegularTransferBetweenSpaces.targetCore smooth Low viewLow hinjLow realizeWeak F g hlow a c‖ ≤ LW * ‖qH c‖)
    (hlowCore : ∀ c, Continuous (fun a => regularAction smooth Low viewLow hinjLow F g hlow a c))
    (T : G) (noise : ℝ≥0 → Ω → G) (noiseConstant : ℝ)
    (hclose : ∀ ε ω, dist (noise ε ω) T ≤ noiseConstant * (ε : ℝ))
    (μ : ℝ≥0 → Measure Ω) [∀ ε, IsProbabilityMeasure (μ ε)]
    (hnoiseCore : ∀ ε c, Continuous (fun ω =>
      regularAction smooth High viewHigh hinjHigh F g hhigh (noise ε ω) c)) :
    let PS := operator qS smooth High viewHigh hinjHigh realizeStrong F g hhigh
    ∃ average : ℝ≥0 → closedCore qS →L[ℂ] closedCore qS,
      (∀ ε x, average ε x = ∫ ω, PS (noise ε ω) x ∂μ ε) ∧
      Tendsto (fun ε => ‖j.comp (average ε - PS T)‖) (𝓝 0) (𝓝 0) := by
  let PS := operator qS smooth High viewHigh hinjHigh realizeStrong F g hhigh
  let AR := FiniteRegularTransferBetweenSpaces.operator qH smooth Low viewLow hinjLow realizeWeak F g hlow
  have hcompat : ∀ p, (AR p).comp i = j.comp (PS p) :=
    CommonFiniteRegularTransferCompatibility.operator_compatibility qS qH qW smooth
      viewHigh hinjHigh viewLow hinjLow downgrade hview F g hhigh hlow realizeStrong realizeWeak
      i j hi hj approximation happroxStrong happroxWeak LS LW hstrong hweak
  have hrectbound : ∀ p, ‖AR p‖ ≤ LW :=
    FiniteRegularTransferBetweenSpaces.operator_norm_le qH smooth Low viewLow hinjLow realizeWeak F g hlow LW hweak hLW
  have hPbound : ∀ ε ω, ‖PS (noise ε ω)‖ ≤ LS := fun ε ω =>
    operator_norm_le qS smooth High viewHigh hinjHigh realizeStrong F g hhigh LS hstrong hLS (noise ε ω)
  have hcore : ∀ c, Tendsto (fun p => AR p (coreLift qH c)) (𝓝 T) (𝓝 (AR T (coreLift qH c))) :=
    FiniteRegularTransferBetweenSpaces.core_tendsto qH smooth Low viewLow hinjLow realizeWeak F g hlow LW hweak hlowCore T
  have hmeas : ∀ ε x, AEStronglyMeasurable (fun ω => PS (noise ε ω) x) (μ ε) := by
    intro ε x
    apply DenseCoreRandomOperators.aestronglyMeasurable_of_continuous_core (μ ε) _ (coreLift qS) (coreLift_dense qS) _ x
    intro c
    exact (realizeStrong.continuous.comp (hnoiseCore ε c)).congr
      (fun ω => (operator_core qS smooth High viewHigh hinjHigh realizeStrong F g hhigh LS hstrong (noise ε ω) c).symm)
  let average := fun ε => pointwiseAnnealed (μ ε) (fun ω => PS (noise ε ω)) (hmeas ε) LS (hPbound ε)
  refine ⟨average, fun ε x => pointwiseAnnealed_apply (μ ε) _ (hmeas ε) LS (hPbound ε) x, ?_⟩
  exact CompactAnnealedPerturbation.mixed_norm_average_tendsto_zero i hicompact j AR PS T hcompat LW hLW
    (Eventually.of_forall hrectbound) (coreLift qH) (coreLift_dense qH) hcore noise (𝓝 0)
    (CompactAnnealedPerturbation.common_neighborhood_of_uniform_distance T noise noiseConstant hclose)
    μ hmeas (fun _ => LS) hPbound

end LeanShared.ActualFiniteRegularAnnealedPerturbation
