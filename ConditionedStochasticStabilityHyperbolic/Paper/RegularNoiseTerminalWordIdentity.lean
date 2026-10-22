module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseCaptureWordIdentity
public import LeanShared.Analysis.ActualFiniteLabelledWordProduct
public import LeanShared.Analysis.ActualWordWeightProduct
public import LeanShared.Geometry.FiniteCaptureWordCutoffs
public import LeanShared.Geometry.FiniteCaptureTerminalCutoffs
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.Ring

/-! Retain the complete beta word and an independent input slot. The
auxiliary terminal factor is part of the exact literal labelled action,
including the zero-length case. -/
@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff BigOperators
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared ActualFiniteRegularWord CylinderPrincipalCoefficient
variable {E M Ω I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [Fintype I]
  {K : Set M} {v : I → Set M}

omit [MetricSpace M] [Fintype I] in
private theorem prefix_pair_terminal (F : Ω → M → M) {N : ℕ}
    (controls : Fin N → Ω) (labels : Fin (N + 1) → I) (n : ℕ) (x : M) :
    prefixOrbit (fun z : Ω × Option I => F z.1) (captureLetters controls labels) n x =
      prefixOrbit F controls n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h : n < N
    · simp only [prefixOrbit, dite_eq_left h, captureLetters, ih]
    · simp only [prefixOrbit, dite_eq_right h, ih]

theorem capture_terminal_word_amplitude_identity (F : Ω → M → M)
    (d : FiniteSmoothCapturePartition.Data (E := E) K v) (g : M → ℝ)
    (τ : I → M → ℂ) {N : ℕ} (controls : Fin N → Ω)
    (labels : Fin (N + 1) → I) (j : I) (x : M) :
    (d.beta (labels 0) x : ℂ) *
      ActualFiniteLabelledWord.amplitude F (captureWeights d g)
        (fun m => captureTerminals d (captureEnd labels) m * τ j m)
        (List.ofFn (captureLetters controls labels)) x =
      ((FiniteSmoothCapturePartition.wordCutoff d
        (fun k : Fin (N + 1) => prefixOrbit F controls k.val x) labels : ℂ) *
        ActualFiniteRegularWord.weight F g (List.ofFn controls) x) *
      τ j (prefixOrbit F controls N x) := by
  have product :
      ActualFiniteLabelledWord.amplitude F (captureWeights d g)
        (fun m => captureTerminals d (captureEnd labels) m * τ j m)
        (List.ofFn (captureLetters controls labels)) x =
      ActualFiniteLabelledWord.amplitude F (captureWeights d g)
        (captureTerminals d (captureEnd labels))
        (List.ofFn (captureLetters controls labels)) x *
        τ j (prefixOrbit F controls N x) := by
    rw [ActualFiniteLabelledWord.amplitude_ofFn_eq_product,
      ActualFiniteLabelledWord.amplitude_ofFn_eq_product]
    simp only [prefix_pair_terminal, mul_assoc]
  rw [product, ← mul_assoc, capture_word_amplitude_identity]

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
