module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseCaptureLabelledAmplitude
public import LeanShared.Analysis.ActualFiniteLabelledWordProduct
public import LeanShared.Analysis.ActualWordWeightProduct
public import LeanShared.Geometry.FiniteCaptureWordCutoffs
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.Ring

/-! The fixed labelled operators represent exactly every observed capture
cutoff, times the original signed accumulated weight. The initial cutoff
is supplied once by the chart localizer; the zero-length terminal is one. -/
@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff BigOperators
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared ActualFiniteRegularWord CylinderPrincipalCoefficient
variable {E M Ω I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [Fintype I]
  {K : Set M} {v : I → Set M}

def captureLetters {N : ℕ} (controls : Fin N → Ω) (labels : Fin (N + 1) → I) :
    Fin N → Ω × Option I :=
  fun j => (controls j, if j.val = 0 then none else some (labels j.castSucc))

def captureEnd {N : ℕ} (labels : Fin (N + 1) → I) : Option I :=
  if N = 0 then none else some (labels (Fin.last N))

omit [MetricSpace M] [Fintype I] in
private theorem prefix_pair (F : Ω → M → M) {N : ℕ}
    (controls : Fin N → Ω) (labels : Fin (N + 1) → I) (n : ℕ) (x : M) :
    prefixOrbit (fun z : Ω × Option I => F z.1) (captureLetters controls labels) n x =
      prefixOrbit F controls n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h : n < N
    · simp only [prefixOrbit, dite_eq_left h, captureLetters, ih]
    · simp only [prefixOrbit, dite_eq_right h, ih]

theorem capture_word_amplitude_identity (F : Ω → M → M)
    (d : FiniteSmoothCapturePartition.Data (E := E) K v) (g : M → ℝ)
    {N : ℕ} (controls : Fin N → Ω) (labels : Fin (N + 1) → I) (x : M) :
    (d.beta (labels 0) x : ℂ) *
      ActualFiniteLabelledWord.amplitude F (captureWeights d g)
        (captureTerminals d (captureEnd labels)) (List.ofFn (captureLetters controls labels)) x =
      (FiniteSmoothCapturePartition.wordCutoff d
        (fun j : Fin (N + 1) => prefixOrbit F controls j.val x) labels : ℂ) *
      ActualFiniteRegularWord.weight F g (List.ofFn controls) x := by
  classical
  rw [ActualFiniteLabelledWord.amplitude_ofFn_eq_product]
  simp_rw [prefix_pair]
  rw [← ActualWordMicrolocalBound.realWeight_cast,
    ActualWordWeightProduct.realWeight_ofFn_eq_product]
  simp only [FiniteSmoothCapturePartition.wordCutoff, Complex.ofReal_prod]
  cases N with
  | zero =>
    simp [captureEnd, captureTerminals, prefixOrbit]
  | succ N =>
    have factors (j : Fin (N + 1)) :
        captureWeights d g ((captureLetters controls labels j).2) (prefixOrbit F controls j.val x) =
          (g (prefixOrbit F controls j.val x) : ℂ) *
            (if j.val = 0 then 1 else (d.beta (labels j.castSucc)
              (prefixOrbit F controls j.val x) : ℂ)) := by
      by_cases h : j.val = 0
      · simp [captureLetters, captureWeights, h]
      · simp [captureLetters, captureWeights, h]
    simp_rw [factors]
    rw [Finset.prod_mul_distrib]
    have cutoffs :
        (∏ j : Fin (N + 1), if j.val = 0 then (1 : ℂ) else
          (d.beta (labels j.castSucc) (prefixOrbit F controls j.val x) : ℂ)) =
        ∏ j : Fin N, (d.beta (labels j.succ.castSucc)
          (prefixOrbit F controls j.succ.val x) : ℂ) := by
      rw [Fin.prod_univ_succ]
      simp only [Fin.val_zero, ite_true, Fin.val_succ, Nat.add_one_ne_zero, ite_false, one_mul]
    rw [cutoffs]
    simp only [captureEnd, Nat.add_one_ne_zero, ite_false, captureTerminals]
    have fullCutoffs :
        (∏ j : Fin (N + 1 + 1),
          (d.beta (labels j) (prefixOrbit F controls j.val x) : ℂ)) =
        (d.beta (labels 0) x : ℂ) *
          ((∏ j : Fin N, (d.beta (labels j.succ.castSucc)
              (prefixOrbit F controls j.succ.val x) : ℂ)) *
            (d.beta (labels (Fin.last (N + 1)))
              (prefixOrbit F controls (N + 1) x) : ℂ)) := by
      rw [Fin.prod_univ_succ]
      congr 1
      rw [Fin.prod_univ_castSucc]
      rfl
    rw [fullCutoffs]
    ring

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
