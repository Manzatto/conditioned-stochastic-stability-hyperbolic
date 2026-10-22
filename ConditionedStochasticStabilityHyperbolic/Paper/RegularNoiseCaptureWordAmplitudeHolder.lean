module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseCaptureWordIdentity
import Mathlib.Tactic.Positivity

/-! Uniform Holder bounds for the full literal spatial cutoff product along
every noisy word. Every beta observation, including the terminal one, is
retained. One window and one pair of exponential constants works for the
whole finite chart family and all word lengths, including zero. -/
public noncomputable section
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction NNReal BigOperators
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared CylinderPrincipalCoefficient
variable {E M ι I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  [Fintype ι] [Fintype I]

theorem Maps.capture_word_amplitude_holder (μE : Measure E) [μE.IsAddHaarMeasure]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (hr : 1 ≤ r)
    (regular : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    {g : M → ℝ} {q a : ℝ} (ha : 0 < a) (ha1 : a < 1) (haq : a < q)
    (weight : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q g)
    {K : Set M} {v : I → Set M} (d : FiniteSmoothCapturePartition.Data (E := E) K v)
    (c : I → OpenPartialHomeomorph M E)
    (hc : ∀ i, c i ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (source : ∀ i, v i ⊆ (c i).source) :
    ∃ η : NNReal, 0 < η ∧ η ≤ F.window ∧ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∀ ε : NNReal, 0 < ε → ε ≤ η → ∀ N : ℕ,
      ∀ controls : Fin N → cube (ι := ι) ε, ∀ labels : Fin (N + 1) → I,
      ∃ f : E →ᵇ ℂ,
        (∀ x, f x = ChartLocalization.coordinate (c (labels 0))
          (fun m => (FiniteSmoothCapturePartition.wordCutoff d
            (fun j : Fin (N + 1) => prefixOrbit
              (fun control : cube (ι := ι) ε => F.family ε control.val) controls j.val m) labels : ℂ))
          (ActualFiniteRegularWord.weight
            (fun control : cube (ι := ι) ε => F.family ε control.val) g (List.ofFn controls)) x) ∧
        ‖f‖ ≤ C * B ^ N ∧
        tsupport (fun x => f x) ⊆
          ChartLocalization.localSupport (c (labels 0)) (fun m => (d.beta (labels 0) m : ℂ)) ∧
        ∀ x y, ‖f x - f y‖ ≤ (C * B ^ N) * dist x y ^ a := by
  classical
  have support (i : I) : tsupport (fun m => (d.beta i m : ℂ)) ⊆ (c i).source :=
    (tsupport_comp_subset Complex.ofReal_zero (d.beta i)).trans ((d.support i).trans (source i))
  have individual (i : I) := F.capture_labelled_amplitude_holder μE hr regular ha ha1 haq weight d
    (c i) (hc i) (fun m => (d.beta i m : ℂ))
    (Complex.ofRealCLM.contMDiff.comp (d.smooth i)) (HasCompactSupport.of_compactSpace _) (support i)
  choose radius positive below B C hB hC estimates using individual
  let windows : Option I → NNReal := fun k => match k with
    | none => F.window
    | some i => radius i
  let η : NNReal := Finset.univ.inf' Finset.univ_nonempty windows
  have positiveη : 0 < η := by
    apply (Finset.lt_inf'_iff Finset.univ_nonempty).mpr
    intro k _
    cases k with
    | none => exact F.window_positive
    | some i => exact positive i
  have belowOuter : η ≤ F.window := Finset.inf'_le windows (Finset.mem_univ none)
  have belowEach (i : I) : η ≤ radius i :=
    Finset.inf'_le windows (Finset.mem_univ (some i))
  let commonB : ℝ := ∑ i, B i
  let commonC : ℝ := ∑ i, C i
  have nonnegB : 0 ≤ commonB := Finset.sum_nonneg fun i _ => hB i
  have nonnegC : 0 ≤ commonC := Finset.sum_nonneg fun i _ => hC i
  have boundB (i : I) : B i ≤ commonB :=
    Finset.single_le_sum (fun k _ => hB k) (Finset.mem_univ i)
  have boundC (i : I) : C i ≤ commonC :=
    Finset.single_le_sum (fun k _ => hC k) (Finset.mem_univ i)
  refine ⟨η, positiveη, belowOuter, commonB, commonC, nonnegB, nonnegC, ?_⟩
  intro ε hp hw N controls labels
  let i := labels 0
  let maps : cube (ι := ι) ε → M → M := fun control => F.family ε control.val
  obtain ⟨f, formula, normBound, supportBound, holder⟩ := estimates i ε hp
    (hw.trans (belowEach i)) (List.ofFn (captureLetters controls labels)) (captureEnd labels)
  have commonBound : C i * B i ^ N ≤ commonC * commonB ^ N :=
    mul_le_mul (boundC i) (pow_le_pow_left₀ (hB i) (boundB i) N)
      (pow_nonneg (hB i) N) nonnegC
  refine ⟨f, ?_, ?_, supportBound, ?_⟩
  · intro y
    rw [formula]
    change _ = ChartLocalization.coordinate (c i) _ _ y
    by_cases inside : y ∈ (c i).target
    · simp only [ChartLocalization.coordinate, ite_eq_left inside]
      exact capture_word_amplitude_identity maps d g controls labels ((c i).symm y)
    · simp only [ChartLocalization.coordinate, ite_eq_right inside]
  · have normBound' : ‖f‖ ≤ C i * B i ^ N := by
      simpa only [List.length_ofFn] using normBound
    exact normBound'.trans commonBound
  · intro x y
    have holder' : ‖f x - f y‖ ≤ (C i * B i ^ N) * dist x y ^ a := by
      simpa only [List.length_ofFn] using holder x y
    exact holder'.trans
      (mul_le_mul_of_nonneg_right commonBound (Real.rpow_nonneg dist_nonneg _))

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
