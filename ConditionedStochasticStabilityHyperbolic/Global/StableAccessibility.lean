module

public import ConditionedStochasticStabilityHyperbolic.Global.WeightedAccessibility
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Stable-orbit access using the actual strictly positive exponential weight

The global process uses exp(phi), even when a separate analytic cutoff weight
vanishes away from the basic sets. A fixed-radius local noise-image inclusion
and a deterministic noise parameter produce an actual feasible finite word
from a forward orbit approaching a positive basic set. No spectral positivity
basin or epsilon-dependent collar is used to choose the radius.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace ConditionedStochasticStabilityHyperbolic.Global.StableAccessibility

open LeanShared.NoiseAccessibility WeightedAccessibility

variable {X Ω : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Ω] [MeasurableSpace Ω]

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Ω] [MeasurableSpace Ω] in
private theorem controlDomain_append (F : X × Ω → X) (U : Set X) (w : X → ℝ)
    (V : Set X) (a b : List Ω) :
    controlDomain F U w V (a ++ b) =
      controlDomain F U w (controlDomain F U w V b) a := by
  induction a with
  | nil => rfl
  | cons ω a ih => simp only [List.cons_append, controlDomain, ih]

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Ω] [MeasurableSpace Ω] in
private theorem controlDomain_mono (F : X × Ω → X) (U : Set X) (w : X → ℝ)
    {V W : Set X} (hVW : V ⊆ W) (controls : List Ω) :
    controlDomain F U w V controls ⊆ controlDomain F U w W controls := by
  induction controls with
  | nil => exact hVW
  | cons ω controls ih =>
      intro x hx
      exact ⟨hx.1, hx.2.1, ih hx.2.2⟩

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Ω] [MeasurableSpace Ω] in
private theorem deterministic_prefix (T : X → X) (F : X × Ω → X) (ω₀ : Ω)
    (hzero : ∀ x, F (x, ω₀) = T x) (U : Set X) (w : X → ℝ)
    (hw : ∀ x, 0 < w x) (V : Set X) (n : ℕ) (x : X)
    (hlive : ∀ i, i ≤ n → T^[i] x ∈ U) (hend : T^[n] x ∈ V) :
    x ∈ controlDomain F U w V (List.replicate n ω₀) := by
  induction n generalizing x with
  | zero => simpa [controlDomain] using hend
  | succ n ih =>
      rw [List.replicate_succ, controlDomain]
      refine ⟨hw x, ?_, ?_⟩
      · change F (x, ω₀) ∈ U
        rw [hzero]
        exact hlive 1 (Nat.succ_le_succ (Nat.zero_le n))
      · change F (x, ω₀) ∈ controlDomain F U w V (List.replicate n ω₀)
        rw [hzero]
        apply ih (T x)
        · intro i hi
          rw [← Function.iterate_succ_apply]
          exact hlive (i + 1) (Nat.succ_le_succ hi)
        · simpa only [Function.iterate_succ_apply] using hend

omit [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Ω] [MeasurableSpace Ω] in
/-- A stable orbit can be steered into the basic set with finitely many
actual controls. The local range radius is independent of the eigenfunction.
The exponential departure weight is positive at every prefix state. -/
theorem exists_feasible_word_to_basicSet
    (T : X → X) (F : X × Ω → X) (ω₀ : Ω) (hzero : ∀ x, F (x, ω₀) = T x)
    (U Λ : Set X) (hΛU : Λ ⊆ U) (φ : X → ℝ) (x : X)
    (hlive : ∀ i : ℕ, T^[i] x ∈ U) {δ : ℝ} (hδ : 0 < δ)
    (himage : ∀ z ∈ U, ∀ y ∈ U, dist (T z) y < δ → ∃ ω, F (z, ω) = y)
    (happroach : ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Λ, dist (T^[n + 1] x) y < r) :
    ∃ controls : List Ω, x ∈ controlDomain F U (fun z => Real.exp (φ z)) Λ controls := by
  obtain ⟨n, y, hy, hnear⟩ := happroach δ hδ
  have hnear' : dist (T (T^[n] x)) y < δ := by
    simpa only [Function.iterate_succ_apply'] using hnear
  obtain ⟨ω, hω⟩ := himage (T^[n] x) (hlive n) y (hΛU hy) hnear'
  refine ⟨List.replicate n ω₀ ++ [ω], ?_⟩
  rw [controlDomain_append]
  apply deterministic_prefix T F ω₀ hzero U (fun z => Real.exp (φ z))
    (fun z => Real.exp_pos _) _ n x (fun i _hi => hlive i)
  change 0 < Real.exp (φ (T^[n] x)) ∧ F (T^[n] x, ω) ∈ U ∧ F (T^[n] x, ω) ∈ Λ
  exact ⟨Real.exp_pos _, hω.symm ▸ hΛU hy, hω.symm ▸ hy⟩

/-- Applied to the genuine transfer eigenfunction, stable-orbit access gives
positive starting-state eigenfunction value and hence the correct basin for
conditioned averages. -/
theorem eigenfunction_pos_of_stable_orbit
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] [ρ.IsOpenPosMeasure]
    (T : X → X) (F : X × Ω → X) (hF : Measurable F) (hFc : Continuous F)
    (ω₀ : Ω) (hzero : ∀ x, F (x, ω₀) = T x)
    (U : Set X) (hU : IsOpen U) (Λ : Set X) (hΛU : Λ ⊆ U)
    (φ : X → ℝ) (hφ : Measurable φ) (R : ℝ) (hR : 0 < R)
    (hbound : ∀ x, Real.exp (φ x) ≤ R)
    (h : X → ℝ) (hhc : Continuous h) (hh0 : ∀ x, 0 ≤ h x)
    (ell : ℝ) (hell : 0 < ell)
    (heigen : ∀ x, (∫ y, h y ∂(NoiseKernel.chain ρ F hF U hU.measurableSet
      (fun z => Real.exp (φ z)) (Real.measurable_exp.comp hφ) R hR hbound).killedTransition x) = ell * h x)
    (hhi : ∀ x, Integrable h (LeanShared.RandomMapKernel.killed ρ F hF U hU.measurableSet x))
    (hΛpos : ∀ y ∈ Λ, 0 < h y) (x : X)
    (hlive : ∀ i : ℕ, T^[i] x ∈ U) {δ : ℝ} (hδ : 0 < δ)
    (himage : ∀ z ∈ U, ∀ y ∈ U, dist (T z) y < δ → ∃ ω, F (z, ω) = y)
    (happroach : ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Λ, dist (T^[n + 1] x) y < r) :
    0 < h x := by
  obtain ⟨controls, hcontrols⟩ := exists_feasible_word_to_basicSet T F ω₀ hzero U Λ hΛU φ x
    hlive hδ himage happroach
  apply eigenfunction_pos_of_controlWord ρ F hF hFc U hU (fun z => Real.exp (φ z))
    (Real.measurable_exp.comp hφ) R hR hbound h hhc hh0 ell hell heigen hhi controls x
  exact controlDomain_mono F U (fun z => Real.exp (φ z)) hΛpos controls hcontrols

end ConditionedStochasticStabilityHyperbolic.Global.StableAccessibility
