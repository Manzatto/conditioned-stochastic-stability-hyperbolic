module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseWordContinuity
public import LeanShared.Geometry.CenteredManifoldCoordinates

/-! Joint control/state continuity of actual centered finite noisy words on
a valid chart ball. Chart validity is checked at the actual input and output. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set
open scoped Topology NNReal
open LeanShared.FiniteJetComposition LeanShared.CenteredManifoldCoordinates

theorem Maps.centered_word_continuousOn
    {E M ι P Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [MetricSpace M] [ChartedSpace E M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r)
    (ε : ℝ≥0) (positive : 0 < ε) (window : ε ≤ F.window) (N : ℕ)
    (c d : OpenPartialHomeomorph M E) (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] E)
    (a b : E) (radius : ℝ)
    (input : ∀ z : P, ‖z‖ ≤ radius → a + L z ∈ c.target)
    (output : ∀ controls : ℕ → cube (ι := ι) ε, ∀ z : P, ‖z‖ ≤ radius →
      word (fun n => F.family ε (controls n).val) N (c.symm (a + L z)) ∈ d.source) :
    ContinuousOn (fun p : (ℕ → cube (ι := ι) ε) × P =>
      centered L R a b (d ∘ word (fun n => F.family ε (p.1 n).val) N ∘ c.symm) p.2)
      (univ ×ˢ Metric.closedBall 0 radius) := by
  intro p hp
  have normBound : ‖p.2‖ ≤ radius := by simpa only [Metric.mem_closedBall, dist_zero_right] using hp.2
  have initial : ContinuousAt (fun q : (ℕ → cube (ι := ι) ε) × P => a + L q.2) p :=
    (L.continuous.comp continuous_snd).continuousAt.const_add a
  have decode : ContinuousAt (fun q : (ℕ → cube (ι := ι) ε) × P => c.symm (a + L q.2)) p :=
    (c.continuousAt_symm (input p.2 normBound)).comp_of_eq initial rfl
  have wordContinuous := (F.word_continuous ε positive window N).continuousAt.comp
    (continuousAt_fst.prodMk decode)
  have last : ContinuousAt (fun q : (ℕ → cube (ι := ι) ε) × P =>
      d (word (fun n => F.family ε (q.1 n).val) N (c.symm (a + L q.2)))) p :=
    (d.continuousAt (output p.1 p.2 normBound)).comp_of_eq wordContinuous rfl
  have final : ContinuousAt (fun q : (ℕ → cube (ι := ι) ε) × P =>
      R.symm (d (word (fun n => F.family ε (q.1 n).val) N (c.symm (a + L q.2))) - b)) p :=
    R.symm.continuous.continuousAt.comp_of_eq (last.sub_const b) rfl
  exact final.continuousWithinAt

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
