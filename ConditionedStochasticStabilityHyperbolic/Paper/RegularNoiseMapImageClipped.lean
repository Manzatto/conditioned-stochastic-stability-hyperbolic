module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseMapImage
public import ConditionedStochasticStabilityHyperbolic.Paper.FixedCubeNoise
public import LeanShared.Analysis.FiniteBlockAnnealedEstimates

/-! The actual noise letters read on the fixed control cube: at scale
`0 < ε ≤ η` the literal noise map with the rescaled control, and the
deterministic reference otherwise. The family is continuous in the control,
uniformly close to the reference, and the reference is the zero-control
letter at the top scale. -/
@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set Filter Topology
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise.MapImage
open LeanShared
variable {E M ι : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace M] [CompactSpace M]
  [ChartedSpace E M] {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r)
  (hr : 1 ≤ r) (η : ℝ≥0) (hw : η ≤ F.window)

/-- The clipped actual letter on the fixed control cube. -/
def clipped (ε : ℝ≥0) (z : FixedControl (ι := ι)) : Space F hr η hw :=
  if h : 0 < ε ∧ ε ≤ η then
    noise F hr η hw ε h.1 h.2 (NoiseCubeRescaling.rescale (ε : ℝ) h.1 z)
  else reference F hr η hw

theorem clipped_pos {ε : ℝ≥0} (hp : 0 < ε) (hl : ε ≤ η) (z : FixedControl (ι := ι)) :
    clipped F hr η hw ε z = noise F hr η hw ε hp hl (NoiseCubeRescaling.rescale (ε : ℝ) hp z) := by
  unfold clipped
  rw [dite_eq_left_of_eq_true (eq_true ⟨hp, hl⟩)]

theorem clipped_off {ε : ℝ≥0} (h : ¬ (0 < ε ∧ ε ≤ η)) (z : FixedControl (ι := ι)) :
    clipped F hr η hw ε z = reference F hr η hw := by
  unfold clipped
  rw [dite_eq_right_of_eq_false (eq_false h)]

theorem clipped_zero (z : FixedControl (ι := ι)) :
    clipped F hr η hw 0 z = reference F hr η hw :=
  clipped_off F hr η hw (fun h => lt_irrefl _ h.1) z

theorem clipped_continuous (ε : ℝ≥0) : Continuous (clipped F hr η hw ε) := by
  by_cases h : 0 < ε ∧ ε ≤ η
  · have same : clipped F hr η hw ε = fun z =>
        noise F hr η hw ε h.1 h.2 (NoiseCubeRescaling.rescale (ε : ℝ) h.1 z) :=
      funext fun z => clipped_pos F hr η hw h.1 h.2 z
    rw [same]
    exact (noise_continuous F hr η hw ε h.1 h.2).comp (NoiseCubeRescaling.rescale (ε : ℝ) h.1).continuous
  · have same : clipped F hr η hw ε = fun _ => reference F hr η hw :=
      funext fun z => clipped_off F hr η hw h z
    rw [same]
    exact continuous_const

theorem clipped_dist (ε : ℝ≥0) (z : FixedControl (ι := ι)) :
    dist (clipped F hr η hw ε z) (reference F hr η hw) ≤ F.constant * (ε : ℝ) := by
  by_cases h : 0 < ε ∧ ε ≤ η
  · rw [clipped_pos F hr η hw h.1 h.2 z]
    exact noise_proximity F hr η hw ε h.1 h.2 _
  · rw [clipped_off F hr η hw h z, dist_self]
    exact mul_nonneg F.constant_positive.le ε.coe_nonneg

theorem small_mul {C x ζ : ℝ} (hC : 0 ≤ C) (hx : 0 ≤ x) (_hζ : 0 < ζ) (small : x < ζ / (C + 1)) :
    C * x < ζ := by
  have hpos : 0 < C + 1 := by linarith
  have key : x * (C + 1) < ζ := (lt_div_iff₀ hpos).mp small
  nlinarith

theorem clipped_tendsto :
    Tendsto (fun p : ℝ≥0 × FixedControl (ι := ι) => clipped F hr η hw p.1 p.2) ((𝓝 0) ×ˢ ⊤)
      (𝓝 (reference F hr η hw)) := by
  rw [Metric.tendsto_nhds]
  intro ζ hζ
  have hC := F.constant_positive
  have hδ : 0 < ζ / (F.constant + 1) := by positivity
  have near : ∀ᶠ ε : ℝ≥0 in 𝓝 0, (ε : ℝ) < ζ / (F.constant + 1) :=
    (NNReal.continuous_coe.tendsto 0).eventually (gt_mem_nhds (by rw [NNReal.coe_zero]; exact hδ))
  filter_upwards [near.prod_inl ⊤] with p hp
  exact (clipped_dist F hr η hw p.1 p.2).trans_lt (small_mul hC.le p.1.coe_nonneg hζ hp)

theorem zero_mem_cube : (0 : Control (ι := ι)) ∈
    (NoiseCubeRescaling.cube (ι := ι) (η : ℝ) : Set (Control (ι := ι))) := by
  intro i
  simp

/-- The reference letter is the zero-control letter at the top scale. -/
theorem reference_eq_noise (positive : 0 < η) :
    reference F hr η hw = noise F hr η hw η positive le_rfl ⟨0, zero_mem_cube η⟩ := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  exact (F.zero_control η positive hw x).symm

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise.MapImage

namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise.WordLists
open LeanShared

theorem listWord_map {Ω₁ Ω₂ X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (A : Ω₂ → X →L[ℂ] X) (f : Ω₁ → Ω₂) (w : List Ω₁) :
    FiniteBlockAnnealedEstimates.listWord (fun z => A (f z)) w =
      FiniteBlockAnnealedEstimates.listWord A (w.map f) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change (A (f a)).comp (FiniteBlockAnnealedEstimates.listWord (fun z => A (f z)) w) =
      (A (f a)).comp (FiniteBlockAnnealedEstimates.listWord A (w.map f))
    rw [ih]

theorem map_eq_ofFn {α β : Type*} (f : α → β) (w : List α) {N : ℕ} (hlen : w.length = N) :
    w.map f = List.ofFn (fun k : Fin N => f (w.get (Fin.cast hlen.symm k))) := by
  subst hlen
  apply List.ext_get
  · simp
  · intro n h1 h2
    simp

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise.WordLists
