module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseLocalFirstHolder
public import LeanShared.Analysis.CenteredFrameDerivative
import all LeanShared.Geometry.CompactUniformCenteredCharts

/-! The literal noise hypotheses give one common spatial tube, noise
window, and first-derivative Holder bound on a compact region of any genuine
chart pair, including every bounded affine normalization of those charts. -/
public noncomputable section
open Set IsManifold Metric
open scoped NNReal Manifold ContDiff Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LeanShared.CenteredManifoldCoordinates
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]

theorem Maps.uniform_chart_first_holder_tube {T : M ≃ₜ M} {r α : ℝ}
    (F : Maps (E := E) (ι := ι) T r) (positiveα : 0 < α) (subunitα : α < 1)
    (lower : α+1 < r) (regular : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
    (K : Set E) (compact : IsCompact K)
    (inside : K ⊆ c.target ∩ (T ∘ c.symm) ⁻¹' d.source) :
    ∃ radius > 0, ∃ η : ℝ≥0, 0 < η ∧ η ≤ F.window ∧ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ η → ∀ control : cube (ι := ι) ε, ∀ a ∈ K,
        (∀ y ∈ closedBall a radius, ‖fderiv ℝ (d ∘ F.family ε control.val ∘ c.symm) y‖ ≤ B) ∧
        ∀ y ∈ closedBall a radius, ∀ z ∈ closedBall a radius,
          ‖fderiv ℝ (d ∘ F.family ε control.val ∘ c.symm) y-
            fderiv ℝ (d ∘ F.family ε control.val ∘ c.symm) z‖ ≤ C*‖y-z‖^α := by
  classical
  have localBounds (x : K) := F.local_first_holder_bounds positiveα subunitα lower regular
    c d hc hd x.val (inside x.property).1 (inside x.property).2
  choose radii positiveRadii windows positiveWindows inWindows B C nonnegativeB nonnegativeC facts
    using localBounds
  obtain ⟨s, cover⟩ := compact.elim_finite_subcover
    (fun x : K => ball x.val (radii x/4)) (fun _ => isOpen_ball)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (div_pos (positiveRadii ⟨x, hx⟩) (by norm_num))⟩)
  obtain ⟨radius, positiveRadius, commonRadius⟩ := CompactUniformCenteredCharts.common_positive
    s (fun x => radii x/2) (fun x _ => half_pos (positiveRadii x))
  obtain ⟨noise, positiveNoise, commonNoise⟩ := CompactUniformCenteredCharts.common_positive
    s (fun x => (windows x : ℝ)) (fun x _ => by exact_mod_cast positiveWindows x)
  let η : ℝ≥0 := min F.window ⟨noise, positiveNoise.le⟩
  have positiveη : 0 < η := lt_min F.window_positive positiveNoise
  let boundB : ℝ := s.sum B
  let boundC : ℝ := s.sum C
  have commonB (x : K) (hx : x ∈ s) : B x ≤ boundB :=
    Finset.single_le_sum (fun i _ => nonnegativeB i) hx
  have commonC (x : K) (hx : x ∈ s) : C x ≤ boundC :=
    Finset.single_le_sum (fun i _ => nonnegativeC i) hx
  refine ⟨radius, positiveRadius, η, positiveη, min_le_left _ _, boundB, boundC,
    Finset.sum_nonneg (fun i _ => nonnegativeB i), Finset.sum_nonneg (fun i _ => nonnegativeC i), ?_⟩
  intro ε hp hw control a ha
  rcases mem_iUnion.mp (cover ha) with ⟨i, hi⟩
  rcases mem_iUnion.mp hi with ⟨his, hai⟩
  have localNoise : ε ≤ windows i := NNReal.coe_le_coe.mp
    ((NNReal.coe_le_coe.mpr (hw.trans (min_le_right _ _))).trans (commonNoise i his))
  have captured (y : E) (hy : y ∈ closedBall a radius) : y ∈ closedBall i.val (radii i) := by
    rw [mem_closedBall] at hy ⊢
    have center := mem_ball.mp hai
    have triangle := dist_triangle y a i.val
    have scale := commonRadius i his
    linarith [positiveRadii i]
  have bounds := facts i ε hp localNoise control
  exact ⟨fun y hy => (bounds.1 y (captured y hy)).trans (commonB i his),
    fun y hy z hz => (bounds.2 y (captured y hy) z (captured z hz)).trans
      (mul_le_mul_of_nonneg_right (commonC i his) (Real.rpow_nonneg (norm_nonneg _) _))⟩

theorem Maps.uniform_centered_first_holder_tube {P Q : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {T : M ≃ₜ M} {r α : ℝ}
    (F : Maps (E := E) (ι := ι) T r) (positiveα : 0 < α) (subunitα : α < 1)
    (lower : α+1 < r) (regular : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
    (K : Set E) (compact : IsCompact K)
    (inside : K ⊆ c.target ∩ (T ∘ c.symm) ⁻¹' d.source)
    (frameBound : ℝ) (oneFrameBound : 1 ≤ frameBound) :
    ∃ radius > 0, ∃ η : ℝ≥0, 0 < η ∧ η ≤ F.window ∧ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ η → ∀ control : cube (ι := ι) ε, ∀ a ∈ K,
      ∀ (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] E),
        ‖L.toContinuousLinearMap‖ ≤ frameBound → ‖R.symm.toContinuousLinearMap‖ ≤ frameBound →
        ∀ b : E, let h := centered L R a b (d ∘ F.family ε control.val ∘ c.symm)
        (∀ z : P, ‖z‖ ≤ radius → ‖fderiv ℝ h z‖ ≤ B) ∧
        ∀ z : P, ‖z‖ ≤ radius → ∀ w : P, ‖w‖ ≤ radius →
          ‖fderiv ℝ h z-fderiv ℝ h w‖ ≤ C*‖z-w‖^α := by
  have positiveFrameBound : 0 < frameBound := lt_of_lt_of_le zero_lt_one oneFrameBound
  obtain ⟨rawRadius, positiveRawRadius, η, positiveη, window, B, C, nonnegativeB, nonnegativeC, raw⟩ :=
    F.uniform_chart_first_holder_tube positiveα subunitα lower regular c d hc hd K compact inside
  refine ⟨rawRadius/frameBound, div_pos positiveRawRadius positiveFrameBound,
    η, positiveη, window, frameBound^2*B, frameBound^2*C*frameBound^α, by positivity, by positivity, ?_⟩
  intro ε hp hw control a ha L R boundL boundR b
  dsimp only
  let f := d ∘ F.family ε control.val ∘ c.symm
  have facts := raw ε hp hw control a ha
  have captured (z : P) (hz : ‖z‖ ≤ rawRadius/frameBound) : a+L z ∈ closedBall a rawRadius := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    calc
      _ ≤ ‖L.toContinuousLinearMap‖*‖z‖ := L.toContinuousLinearMap.le_opNorm _
      _ ≤ frameBound*(rawRadius/frameBound) :=
        mul_le_mul boundL hz (norm_nonneg _) positiveFrameBound.le
      _ = rawRadius := by field_simp
  constructor
  · intro z hz
    rw [fderiv_centered]
    calc
      _ ≤ ‖R.symm.toContinuousLinearMap‖*
          (‖fderiv ℝ f (a+L z)‖*‖L.toContinuousLinearMap‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ frameBound*(B*frameBound) := mul_le_mul boundR
        (mul_le_mul (facts.1 _ (captured z hz)) boundL (norm_nonneg _) nonnegativeB)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) positiveFrameBound.le
      _ = frameBound^2*B := by ring
  · intro z hz w hw
    have transport :
        ‖fderiv ℝ (centered L R a b f) z-fderiv ℝ (centered L R a b f) w‖ ≤
          ‖R.symm.toContinuousLinearMap‖*
            (‖fderiv ℝ f (a+L z)-fderiv ℝ f (a+L w)‖*‖L.toContinuousLinearMap‖) := by
      rw [fderiv_centered, fderiv_centered, ← ContinuousLinearMap.comp_sub,
        ← ContinuousLinearMap.sub_comp]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    have gap : ‖(a+L z)-(a+L w)‖ ≤ frameBound*‖z-w‖ := by
      rw [add_sub_add_left_eq_sub, ← map_sub]
      exact (L.toContinuousLinearMap.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right boundL (norm_nonneg _))
    have power : ‖(a+L z)-(a+L w)‖^α ≤ frameBound^α*‖z-w‖^α := by
      calc
        _ ≤ (frameBound*‖z-w‖)^α := Real.rpow_le_rpow (norm_nonneg _) gap positiveα.le
        _ = _ := Real.mul_rpow positiveFrameBound.le (norm_nonneg _)
    calc
      _ ≤ frameBound*((C*‖(a+L z)-(a+L w)‖^α)*frameBound) := transport.trans
        (mul_le_mul boundR
          (mul_le_mul (facts.2 _ (captured z hz) _ (captured w hw)) boundL
            (norm_nonneg _) (mul_nonneg nonnegativeC (Real.rpow_nonneg (norm_nonneg _) _)))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) positiveFrameBound.le)
      _ ≤ frameBound*((C*(frameBound^α*‖z-w‖^α))*frameBound) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left power nonnegativeC)
            positiveFrameBound.le) positiveFrameBound.le
      _ = (frameBound^2*C*frameBound^α)*‖z-w‖^α := by ring

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
