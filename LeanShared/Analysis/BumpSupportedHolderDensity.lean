module
public import LeanShared.Analysis.BumpLowerHolderConvergence

/-! Actual supported smooth approximation in every strictly lower Hölder
norm on Euclidean space. The safety radius and the entire smooth sequence
are constructed, retaining the EXACT prescribed open support region. -/
public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
namespace LeanShared.BumpSupportedHolderDensity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
  (f : E →ᵇ ℂ) {a b C : ℝ}

/-- The literal supported smooth elements of the actual lower Hölder graph. -/
def SmoothGraph (V : Set E) (v : BoundedHolderSpace.graph E b) : Prop :=
  ContDiff ℝ ∞ (fun x => BoundedHolderSpace.physical E b v x) ∧
    HasCompactSupport (fun x => BoundedHolderSpace.physical E b v x) ∧
      tsupport (fun x => BoundedHolderSpace.physical E b v x) ⊆ V

include μ in
theorem exists_sequence {V : Set E} (hV : IsOpen V) (support : tsupport f ⊆ V)
    (compact : HasCompactSupport f) (hb : 0 ≤ b) (hab : b < a) (hC : 0 ≤ C)
    (hf : ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ a) :
    ∃ v : ℕ → BoundedHolderSpace.graph E b,
      (∀ n, SmoothGraph V (v n)) ∧
        Tendsto v atTop (𝓝 (BumpLowerHolderConvergence.lift f hb hab hC hf)) := by
  obtain ⟨δ, hδ, safe⟩ := BumpSupportedRegularization.exists_support_radius μ f compact hV support
  let r (n : ℕ) : ℝ := δ / ((n : ℝ) + 1)
  have hr (n : ℕ) : 0 < r n := div_pos hδ (by positivity)
  let ψ (n : ℕ) : ContDiffBump (0 : E) := ⟨r n / 2, r n, half_pos (hr n), half_lt_self (hr n)⟩
  have radius : Tendsto (fun n => (ψ n).rOut) atTop (𝓝 0) := by
    simpa only [ψ, r, div_eq_mul_inv, one_div, mul_zero, one_mul] using
      (tendsto_const_nhds (x := δ)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let v (n : ℕ) := BumpLowerHolderConvergence.lift
    (BumpSupportedRegularization.bounded μ (ψ n) f) hb hab hC
    (BumpHolderRegularization.convolution_increment μ (ψ n) f hf)
  refine ⟨v, fun n => ?_, BumpLowerHolderConvergence.smoothing_tendsto μ f hb hab hC hf ψ radius⟩
  have physical : BoundedHolderSpace.physical E b (v n) =
      BumpSupportedRegularization.bounded μ (ψ n) f :=
    BumpLowerHolderConvergence.physical_lift _ hb hab hC _
  have values : (fun x => BoundedHolderSpace.physical E b (v n) x) =
      BumpSupportedRegularization.function μ (ψ n) f := by
    funext x
    exact congrArg (fun h : E →ᵇ ℂ => h x) physical
  change ContDiff ℝ ∞ _ ∧ HasCompactSupport _ ∧ tsupport _ ⊆ V
  rw [values]
  refine ⟨BumpSupportedRegularization.smooth μ (ψ n) f, ?_, ?_⟩
  · exact (ψ n).hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) compact
  · apply safe (ψ n)
    change δ / ((n : ℝ) + 1) ≤ δ
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]

include μ in
/-- Thus the literal rough function belongs to the lower-norm closure of
actual compactly supported smooth functions in the SAME region. -/
theorem mem_smooth_closure {V : Set E} (hV : IsOpen V) (support : tsupport f ⊆ V)
    (compact : HasCompactSupport f) (hb : 0 ≤ b) (hab : b < a) (hC : 0 ≤ C)
    (hf : ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ a) :
    BumpLowerHolderConvergence.lift f hb hab hC hf ∈
      closure {v : BoundedHolderSpace.graph E b | SmoothGraph V v} := by
  obtain ⟨v, smooth, limit⟩ := exists_sequence μ f hV support compact hb hab hC hf
  exact mem_closure_of_tendsto limit (Eventually.of_forall smooth)
end LeanShared.BumpSupportedHolderDensity
