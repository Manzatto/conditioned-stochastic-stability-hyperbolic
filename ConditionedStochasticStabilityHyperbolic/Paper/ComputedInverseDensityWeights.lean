module
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseJacobianWeights
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoisePositiveWeights
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedInverseDensitySources

/-! Every scalar field of InverseDensityWeights is constructed from the
original continuous departure weight and the actual finite smooth reference
measure. The only collar condition is deterministic positivity on its closure. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set MeasureTheory Measure IsManifold
open scoped Topology Manifold ContDiff NNReal ENNReal

set_option maxHeartbeats 3200000 in
def InverseFamily.densityWeights
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
    (J : InverseFamily F) (d : LeanShared.FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [IsAddHaarMeasure μ]
    (K G : Set M) (measurableK : MeasurableSet K)
    (w : M → ℝ) (continuousW : Continuous w) (nonnegativeW : ∀ x ∈ K, 0 ≤ w x)
    (positiveW : ∀ x ∈ closure G, 0 < w (T.symm x)) (R : ℝ) (positiveR : 0 < R) :
    InverseDensityWeights J (d.measure μ) K G (fun x => w x.val) R := by
  classical
  have existence := J.eventually_positive_weight w continuousW G positiveW
  let η := Classical.choose existence
  have properties := Classical.choose_spec existence
  refine {
    window := η
    positive := properties.1
    window_le := properties.2.1
    weight := J.jacobianWeight d w R
    measurable := fun ε hp hw => (J.jacobianWeight_continuous d μ w continuousW R ε hp
      (hw.trans properties.2.1)).measurable
    nonnegative := ?_
    continuous := ?_
    bounded := ?_
    positive_on := ?_
    change_variables := ?_ }
  · intro ε hp hw x a
    have jacobian := d.jacobian_continuous_positive_map μ
      (J.homeomorph ε hp (hw.trans properties.2.1) a)
      (J.forward_contMDiff ε hp (hw.trans properties.2.1) a)
      (J.map_contMDiff ε hp (hw.trans properties.2.1) a)
    simp only [InverseFamily.jacobianWeight,dite_eq_left (And.intro hp (hw.trans properties.2.1))]
    exact mul_nonneg (div_nonneg (le_max_right _ _) positiveR.le) (jacobian.2.1 x).le
  · intro ε hp hw a
    exact (J.jacobianWeight_continuous d μ w continuousW R ε hp
      (hw.trans properties.2.1)).comp (continuous_id.prodMk continuous_const)
  · intro ε hp hw
    obtain ⟨B,bound⟩ := isCompact_univ.exists_bound_of_continuousOn
      (J.jacobianWeight_continuous d μ w continuousW R ε hp (hw.trans properties.2.1)).continuousOn
    exact ⟨max B 0,le_max_right _ _,fun x a => (bound (x,a) (mem_univ _)).trans (le_max_left _ _)⟩
  · intro ε hp hw x _ hx a
    have jacobian := d.jacobian_continuous_positive_map μ
      (J.homeomorph ε hp (hw.trans properties.2.1) a)
      (J.forward_contMDiff ε hp (hw.trans properties.2.1) a)
      (J.map_contMDiff ε hp (hw.trans properties.2.1) a)
    have positive := properties.2.2 ε hp hw a x hx
    simp only [InverseFamily.jacobianWeight,dite_eq_left (And.intro hp (hw.trans properties.2.1))]
    exact mul_pos (div_pos (lt_max_of_lt_left positive) positiveR) (jacobian.2.1 x)
  · intro ε hp hw f g hf hg a
    have law := J.jacobianWeight_killed_duality d μ w continuousW R positiveR K measurableK
      ε hp (hw.trans properties.2.1) f g hf hg a
    refine law.trans ?_
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableK] with x hx
    rw [max_eq_left (nonnegativeW x hx)]
    congr 3
    exact congrArg (fun z : ℝ => z / R)
      (LeanShared.SubtypeKernel.zeroExtend_coe K (fun x => w x.val) ⟨x,hx⟩).symm

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
