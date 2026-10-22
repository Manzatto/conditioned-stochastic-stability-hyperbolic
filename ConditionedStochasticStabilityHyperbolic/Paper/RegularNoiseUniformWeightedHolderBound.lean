module
public import LeanShared.Geometry.ManifoldWeightedHolderOperator
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseUniformHolderTransport
public import LeanShared.Analysis.QuotientLinearLiftNorm

/-! Actual joint C¹ map regularity and one supported fractional weight
produce one uniform regular-operator norm bound near a reference parameter.
The finite chart constants and quotient descent bound are derived. -/
public noncomputable section
set_option maxHeartbeats 1600000
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction BigOperators
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared
variable {E M J ι:Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  (μ:Measure E) [μ.IsAddHaarMeasure] {V S:Set M}
  (e:J→OpenPartialHomeomorph M E) (D:ConstructedManifoldLocalization.Data e S)
  (atlas:∀ i,e i∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
  (openV:IsOpen V) (region:V⊆S) {u b:ℝ} (hb:0<b) (hb1:b<1) (hbu:b<u) (hu1:u<1)
  {w:M→ℂ} (hw:FractionalManifoldRegularity.Regular (E:=E) (F:=ℂ) u w)
  (support:tsupport w⊆V) {T:M≃ₜM} {r:ℝ} (F:Maps (E:=E) (ι:=ι) T r)
  (hr:1≤r) (hT:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)

local instance localNormed (i:D.indices) : NormedAddCommGroup
    (ManifoldWeightedHolderCoordinateOperators.Local e D openV hb hb1 i) := inferInstance
local instance localSemi (i:D.indices) : SeminormedAddCommGroup
    (ManifoldWeightedHolderCoordinateOperators.Local e D openV hb hb1 i) :=
  (localNormed e D openV hb hb1 i).toSeminormedAddCommGroup
local instance localScalar (i:D.indices) : NormedSpace ℂ
    (ManifoldWeightedHolderCoordinateOperators.Local e D openV hb hb1 i) := inferInstance
local instance coordinateNormed : NormedAddCommGroup
    (ManifoldWeightedHolderOperator.Coordinates e D openV hb hb1) := inferInstance
local instance coordinateSemi : SeminormedAddCommGroup
    (ManifoldWeightedHolderOperator.Coordinates e D openV hb hb1) :=
  (coordinateNormed e D openV hb hb1).toSeminormedAddCommGroup
local instance coordinateScalar : NormedSpace ℂ
    (ManifoldWeightedHolderOperator.Coordinates e D openV hb hb1) := inferInstance
local instance regularNormed : NormedAddCommGroup
    (ManifoldWeightedHolderOperator.Regular e D openV hb hb1) := inferInstance
local instance regularSemi : SeminormedAddCommGroup
    (ManifoldWeightedHolderOperator.Regular e D openV hb hb1) :=
  (regularNormed e D openV hb hb1).toSeminormedAddCommGroup
local instance regularScalar : NormedSpace ℂ
    (ManifoldWeightedHolderOperator.Regular e D openV hb hb1) := inferInstance

include hr in
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
theorem Maps.contMDiff_one (ε:NNReal) (hp:0<ε) (hw:ε≤F.window) (control:cube (ι:=ι) ε) :
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (F.family ε control.val) := by
  apply (F.map_regular ε hp hw control).differentiable.of_le
  exact_mod_cast (Nat.le_floor (by simpa using hr) : (1:ℕ)≤⌊r⌋₊)

include μ atlas hbu hu1 hw support hT in
theorem Maps.exists_pair_holder_bound (i j:D.indices) :
    ∃η:NNReal,0<η ∧ ∃C:ℝ,0≤C ∧ ∀ ε:NNReal,∀ hp:0<ε,∀ _hl:ε≤η,
      ∀ window:ε≤F.window,∀ control:cube (ι:=ι) ε,
      ‖(ManifoldWeightedHolderOperator.transport μ e D atlas openV hb hb1 hbu hu1 hw support
        (F.family ε control.val) (F.contMDiff_one hr ε hp window control) i j).map‖≤C := by
  obtain ⟨η,hη,C,hC,Q,bound,formula⟩:=F.exists_uniform_holder_transport hr hT
    (e i) (e j) (atlas i) (atlas j) (D.cutoff i) (D.smooth i) (D.compact i) (D.support i)
    (closure ((ManifoldWeightedHolderCoordinateOperators.regions e D openV).region j))
    ((ManifoldWeightedHolderCoordinateOperators.regions e D openV).compact_closure j)
    ((ManifoldWeightedHolderCoordinateOperators.regions e D openV).closure_target j)
    (hb.trans hbu) hu1 hw hb.le hbu
  refine ⟨η,hη,C,hC,?_⟩
  intro ε hp hl window control
  let old:=ManifoldWeightedHolderOperator.transport μ e D atlas openV hb hb1 hbu hu1 hw support
    (F.family ε control.val) (F.contMDiff_one hr ε hp window control) i j
  change ‖old.map‖≤C
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  have equal:(old.map v).val=Q ε hp hl control v.val := by
    apply BoundedHolderSpace.physical_injective E b
    ext y
    exact (old.physical v y).trans
      (formula ε hp hl control v.val
        (fun z hz=>EuclideanLittleChartExtension.zero_outside_closure
          ((ManifoldWeightedHolderCoordinateOperators.regions e D openV).compact_closure j) hb hb1 v z hz) y).symm
  change ‖(old.map v).val‖≤C*‖v.val‖
  rw [equal]
  exact ((Q ε hp hl control).le_opNorm v.val).trans
    (mul_le_mul_of_nonneg_right (bound ε hp hl control) (norm_nonneg v.val))

include μ atlas region hbu hu1 hw support hT in
theorem Maps.exists_uniform_holder_operator_bound :
    ∃η:NNReal,0<η ∧ ∃C:ℝ,0≤C ∧ ∀ ε:NNReal,∀ hp:0<ε,∀ _hl:ε≤η,
      ∀ window:ε≤F.window,∀ control:cube (ι:=ι) ε,
      ‖ManifoldWeightedHolderOperator.operator μ e D atlas openV region hb hb1 hbu hu1 hw support
        (F.family ε control.val) (F.contMDiff_one hr ε hp window control)‖≤C := by
  classical
  choose η positiveη C positiveC bound using
    (fun i j:D.indices=>F.exists_pair_holder_bound μ e D atlas openV hb hb1 hbu hu1 hw support hr hT i j)
  let windowAt:Option (D.indices×D.indices)→NNReal:=fun q=>match q with
    | none=>F.window
    | some (i,j)=>η i j
  let window:NNReal:=Finset.univ.inf' Finset.univ_nonempty windowAt
  have windowPositive:0<window:=by
    apply (Finset.lt_inf'_iff Finset.univ_nonempty).mpr
    intro q _
    cases q with
    | none=>exact F.window_positive
    | some ij=>exact positiveη ij.1 ij.2
  have below(i j:D.indices):window≤η i j:=
    Finset.inf'_le windowAt (Finset.mem_univ (some (i,j)))
  let B:ℝ:=∑i:D.indices,∑j:D.indices,C i j
  have hB:0≤B:=Finset.sum_nonneg fun i _=>Finset.sum_nonneg fun j _=>positiveC i j
  refine ⟨window,windowPositive,B,hB,?_⟩
  intro ε hp hl window control
  have hbound(i j:D.indices):
      ‖(ManifoldWeightedHolderOperator.transport μ e D atlas openV hb hb1 hbu hu1 hw support
          (F.family ε control.val) (F.contMDiff_one hr ε hp window control) i j).map‖≤C i j:=
    bound i j ε hp (hl.trans (below i j)) window control
  have rows_bound (z:ManifoldWeightedHolderOperator.Coordinates e D openV hb hb1) :
      ‖ManifoldWeightedHolderOperator.rows μ e D atlas openV hb hb1 hbu hu1 hw support
        (F.family ε control.val) (F.contMDiff_one hr ε hp window control) z‖≤B*‖z‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hB (norm_nonneg z))).mpr
    intro i
    change ‖ManifoldWeightedHolderOperator.row μ e D atlas openV hb hb1 hbu hu1 hw support
      (F.family ε control.val) (F.contMDiff_one hr ε hp window control) i z‖≤B*‖z‖
    calc
      _ ≤ ∑j:D.indices,‖(ManifoldWeightedHolderOperator.transport μ e D atlas openV hb hb1 hbu hu1 hw support
          (F.family ε control.val) (F.contMDiff_one hr ε hp window control) i j).map (z j)‖ := by
        simp only [ManifoldWeightedHolderOperator.row,sum_apply,ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.proj_apply]
        exact norm_sum_le _ _
      _ ≤ ∑j:D.indices,C i j*‖z‖ := by
        apply Finset.sum_le_sum
        intro j _
        exact ((ManifoldWeightedHolderOperator.transport μ e D atlas openV hb hb1 hbu hu1 hw support
          (F.family ε control.val) (F.contMDiff_one hr ε hp window control) i j).map.le_opNorm (z j)).trans
            (mul_le_mul (hbound i j) (norm_le_pi_norm z j) (norm_nonneg _) (positiveC i j))
      _ = (∑j:D.indices,C i j)*‖z‖ := (Finset.sum_mul _ _ _).symm
      _ ≤ B*‖z‖ := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun k _=>Finset.sum_nonneg fun j _=>positiveC k j) (Finset.mem_univ i))
        (norm_nonneg z)
  apply QuotientLinearLiftNorm.bound _ _ _ hB
  intro z
  exact (Submodule.Quotient.norm_mk_le _ _).trans (rows_bound z)
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
