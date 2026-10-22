module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseUniformWeightedHolderBound
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ConstructedHolderSingleTransfer
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ConstructedHolderSingleTransfer

/-! Actual finite-regular actions for every small noisy map and the
reference map. Their membership and one uniform bound are produced from
the literal Whitney controls, not supplied as regular-action fields. -/
public noncomputable section
set_option maxHeartbeats 1600000
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.ConstructedHolderNoiseAction
open LeanShared ConstructedHolderPhysicalModel ConstructedHolderSingleTransfer Paper

structure UniformBounds {H:Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (outer:NNReal) {ι:Type*} [Fintype ι]
    (Q:∀ ε:NNReal,0<ε→ε≤outer→RegularNoise.cube (ι:=ι) ε→(H→L[ℂ]H)) where
  window : NNReal
  positive : 0<window
  below : window≤outer
  constant : ℝ
  nonnegative : 0≤constant
  bound : ∀ ε:NNReal,∀ hp:0<ε,∀ hl:ε≤window,∀ control:RegularNoise.cube (ι:=ι) ε,
    ‖Q ε hp (hl.trans below) control‖≤constant

variable {E M J ι:Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  (μE:Measure E) [μE.IsAddHaarMeasure] {V S:Set M}
  (e:J→OpenPartialHomeomorph M E) (D:ConstructedManifoldLocalization.Data e S)
  (atlas:∀ j,e j∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
  (openV:IsOpen V) (region:V⊆S) {b:ℝ} (hb:0<b) (hb1:b<1)
  {T:M≃ₜM} {r:ℝ} (F:RegularNoise.Maps (E:=E) (ι:=ι) T r) (hr:1≤r)
  (hT:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
  {g:M→ℝ} {q:ℝ} (hbq:b<q)
  (hg:FractionalManifoldRegularity.Regular (E:=E) (F:=ℝ) q g)
  (support:tsupport g⊆V)

@[expose] def noiseTransfer (ε:NNReal) (hp:0<ε) (hw:ε≤F.window)
    (control:RegularNoise.cube (ι:=ι) ε) :=
  transfer μE e D atlas openV region hb hb1 (F.family ε control.val)
    (F.contMDiff_one hr ε hp hw control) hbq hg support

def bounds : UniformBounds F.window (noiseTransfer μE e D atlas openV region hb hb1 F hr hbq hg support) := Classical.choice <| by
  obtain ⟨η,hη,C,hC,bound⟩:=F.exists_uniform_holder_operator_bound μE e D atlas openV region hb hb1
    (between hb1 hbq) (below_one hb1) (regular_weight hb hb1 hbq hg) (weight_support support) hr hT
  refine ⟨⟨min η F.window,lt_min hη F.window_positive,min_le_right _ _,C,hC,?_⟩⟩
  intro ε hp hl control
  exact bound ε hp (hl.trans (min_le_left _ _)) (hl.trans (min_le_right _ _)) control

@[expose] def Parameter := Option (Σ ε:{ε:NNReal//0<ε∧ε≤
    (bounds μE e D atlas openV region hb hb1 F hr hT hbq hg support).window},RegularNoise.cube (ι:=ι) ε.val)

@[expose] def maps : Parameter μE e D atlas openV region hb hb1 F hr hT hbq hg support→M→M
  | none=>T
  | some a=>F.family a.1.val a.2.val

 theorem regular (a:Parameter μE e D atlas openV region hb hb1 F hr hT hbq hg support) :
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (maps μE e D atlas openV region hb hb1 F hr hT hbq hg support a) := by
  cases a with
  | none=>exact hT
  | some a=>
    exact F.contMDiff_one hr a.1.val a.1.property.1
      (a.1.property.2.trans (bounds μE e D atlas openV region hb hb1 F hr hT hbq hg support).below) a.2

@[expose] def operator (a:Parameter μE e D atlas openV region hb hb1 F hr hT hbq hg support) :=
  transfer μE e D atlas openV region hb hb1
    (maps μE e D atlas openV region hb hb1 F hr hT hbq hg support a)
    (regular μE e D atlas openV region hb hb1 F hr hT hbq hg support a) hbq hg support

include μE atlas region hbq hg support hr hT in
theorem invariant : ∀ a (f:Regular e D openV hb hb1),
    FiniteRegularTransferRealization.weightedComposition
      (maps μE e D atlas openV region hb hb1 F hr hT hbq hg support a) g
      (view e D openV hb hb1 f)∈(view e D openV hb hb1).range := by
  intro a f
  refine ⟨operator μE e D atlas openV region hb hb1 F hr hT hbq hg support a f,?_⟩
  ext x
  exact transfer_function μE e D atlas openV region hb hb1
    (maps μE e D atlas openV region hb hb1 F hr hT hbq hg support a)
    (regular μE e D atlas openV region hb hb1 F hr hT hbq hg support a) hbq hg support f x

@[expose] def constant : ℝ:=max ‖transfer μE e D atlas openV region hb hb1 T hT hbq hg support‖
  (bounds μE e D atlas openV region hb hb1 F hr hT hbq hg support).constant

include μE atlas region hbq hg support hr hT in
theorem operator_bound (a:Parameter μE e D atlas openV region hb hb1 F hr hT hbq hg support) :
    ‖operator μE e D atlas openV region hb hb1 F hr hT hbq hg support a‖≤
      constant μE e D atlas openV region hb hb1 F hr hT hbq hg support := by
  cases a with
  | none=>exact le_max_left _ _
  | some a=>exact ((bounds μE e D atlas openV region hb hb1 F hr hT hbq hg support).bound
      a.1.val a.1.property.1 a.1.property.2 a.2).trans (le_max_right _ _)

include μE atlas region hbq hg support hr hT in
theorem action_eq (a:Parameter μE e D atlas openV region hb hb1 F hr hT hbq hg support)
    (f:Regular e D openV hb hb1) :
    InvariantFiniteRegularTransfer.action (view e D openV hb hb1) (view_injective e D openV hb hb1)
      (maps μE e D atlas openV region hb hb1 F hr hT hbq hg support) g
      (invariant μE e D atlas openV region hb hb1 F hr hT hbq hg support) a f=
      operator μE e D atlas openV region hb hb1 F hr hT hbq hg support a f := by
  apply view_injective e D openV hb hb1
  ext x
  exact (InvariantFiniteRegularTransfer.action_apply _ _ _ _ _ a f x).trans
    (transfer_function μE e D atlas openV region hb hb1
      (maps μE e D atlas openV region hb hb1 F hr hT hbq hg support a)
      (regular μE e D atlas openV region hb hb1 F hr hT hbq hg support a) hbq hg support f x).symm

include μE atlas region hbq hg support hr hT in
theorem action_bound (a:Parameter μE e D atlas openV region hb hb1 F hr hT hbq hg support)
    (f:Regular e D openV hb hb1) :
    ‖InvariantFiniteRegularTransfer.action (view e D openV hb hb1) (view_injective e D openV hb hb1)
      (maps μE e D atlas openV region hb hb1 F hr hT hbq hg support) g
      (invariant μE e D atlas openV region hb hb1 F hr hT hbq hg support) a f‖≤
      constant μE e D atlas openV region hb hb1 F hr hT hbq hg support*‖f‖ := by
  rw [action_eq μE e D atlas openV region hb hb1 F hr hT hbq hg support a f]
  exact ((operator μE e D atlas openV region hb hb1 F hr hT hbq hg support a).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (operator_bound μE e D atlas openV region hb hb1 F hr hT hbq hg support a)
      (norm_nonneg f))
end ConditionedStochasticStabilityHyperbolic.ConstructedHolderNoiseAction
