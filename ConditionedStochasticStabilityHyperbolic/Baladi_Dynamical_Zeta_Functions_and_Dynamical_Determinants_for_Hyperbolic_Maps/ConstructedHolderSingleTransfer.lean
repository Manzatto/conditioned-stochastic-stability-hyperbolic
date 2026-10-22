module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ConstructedHolderPhysicalModel
public import LeanShared.Geometry.ManifoldWeightedHolderOperator
public import LeanShared.Geometry.FractionalSubunitRegularity
public import LeanShared.Geometry.FractionalRegularLinearIsometry

/-! A genuine C¹ map and a supported finite-C^r weight construct every
regular-action field of the physical model. The exponent between β and
min(1,r) is chosen internally. No action membership or norm bound is input. -/
public noncomputable section
set_option maxHeartbeats 1600000
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.ConstructedHolderSingleTransfer
open LeanShared ConstructedHolderPhysicalModel
variable {E U M J A Ω:Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  (μE:Measure E) [μE.IsAddHaarMeasure] {V S:Set M}
  (e:J→OpenPartialHomeomorph M E) (D:ConstructedManifoldLocalization.Data e S)
  (atlas:∀j,e j∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
  (openV:IsOpen V) (region:V⊆S) {b:ℝ} (hb:0<b) (hb1:b<1)
  (F:M→M) (hF:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 F)
  {g:M→ℝ} {r:ℝ} (hbr:b<r)
  (hg:FractionalManifoldRegularity.Regular (E:=E) (F:=ℝ) r g)
  (support:tsupport g⊆V)

@[expose] def order (b r:ℝ) : ℝ := (b+min r 1)/2
include hb1 hbr in
theorem between : b<order b r := by
  dsimp [order]
  have h:=lt_min hbr hb1
  linarith
include hb hb1 hbr in
theorem positive : 0<order b r := hb.trans (between hb1 hbr)
include hb1 in
theorem below_one : order b r<1 := by
  dsimp [order]
  linarith [min_le_right r 1]
include hbr in
theorem below_r : order b r<r := by
  dsimp [order]
  linarith [min_le_left r 1]
include hb hb1 hbr hg in
omit [CompactSpace M] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem regular_weight : FractionalManifoldRegularity.Regular (E:=E) (F:=ℂ)
    (order b r) (fun x=>(g x:ℂ)) :=
  FractionalManifoldRegularity.lower_subunit (positive hb hb1 hbr) (below_one hb1) (below_r hbr) hg.ofReal
include support in
omit [CompactSpace M] in
theorem weight_support : tsupport (fun x=>(g x:ℂ))⊆V :=
  (tsupport_comp_subset Complex.ofReal_zero g).trans support

@[expose] def transfer : Regular e D openV hb hb1 →L[ℂ] Regular e D openV hb hb1 :=
  ManifoldWeightedHolderOperator.operator μE e D atlas openV region hb hb1
    (between hb1 hbr) (below_one hb1) (regular_weight hb hb1 hbr hg)
    (weight_support support) F hF

include μE atlas region hbr hg support hF in
 omit [CompactSpace M] in
 theorem transfer_function (f:Regular e D openV hb hb1) (x:M) :
    view e D openV hb hb1 (transfer μE e D atlas openV region hb hb1 F hF hbr hg support f) x=
      (g x:ℂ)*view e D openV hb hb1 f (F x) :=
  ManifoldWeightedHolderOperator.physical_operator μE e D atlas openV region hb hb1
    (between hb1 hbr) (below_one hb1) (regular_weight hb hb1 hbr hg) (weight_support support) F hF f x

include μE atlas region hbr hg support hF in
 omit [CompactSpace M] in
 theorem invariant : ∀(_a:Ω) (f:Regular e D openV hb hb1),
    FiniteRegularTransferRealization.weightedComposition F g (view e D openV hb hb1 f)∈
      (view e D openV hb hb1).range := by
  intro _ f
  refine ⟨transfer μE e D atlas openV region hb hb1 F hF hbr hg support f,?_⟩
  ext x
  exact transfer_function μE e D atlas openV region hb hb1 F hF hbr hg support f x

include μE atlas region hbr hg support hF in
 omit [CompactSpace M] in
 theorem action_eq (a:Ω) (f:Regular e D openV hb hb1) :
    InvariantFiniteRegularTransfer.action (view e D openV hb hb1) (view_injective e D openV hb hb1)
      (fun _:Ω=>F) g (invariant μE e D atlas openV region hb hb1 F hF hbr hg support) a f=
        transfer μE e D atlas openV region hb hb1 F hF hbr hg support f := by
  apply view_injective e D openV hb hb1
  ext x
  exact (InvariantFiniteRegularTransfer.action_apply _ _ _ _ _ a f x).trans
    (transfer_function μE e D atlas openV region hb hb1 F hF hbr hg support f x).symm

include μE atlas region hbr hg support hF in
 omit [CompactSpace M] in
 theorem action_bound (a:Ω) (f:Regular e D openV hb hb1) :
    ‖InvariantFiniteRegularTransfer.action (view e D openV hb hb1) (view_injective e D openV hb hb1)
      (fun _:Ω=>F) g (invariant μE e D atlas openV region hb hb1 F hF hbr hg support) a f‖≤
      ‖transfer μE e D atlas openV region hb hb1 F hF hbr hg support‖*‖f‖ := by
  rw [action_eq μE e D atlas openV region hb hb1 F hF hbr hg support a f]
  exact (transfer μE e D atlas openV region hb hb1 F hF hbr hg support).le_opNorm f
end ConditionedStochasticStabilityHyperbolic.ConstructedHolderSingleTransfer
