module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ConstructedHolderNoiseAction
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseMapImage

/-! The genuine uniform transfer action on the common continuous-map image.
Its cap can be chosen below two different Hölder action windows, so those
spaces use exactly the same metric parameter domain. -/
public noncomputable section
set_option maxHeartbeats 1600000
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.ConstructedHolderNoiseImage
open LeanShared ConstructedHolderPhysicalModel ConstructedHolderSingleTransfer Paper
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

variable (η:NNReal) (cap:η≤(ConstructedHolderNoiseAction.bounds μE e D atlas openV region hb hb1 F hr hT hbq hg support).window)
@[expose] def Space := RegularNoise.MapImage.Space F hr η
  (cap.trans (ConstructedHolderNoiseAction.bounds μE e D atlas openV region hb hb1 F hr hT hbq hg support).below)

@[expose] def maps (z:Space μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap) : M→M:=z.val

def representative (z:Space μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap) : ConstructedHolderNoiseAction.Parameter μE e D atlas openV region hb hb1 F hr hT hbq hg support:=
  match RegularNoise.MapImage.representative F hr η
    (cap.trans (ConstructedHolderNoiseAction.bounds μE e D atlas openV region hb hb1 F hr hT hbq hg support).below) z with
  | none=>none
  | some p=>some ⟨⟨p.1.val,p.1.property.1,p.1.property.2.trans cap⟩,p.2⟩

theorem representative_maps (z:Space μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap) :
    ConstructedHolderNoiseAction.maps μE e D atlas openV region hb hb1 F hr hT hbq hg support (representative μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap z)=maps μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap z := by
  let hw:=cap.trans (ConstructedHolderNoiseAction.bounds μE e D atlas openV region hb hb1 F hr hT hbq hg support).below
  calc
    _ = RegularNoise.MapImage.parameterMaps F η (RegularNoise.MapImage.representative F hr η hw z) := by
      unfold representative
      cases RegularNoise.MapImage.representative F hr η hw z <;> rfl
    _ = _ := RegularNoise.MapImage.representative_maps F hr η hw z

theorem regular (z:Space μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap) : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (maps μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap z) :=
  RegularNoise.MapImage.regular F hr η
    (cap.trans (ConstructedHolderNoiseAction.bounds μE e D atlas openV region hb hb1 F hr hT hbq hg support).below) hT z

@[expose] def operator (z:Space μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap) :=
  transfer μE e D atlas openV region hb hb1 (maps μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap z) (regular μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap z) hbq hg support

include μE atlas region hbq hg support hr hT in
theorem operator_eq (z:Space μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap) :
    operator μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap z=ConstructedHolderNoiseAction.operator μE e D atlas openV region hb hb1 F hr hT hbq hg support (representative μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap z) := by
  apply ContinuousLinearMap.ext
  intro f
  apply view_injective e D openV hb hb1
  ext x
  calc
    _ = (g x:ℂ)*view e D openV hb hb1 f (maps μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap z x):=
      transfer_function μE e D atlas openV region hb hb1 (maps μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap z) (regular μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap z) hbq hg support f x
    _ = (g x:ℂ)*view e D openV hb hb1 f
        (ConstructedHolderNoiseAction.maps μE e D atlas openV region hb hb1 F hr hT hbq hg support (representative μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap z) x):=by
      rw [representative_maps μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap z]
    _ = _ := (transfer_function μE e D atlas openV region hb hb1
      (ConstructedHolderNoiseAction.maps μE e D atlas openV region hb hb1 F hr hT hbq hg support (representative μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap z))
      (ConstructedHolderNoiseAction.regular μE e D atlas openV region hb hb1 F hr hT hbq hg support (representative μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap z)) hbq hg support f x).symm

include μE atlas region hbq hg support hr hT in
theorem operator_bound (z:Space μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap) :
    ‖operator μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap z‖≤ConstructedHolderNoiseAction.constant μE e D atlas openV region hb hb1 F hr hT hbq hg support := by
  rw [operator_eq μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap z]
  exact ConstructedHolderNoiseAction.operator_bound μE e D atlas openV region hb hb1 F hr hT hbq hg support (representative μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap z)
include μE atlas region hbq hg support hr hT in
theorem invariant : ∀ a (f:Regular e D openV hb hb1),
    FiniteRegularTransferRealization.weightedComposition
      (maps μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap a) g
      (view e D openV hb hb1 f)∈(view e D openV hb hb1).range := by
  intro a f
  refine ⟨operator μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap a f,?_⟩
  ext x
  exact transfer_function μE e D atlas openV region hb hb1
    (maps μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap a)
    (regular μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap a) hbq hg support f x

include μE atlas region hbq hg support hr hT in
theorem action_eq (a:Space μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap)
    (f:Regular e D openV hb hb1) :
    InvariantFiniteRegularTransfer.action (view e D openV hb hb1) (view_injective e D openV hb hb1)
      (maps μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap) g
      (invariant μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap) a f=
      operator μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap a f := by
  apply view_injective e D openV hb hb1
  ext x
  exact (InvariantFiniteRegularTransfer.action_apply _ _ _ _ _ a f x).trans
    (transfer_function μE e D atlas openV region hb hb1
      (maps μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap a)
      (regular μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap a) hbq hg support f x).symm

include μE atlas region hbq hg support hr hT in
theorem action_bound (a:Space μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap)
    (f:Regular e D openV hb hb1) :
    ‖InvariantFiniteRegularTransfer.action (view e D openV hb hb1) (view_injective e D openV hb hb1)
      (maps μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap) g
      (invariant μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap) a f‖≤
      ConstructedHolderNoiseAction.constant μE e D atlas openV region hb hb1 F hr hT hbq hg support*‖f‖ := by
  rw [action_eq μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap a f]
  exact ((operator μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap a).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (operator_bound μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap a)
      (norm_nonneg f))
end ConditionedStochasticStabilityHyperbolic.ConstructedHolderNoiseImage
