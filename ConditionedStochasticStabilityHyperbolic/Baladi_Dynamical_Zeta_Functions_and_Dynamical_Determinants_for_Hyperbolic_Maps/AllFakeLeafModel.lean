module
public import LeanShared.Analysis.FakeLeafGraph
public import LeanShared.Analysis.AmbientLeafFamily
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import LeanShared.Geometry.EmbeddedSubmanifoldVolume

/-! The manuscript's leaf family is ALL embedded C¹ submanifolds of the
unstable dimension satisfying its literal signed supremum--infimum condition.
Uniform slopes, graph maps and Gram densities are constructed. The only
geometric background is the ordinary local inverse-function/graph area
formula. No supremum-norm identification is a source field. -/
public noncomputable section
open Set MeasureTheory IsManifold
open scoped Manifold ContDiff Topology
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- An actual embedded C¹ manifold of the specified dimension, carrying the
subspace topology and an injective derivative of its ambient inclusion. -/
def C1Embedded (U : Submodule ℝ E) (Γ : Set E) : Prop :=
  ∃ atlas : ChartedSpace U Γ, letI := atlas
    IsManifold (𝓘(ℝ, U)) 1 Γ ∧
      ContMDiff (𝓘(ℝ, U)) (𝓘(ℝ, E)) 1 (Subtype.val : Γ → E) ∧
      ∀ x : Γ, Function.Injective (mfderiv (𝓘(ℝ, U)) (𝓘(ℝ, E)) (Subtype.val : Γ → E) x)

/-- Every leaf admitted by the paper, with no chosen subfamily. -/
abbrev Index (U : Submodule ℝ E) (C : Set E) :=
  {Γ : Set E // C1Embedded U Γ ∧ FakeLeafGeometry.leafError C (Module.finrank ℝ Uᗮ) Γ = 0}

/-- Induced Riemannian volume, constructed independently from ordinary C¹
manifold charts and the rectangular ambient derivative Jacobian. Chart
compatibility and independence are proved in `ImmersionAtlasVolume`.
The reference Haar measure fixes the normalization. -/
def inducedVolume (U : Submodule ℝ E) (μ : Measure U) (Γ : Set E) : Measure E :=
  EmbeddedSubmanifoldVolume.volume U μ Γ

structure ConeData (U : Submodule ℝ E) (C : Set E) : Prop where
  closed : IsClosed C
  scale : ∀ r : ℝ, 0 ≤ r → ∀ v ∈ C, r • v ∈ C
  transverse : ∀ v ∈ C, v ∈ U → v = 0
  stable_positive : 0 < Module.finrank ℝ Uᗮ
  normal_planes : (FakeLeafGeometry.admissiblePlanes C (Module.finrank ℝ Uᗮ)).Nonempty

/-- Standard geometric theorems, stated for the actual embedded inclusion,
actual inverse projection and actual derivative Gram density. -/
structure ClassicalGeometry (U : Submodule ℝ E) (μ : Measure U)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ U) : Prop where
  borel : ∀ Γ : Set E, C1Embedded U Γ → MeasurableSet Γ
  projection_open : ∀ Γ : Set E, C1Embedded U Γ → ∀ L : ℝ, 0 ≤ L →
    (∀ x ∈ Γ, ∀ y ∈ Γ, ‖Uᗮ.starProjection (x - y)‖ ≤ L * ‖U.starProjection (x - y)‖) →
    IsOpen (FakeLeafGraph.parameterDomain U Γ)
  area : ∀ (Γ : Set E) (embedded : C1Embedded U Γ) (L : ℝ) (hL : 0 ≤ L)
    (slope : ∀ x ∈ Γ, ∀ y ∈ Γ, ‖Uᗮ.starProjection (x - y)‖ ≤ L * ‖U.starProjection (x - y)‖),
    (FakeLeafGraph.asGraphLeaf U Γ hL slope (borel Γ embedded) b
      (projection_open Γ embedded L hL slope)).measure μ = inducedVolume U μ Γ

variable (U : Submodule ℝ E) (C : Set E) (cone : ConeData U C)

def slope : ℝ := Classical.choose (FakeLeafGeometry.exists_uniform_fakeLeaf_slope U
  cone.closed cone.scale cone.transverse cone.stable_positive cone.normal_planes)

omit [MeasurableSpace E] [BorelSpace E] in
theorem slope_positive : 0 < slope U C cone :=
  (Classical.choose_spec (FakeLeafGeometry.exists_uniform_fakeLeaf_slope U
    cone.closed cone.scale cone.transverse cone.stable_positive cone.normal_planes)).1

omit [MeasurableSpace E] [BorelSpace E] in
theorem slope_bound (Γ : Index U C) : ∀ x ∈ Γ.val, ∀ y ∈ Γ.val,
    ‖Uᗮ.starProjection (x - y)‖ ≤ slope U C cone * ‖U.starProjection (x - y)‖ :=
  (Classical.choose_spec (FakeLeafGeometry.exists_uniform_fakeLeaf_slope U
    cone.closed cone.scale cone.transverse cone.stable_positive cone.normal_planes)).2 Γ.val Γ.property.2

variable (μ : Measure U) {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : OrthonormalBasis ι ℝ U) (geometry : ClassicalGeometry U μ b)

def leaves (Γ : Index U C) : GraphLeafNorm.GraphLeaf U E
    (GraphJacobian.densityBound (ι := ι) (slope U C cone)) :=
  FakeLeafGraph.asGraphLeaf U Γ.val (slope_positive U C cone).le (slope_bound U C cone Γ)
    (geometry.borel Γ.val Γ.property.1) b
    (geometry.projection_open Γ.val Γ.property.1 _ (slope_positive U C cone).le (slope_bound U C cone Γ))

theorem leaves_image (Γ : Index U C) :
    (leaves U C cone μ b geometry Γ).graph '' (leaves U C cone μ b geometry Γ).domain = Γ.val :=
  FakeLeafGraph.asGraphLeaf_image U Γ.val (slope_positive U C cone).le (slope_bound U C cone Γ)
    (geometry.borel Γ.val Γ.property.1) b _

theorem leaves_measure (Γ : Index U C) :
    (leaves U C cone μ b geometry Γ).measure μ = inducedVolume U μ Γ.val :=
  geometry.area Γ.val Γ.property.1 _ (slope_positive U C cone).le (slope_bound U C cone Γ)

/-- The constructed ambient leaf target has exactly the manuscript's
supremum of induced-volume L¹ norms. -/
theorem norm_eq_induced_sup
    (z : GraphLeafNorm.AmbientFamilySpace μ (leaves U C cone μ b geometry))
    (f : E → ℂ)
    (represents : ∀ Γ, z Γ =ᵐ[(leaves U C cone μ b geometry Γ).measure μ] f) :
    ‖z‖ = ⨆ Γ : Index U C, ∫ x, ‖f x‖ ∂inducedVolume U μ Γ.val := by
  rw [lp.norm_eq_ciSup]
  congr 1
  funext Γ
  rw [L1.norm_eq_integral_norm]
  calc
    (∫ x, ‖z Γ x‖ ∂(leaves U C cone μ b geometry Γ).measure μ) =
        ∫ x, ‖f x‖ ∂(leaves U C cone μ b geometry Γ).measure μ :=
      integral_congr_ae (by filter_upwards [represents Γ] with x same; rw [same])
    _ = _ := congrArg (fun ν : Measure E => ∫ x, ‖f x‖ ∂ν) (leaves_measure U C cone μ b geometry Γ)
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
