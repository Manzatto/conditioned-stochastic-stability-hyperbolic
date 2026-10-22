module

public import LeanShared.Analysis.FakeLeafGeometry
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import LeanShared.Analysis.EuclideanGraphLeaf

/-!
# Genuine graph representation over the fake leaf's projection image

The graph domain is the actual unstable projection image; it need not be all
of the reference subspace. The inverse and graph height are constructed from
the checked secant slope, not assumed. Borel measurability follows from the
injective-image theorem. Openness, C¹ regularity, and induced area identification
are separate geometric facts and are not asserted here.
-/

@[expose] public noncomputable section

open Set

namespace LeanShared.FakeLeafGraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  (U : Submodule ℝ E) (Γ : Set E) {L : ℝ} (hL : 0 ≤ L)
  (hslope : ∀ x ∈ Γ, ∀ y ∈ Γ,
    ‖Uᗮ.starProjection (x - y)‖ ≤ L * ‖U.starProjection (x - y)‖)

def projection : Γ → U := fun x => U.orthogonalProjectionOnto (x : E)

def parameterDomain : Set U := range (projection U Γ)

theorem projection_continuous : Continuous (projection U Γ) :=
  U.orthogonalProjectionOnto.continuous.comp continuous_subtype_val

include hL hslope in
theorem projection_injective : Function.Injective (projection U Γ) :=
  (ConeGraphGeometry.leafProjection_antilipschitz U hL hslope).injective

/-- Every leaf point has exactly one parameter in the actual projection image. -/
def parameterEquiv : Γ ≃ parameterDomain U Γ :=
  Equiv.ofInjective (projection U Γ) (projection_injective U Γ hL hslope)

/-- The actual inverse parameterization, with values remaining in the leaf. -/
def point (u : parameterDomain U Γ) : Γ := (parameterEquiv U Γ hL hslope).symm u

theorem point_projection (u : parameterDomain U Γ) :
    projection U Γ (point U Γ hL hslope u) = (u : U) :=
  Equiv.apply_ofInjective_symm (projection_injective U Γ hL hslope) u

theorem point_of_projection (x : Γ) :
    point U Γ hL hslope ⟨projection U Γ x, x, rfl⟩ = x :=
  Equiv.ofInjective_symm_apply (projection_injective U Γ hL hslope) x

/-- The graph height in the genuine orthogonal complement. -/
def height (u : parameterDomain U Γ) : Uᗮ :=
  Uᗮ.orthogonalProjectionOnto (point U Γ hL hslope u : E)

theorem point_eq_graph (u : parameterDomain U Γ) :
    (point U Γ hL hslope u : E) = (u : U) + (height U Γ hL hslope u : E) := by
  have hp := congrArg Subtype.val (point_projection U Γ hL hslope u)
  change U.starProjection (point U Γ hL hslope u : E) = ((u : U) : E) at hp
  rw [← hp]
  exact (U.starProjection_add_starProjection_orthogonal _).symm

/-- The uniform secant constant is exactly a Lipschitz bound on the graph height. -/
theorem height_lipschitz : LipschitzWith (Real.toNNReal L) (height U Γ hL hslope) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [Real.coe_toNNReal L hL]
  have hh := hslope (point U Γ hL hslope u) (point U Γ hL hslope u).property
    (point U Γ hL hslope v) (point U Γ hL hslope v).property
  have hpu : U.orthogonalProjectionOnto (point U Γ hL hslope u : E) = (u : U) :=
    point_projection U Γ hL hslope u
  have hpv : U.orthogonalProjectionOnto (point U Γ hL hslope v : E) = (v : U) :=
    point_projection U Γ hL hslope v
  simpa only [height, dist_eq_norm, Subtype.dist_eq, map_sub,
    Submodule.starProjection_apply, ← Submodule.coe_sub, Submodule.norm_coe,
    hpu, hpv] using hh

/-- The inverse parameterization has a common Lipschitz bound. -/
theorem point_lipschitz : LipschitzWith (Real.toNNReal (1 + L)) (point U Γ hL hslope) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have hh := (ConeGraphGeometry.leafProjection_antilipschitz U hL hslope).le_mul_dist
    (point U Γ hL hslope u) (point U Γ hL hslope v)
  change dist (point U Γ hL hslope u) (point U Γ hL hslope v) ≤
    _ * dist (projection U Γ (point U Γ hL hslope u))
      (projection U Γ (point U Γ hL hslope v)) at hh
  simpa only [point_projection, Subtype.dist_eq] using hh

theorem range_point : range (fun u : parameterDomain U Γ => (point U Γ hL hslope u : E)) = Γ := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact (point U Γ hL hslope u).property
  · intro hx
    refine ⟨⟨projection U Γ ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩, ?_⟩
    exact congrArg Subtype.val (point_of_projection U Γ hL hslope ⟨x, hx⟩)

theorem graph_image : range (fun u : parameterDomain U Γ =>
    ((u : U) : E) + (height U Γ hL hslope u : E)) = Γ := by
  simpa only [← point_eq_graph] using range_point U Γ hL hslope

section Measurability

variable [MeasurableSpace E] [BorelSpace E] (hΓ : MeasurableSet Γ)

include hL hslope hΓ in
/-- Lusin--Souslin makes the injective projection of a Borel leaf a measurable embedding. -/
theorem projection_measurableEmbedding : MeasurableEmbedding (projection U Γ) := by
  apply ContinuousOn.measurableEmbedding hΓ U.orthogonalProjectionOnto.continuous.continuousOn
  intro x hx y hy hxy
  exact congrArg Subtype.val (projection_injective U Γ hL hslope
    (show projection U Γ ⟨x, hx⟩ = projection U Γ ⟨y, hy⟩ from hxy))

include hL hslope hΓ in
theorem parameterDomain_measurable : MeasurableSet (parameterDomain U Γ) :=
  (projection_measurableEmbedding U Γ hL hslope hΓ).measurableSet_range

theorem height_measurable : Measurable (height U Γ hL hslope) :=
  (height_lipschitz U Γ hL hslope).continuous.measurable

theorem point_measurable : Measurable (point U Γ hL hslope) :=
  (point_lipschitz U Γ hL hslope).continuous.measurable

/-- A measurable global field agreeing with the true height on the actual domain. -/
def heightExtension : U → Uᗮ :=
  Function.extend (Subtype.val : parameterDomain U Γ → U) (height U Γ hL hslope) (fun _ => 0)

omit [MeasurableSpace E] [BorelSpace E] in
theorem heightExtension_on_domain (u : parameterDomain U Γ) :
    heightExtension U Γ hL hslope (u : U) = height U Γ hL hslope u :=
  Subtype.val_injective.extend_apply _ _ u

include hΓ in
theorem heightExtension_measurable : Measurable (heightExtension U Γ hL hslope) :=
  (MeasurableEmbedding.subtype_coe (parameterDomain_measurable U Γ hL hslope hΓ)).measurable_extend
    (height_measurable U Γ hL hslope) measurable_const

omit [MeasurableSpace E] [BorelSpace E] in
theorem heightExtension_off_domain {u : U} (hu : u ∉ parameterDomain U Γ) :
    heightExtension U Γ hL hslope u = 0 := by
  apply Function.extend_apply'
  rintro ⟨v, hv⟩
  exact hu (hv ▸ v.property)

omit [MeasurableSpace E] [BorelSpace E] in
/-- The resulting global measurable graph has exactly the original leaf on its domain. -/
theorem graphExtension_image :
    ConeGraphGeometry.graphPoint U (heightExtension U Γ hL hslope) '' parameterDomain U Γ = Γ := by
  refine Eq.trans ?_ (graph_image U Γ hL hslope)
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    change (u : E) + (height U Γ hL hslope ⟨u, hu⟩ : E) =
      (u : E) + (heightExtension U Γ hL hslope u : E)
    rw [heightExtension_on_domain U Γ hL hslope ⟨u, hu⟩]
  · rintro ⟨u, rfl⟩
    refine ⟨(u : U), u.property, ?_⟩
    change ((u : U) : E) + (heightExtension U Γ hL hslope (u : U) : E) = _
    rw [heightExtension_on_domain]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The extension retains the uniform Lipschitz bound on the genuine parameter domain. -/
theorem heightExtension_lipschitzOn :
    LipschitzOnWith (Real.toNNReal L) (heightExtension U Γ hL hslope) (parameterDomain U Γ) := by
  intro u hu v hv
  have hh := (height_lipschitz U Γ hL hslope).edist_le_mul ⟨u, hu⟩ ⟨v, hv⟩
  rw [heightExtension_on_domain U Γ hL hslope ⟨u, hu⟩,
    heightExtension_on_domain U Γ hL hslope ⟨v, hv⟩]
  simpa only [Subtype.edist_eq] using hh

omit [MeasurableSpace E] [BorelSpace E] in
/-- On an open parameter domain the actual extension derivative has the uniform bound.
This asserts no differentiability: at points without a derivative `fderiv` is zero. -/
theorem heightExtension_derivative_norm_le (hopen : IsOpen (parameterDomain U Γ))
    {u : U} (hu : u ∈ parameterDomain U Γ) :
    ‖fderiv ℝ (heightExtension U Γ hL hslope) u‖ ≤ L := by
  simpa only [Real.coe_toNNReal L hL] using norm_fderiv_le_of_lipschitzOn ℝ
    (hopen.mem_nhds hu) (heightExtension_lipschitzOn U Γ hL hslope)

variable [MeasurableSpace (U →L[ℝ] Uᗮ)] [BorelSpace (U →L[ℝ] Uᗮ)]

/-- The derivative field of the actual extension is measurable; it need not be
replaced by an unrelated field supplied as an assumption. -/
theorem heightExtension_derivative_measurable :
    Measurable (fderiv ℝ (heightExtension U Γ hL hslope)) := by
  borelize (U →L[ℝ] Uᗮ)
  exact measurable_fderiv ℝ (heightExtension U Γ hL hslope)

section GraphMeasure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual fake-leaf graph and actual derivative produce the intrinsic
Gram-density graph measure, conditional on openness of the projection image.
Equality with the leaf's induced Riemannian volume is a separate area theorem. -/
def asGraphLeaf (b : OrthonormalBasis ι ℝ U) (hopen : IsOpen (parameterDomain U Γ)) :
    GraphLeafNorm.GraphLeaf U E (GraphJacobian.densityBound (ι := ι) L) :=
  EuclideanGraphLeaf.ofDerivativeField U b (heightExtension U Γ hL hslope)
    (heightExtension_measurable U Γ hL hslope hΓ)
    (parameterDomain U Γ) (parameterDomain_measurable U Γ hL hslope hΓ)
    (fderiv ℝ (heightExtension U Γ hL hslope))
    (heightExtension_derivative_measurable U Γ hL hslope)
    (fun _ hu => heightExtension_derivative_norm_le U Γ hL hslope hopen hu)

@[simp] theorem asGraphLeaf_domain (b : OrthonormalBasis ι ℝ U)
    (hopen : IsOpen (parameterDomain U Γ)) :
    (asGraphLeaf U Γ hL hslope hΓ b hopen).domain = parameterDomain U Γ := rfl

theorem asGraphLeaf_graph_on_domain (b : OrthonormalBasis ι ℝ U)
    (hopen : IsOpen (parameterDomain U Γ)) (u : parameterDomain U Γ) :
    (asGraphLeaf U Γ hL hslope hΓ b hopen).graph (u : U) = (point U Γ hL hslope u : E) := by
  change ((u : U) : E) + (heightExtension U Γ hL hslope (u : U) : E) = _
  rw [heightExtension_on_domain]
  exact (point_eq_graph U Γ hL hslope u).symm

theorem asGraphLeaf_image (b : OrthonormalBasis ι ℝ U)
    (hopen : IsOpen (parameterDomain U Γ)) :
    (asGraphLeaf U Γ hL hslope hΓ b hopen).graph ''
      (asGraphLeaf U Γ hL hslope hΓ b hopen).domain = Γ :=
  graphExtension_image U Γ hL hslope

/-- The literal fake-leaf condition, Borel measurability, and an open projection
image produce graph measures with one cone-derived volume-density constant. -/
theorem exists_uniform_fakeLeaf_graphLeaf (b : OrthonormalBasis ι ℝ U)
    {C : Set E} (hclosed : IsClosed C)
    (hscale : ∀ r : ℝ, 0 ≤ r → ∀ v ∈ C, r • v ∈ C)
    (htrans : ∀ v ∈ C, v ∈ U → v = 0)
    (hds : 0 < Module.finrank ℝ Uᗮ)
    (hplanes : (FakeLeafGeometry.admissiblePlanes C (Module.finrank ℝ Uᗮ)).Nonempty) :
    ∃ L : ℝ, 0 < L ∧ ∀ Γ' : Set E, MeasurableSet Γ' →
      FakeLeafGeometry.leafError C (Module.finrank ℝ Uᗮ) Γ' = 0 →
      IsOpen (parameterDomain U Γ') →
      ∃ leaf : GraphLeafNorm.GraphLeaf U E (GraphJacobian.densityBound (ι := ι) L),
        leaf.domain = parameterDomain U Γ' ∧ leaf.graph '' leaf.domain = Γ' := by
  obtain ⟨L, hL, hb⟩ := FakeLeafGeometry.exists_uniform_fakeLeaf_slope
    U hclosed hscale htrans hds hplanes
  refine ⟨L, hL, fun Γ' hΓ' hfake hopen => ?_⟩
  refine ⟨asGraphLeaf U Γ' hL.le (hb Γ' hfake) hΓ' b hopen, rfl, ?_⟩
  exact asGraphLeaf_image U Γ' hL.le (hb Γ' hfake) hΓ' b hopen

end GraphMeasure

end Measurability

end LeanShared.FakeLeafGraph
