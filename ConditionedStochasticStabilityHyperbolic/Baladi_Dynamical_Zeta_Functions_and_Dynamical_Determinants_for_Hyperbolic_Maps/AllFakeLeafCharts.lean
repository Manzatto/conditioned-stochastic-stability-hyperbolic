module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel

/-! A single canonical index type covers every paper fake leaf in every
chart. Empty leaves provide actual defaults; finite chart families have one
constructed cone/Gram bound. No arbitrary chart leaf family is supplied. -/
public noncomputable section
open Set MeasureTheory IsManifold
open scoped Manifold ContDiff Topology
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem embedded_empty (U : Submodule ℝ E) : C1Embedded U (∅ : Set E) := by
  let charts := ChartedSpace.empty U (↥(∅ : Set E))
  let _ := charts
  refine ⟨charts, ?_, ?_, ?_⟩
  · apply isManifold_of_contDiffOn
    intro e _ he _
    exact False.elim he
  · intro x
    exact False.elim x.property
  · intro x
    exact False.elim x.property

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem fake_empty (U : Submodule ℝ E) (C : Set E) :
    FakeLeafGeometry.leafError C (Module.finrank ℝ Uᗮ) (∅ : Set E) = 0 := by
  simp [FakeLeafGeometry.leafError, FakeLeafGeometry.leafErrorValues]

def emptyIndex (U : Submodule ℝ E) (C : Set E) : Index U C :=
  ⟨∅, embedded_empty U, fake_empty U C⟩

variable {J : Type*} (U : Submodule ℝ E) (cones : J → Set E)

abbrev ChartIndex := ∀ j : J, Index U (cones j)

def defaultIndex : ChartIndex U cones := fun j => emptyIndex U (cones j)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem evaluation_surjective (j : J) : Function.Surjective (fun a : ChartIndex U cones => a j) := by
  classical
  intro Γ
  refine ⟨Function.update (defaultIndex U cones) j Γ, ?_⟩
  dsimp only
  exact Function.update_self (β := fun j : J => Index U (cones j)) j Γ _

variable [Finite J] (cone : ∀ j, ConeData U (cones j))

def commonSlope : ℝ := max 1 (Classical.choose (Finite.exists_le (fun j => slope U (cones j) (cone j))))

omit [MeasurableSpace E] [BorelSpace E] in
theorem commonSlope_positive : 0 < commonSlope U cones cone := lt_of_lt_of_le zero_lt_one (le_max_left _ _)

omit [MeasurableSpace E] [BorelSpace E] in
theorem slope_le_common (j : J) : slope U (cones j) (cone j) ≤ commonSlope U cones cone :=
  (Classical.choose_spec (Finite.exists_le (fun j => slope U (cones j) (cone j))) j).trans (le_max_right _ _)

omit [MeasurableSpace E] [BorelSpace E] in
theorem chart_slope (j : J) (Γ : Index U (cones j)) : ∀ x ∈ Γ.val, ∀ y ∈ Γ.val,
    ‖Uᗮ.starProjection (x - y)‖ ≤ commonSlope U cones cone * ‖U.starProjection (x - y)‖ := by
  intro x hx y hy
  exact (slope_bound U (cones j) (cone j) Γ x hx y hy).trans
    (mul_le_mul_of_nonneg_right (slope_le_common U cones cone j) (norm_nonneg _))

variable (μ : Measure U) {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : OrthonormalBasis ι ℝ U) (geometry : ClassicalGeometry U μ b)

def chartLeaves (j : J) (a : ChartIndex U cones) : GraphLeafNorm.GraphLeaf U E
    (GraphJacobian.densityBound (ι := ι) (commonSlope U cones cone)) :=
  FakeLeafGraph.asGraphLeaf U (a j).val (commonSlope_positive U cones cone).le
    (chart_slope U cones cone j (a j)) (geometry.borel (a j).val (a j).property.1) b
    (geometry.projection_open (a j).val (a j).property.1 _ (commonSlope_positive U cones cone).le
      (chart_slope U cones cone j (a j)))

theorem chartLeaves_measure (j : J) (a : ChartIndex U cones) :
    (chartLeaves U cones cone μ b geometry j a).measure μ = inducedVolume U μ (a j).val :=
  geometry.area (a j).val (a j).property.1 _ (commonSlope_positive U cones cone).le
    (chart_slope U cones cone j (a j))

theorem chartLeaves_image (j : J) (a : ChartIndex U cones) :
    (chartLeaves U cones cone μ b geometry j a).graph ''
      (chartLeaves U cones cone μ b geometry j a).domain = (a j).val :=
  FakeLeafGraph.asGraphLeaf_image U (a j).val (commonSlope_positive U cones cone).le
    (chart_slope U cones cone j (a j)) (geometry.borel (a j).val (a j).property.1) b _

/-- In every chart the constructed family's norm is exactly the supremum
over ALL fake C¹ leaves, despite the common cross-chart index type. -/
theorem chart_norm_eq_induced_sup (j : J)
    (z : GraphLeafNorm.AmbientFamilySpace μ (chartLeaves U cones cone μ b geometry j))
    (f : E → ℂ)
    (represents : ∀ a, z a =ᵐ[(chartLeaves U cones cone μ b geometry j a).measure μ] f) :
    ‖z‖ = ⨆ Γ : Index U (cones j), ∫ x, ‖f x‖ ∂inducedVolume U μ Γ.val := by
  rw [lp.norm_eq_ciSup]
  have integrals : ∀ a : ChartIndex U cones, ‖z a‖ = ∫ x, ‖f x‖ ∂inducedVolume U μ (a j).val := by
    intro a
    rw [L1.norm_eq_integral_norm]
    calc
      (∫ x, ‖z a x‖ ∂(chartLeaves U cones cone μ b geometry j a).measure μ) =
          ∫ x, ‖f x‖ ∂(chartLeaves U cones cone μ b geometry j a).measure μ :=
        integral_congr_ae (by filter_upwards [represents a] with x same; rw [same])
      _ = _ := congrArg (fun ν : Measure E => ∫ x, ‖f x‖ ∂ν) (chartLeaves_measure U cones cone μ b geometry j a)
  simp_rw [integrals]
  have ranges : Set.range (fun a : ChartIndex U cones => ∫ x, ‖f x‖ ∂inducedVolume U μ (a j).val) =
      Set.range (fun Γ : Index U (cones j) => ∫ x, ‖f x‖ ∂inducedVolume U μ Γ.val) := by
    ext r
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a j, rfl⟩
    · rintro ⟨Γ, rfl⟩
      obtain ⟨a, same⟩ := evaluation_surjective U cones j Γ
      exact ⟨a, congrArg (fun Γ : Index U (cones j) => ∫ x, ‖f x‖ ∂inducedVolume U μ Γ.val) same⟩
  exact congrArg sSup ranges
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
