module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafCharts
public import LeanShared.Analysis.GraphLeafReparam

/-! Every chart may have its own transverse unstable plane. Orthonormal
parameter changes put their complete fake-leaf families over one common
Euclidean parameter space, preserving their actual induced measures. -/
public noncomputable section
open Set MeasureTheory
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel.Heterogeneous
open LeanShared
variable {E P J ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasurableSpace P] [BorelSpace P] [Finite J] [Fintype ι] [DecidableEq ι]
  (planes : J → Submodule ℝ E) (cones : J → Set E) (cone : ∀ j, ConeData (planes j) (cones j))

abbrev ChartIndex := ∀ j : J, Index (planes j) (cones j)

def defaultIndex : ChartIndex planes cones := fun j => emptyIndex (planes j) (cones j)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Finite J] in
theorem evaluation_surjective (j : J) : Function.Surjective (fun a : ChartIndex planes cones => a j) := by
  classical
  intro Γ
  refine ⟨Function.update (defaultIndex planes cones) j Γ, ?_⟩
  dsimp only
  exact Function.update_self (β := fun j : J => Index (planes j) (cones j)) j Γ _

def commonSlope : ℝ := max 1 (Classical.choose (Finite.exists_le (fun j => slope (planes j) (cones j) (cone j))))

omit [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [FiniteDimensional ℝ P] [MeasurableSpace P] [BorelSpace P] [Fintype ι] [DecidableEq ι] in
theorem commonSlope_positive : 0 < commonSlope planes cones cone :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

omit [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [FiniteDimensional ℝ P] [MeasurableSpace P] [BorelSpace P] [Fintype ι] [DecidableEq ι] in
theorem slope_le_common (j : J) : slope (planes j) (cones j) (cone j) ≤ commonSlope planes cones cone :=
  (Classical.choose_spec (Finite.exists_le (fun j => slope (planes j) (cones j) (cone j))) j).trans (le_max_right _ _)

omit [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [FiniteDimensional ℝ P] [MeasurableSpace P] [BorelSpace P] [Fintype ι] [DecidableEq ι] in
theorem chart_slope (j : J) (Γ : Index (planes j) (cones j)) : ∀ x ∈ Γ.val, ∀ y ∈ Γ.val,
    ‖(planes j)ᗮ.starProjection (x - y)‖ ≤ commonSlope planes cones cone * ‖(planes j).starProjection (x - y)‖ := by
  intro x hx y hy
  exact (slope_bound (planes j) (cones j) (cone j) Γ x hx y hy).trans
    (mul_le_mul_of_nonneg_right (slope_le_common planes cones cone j) (norm_nonneg _))

variable (μ : Measure P) (coordinates : ∀ j, P ≃ₗᵢ[ℝ] planes j)
  (basis : ∀ j, OrthonormalBasis ι ℝ (planes j))
  (area : ∀ j, ClassicalGeometry (planes j) (μ.map (coordinates j)) (basis j))

def rawLeaves (j : J) (a : ChartIndex planes cones) : GraphLeafNorm.GraphLeaf (planes j) E
    (GraphJacobian.densityBound (ι := ι) (commonSlope planes cones cone)) :=
  FakeLeafGraph.asGraphLeaf (planes j) (a j).val (commonSlope_positive planes cones cone).le
    (chart_slope planes cones cone j (a j)) ((area j).borel (a j).val (a j).property.1) (basis j)
    ((area j).projection_open (a j).val (a j).property.1 _ (commonSlope_positive planes cones cone).le
      (chart_slope planes cones cone j (a j)))

def leaves (j : J) (a : ChartIndex planes cones) : GraphLeafNorm.GraphLeaf P E
    (GraphJacobian.densityBound (ι := ι) (commonSlope planes cones cone)) :=
  (rawLeaves planes cones cone μ coordinates basis area j a).reparam (coordinates j)

omit [FiniteDimensional ℝ P] in
theorem leaves_measure (j : J) (a : ChartIndex planes cones) :
    (leaves planes cones cone μ coordinates basis area j a).measure μ =
      inducedVolume (planes j) (μ.map (coordinates j)) (a j).val := by
  rw [leaves, GraphLeafNorm.GraphLeaf.reparam_measure]
  exact (area j).area (a j).val (a j).property.1 _ (commonSlope_positive planes cones cone).le
    (chart_slope planes cones cone j (a j))

omit [FiniteDimensional ℝ P] in
/-- Exact chart norm on the full literal family, with each chart's actual
transverse plane and isometrically transported Haar normalization. -/
theorem norm_eq_induced_sup (j : J)
    (z : GraphLeafNorm.AmbientFamilySpace μ (leaves planes cones cone μ coordinates basis area j))
    (f : E → ℂ)
    (represents : ∀ a, z a =ᵐ[(leaves planes cones cone μ coordinates basis area j a).measure μ] f) :
    ‖z‖ = ⨆ Γ : Index (planes j) (cones j),
      ∫ x, ‖f x‖ ∂inducedVolume (planes j) (μ.map (coordinates j)) Γ.val := by
  rw [lp.norm_eq_ciSup]
  have integrals : ∀ a : ChartIndex planes cones, ‖z a‖ =
      ∫ x, ‖f x‖ ∂inducedVolume (planes j) (μ.map (coordinates j)) (a j).val := by
    intro a
    rw [L1.norm_eq_integral_norm]
    calc
      (∫ x, ‖z a x‖ ∂(leaves planes cones cone μ coordinates basis area j a).measure μ) =
          ∫ x, ‖f x‖ ∂(leaves planes cones cone μ coordinates basis area j a).measure μ :=
        integral_congr_ae (by filter_upwards [represents a] with x same; rw [same])
      _ = _ := congrArg (fun ν : Measure E => ∫ x, ‖f x‖ ∂ν)
        (leaves_measure planes cones cone μ coordinates basis area j a)
  simp_rw [integrals]
  have ranges : Set.range (fun a : ChartIndex planes cones =>
      ∫ x, ‖f x‖ ∂inducedVolume (planes j) (μ.map (coordinates j)) (a j).val) =
      Set.range (fun Γ : Index (planes j) (cones j) =>
        ∫ x, ‖f x‖ ∂inducedVolume (planes j) (μ.map (coordinates j)) Γ.val) := by
    ext r
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a j, rfl⟩
    · rintro ⟨Γ, rfl⟩
      obtain ⟨a, same⟩ := evaluation_surjective planes cones j Γ
      exact ⟨a, congrArg (fun Γ : Index (planes j) (cones j) =>
        ∫ x, ‖f x‖ ∂inducedVolume (planes j) (μ.map (coordinates j)) Γ.val) same⟩
  exact congrArg sSup ranges
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel.Heterogeneous
