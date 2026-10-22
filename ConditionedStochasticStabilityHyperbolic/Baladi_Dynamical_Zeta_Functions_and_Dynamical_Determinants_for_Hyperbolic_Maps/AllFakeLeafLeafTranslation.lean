module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafLowOrderPairing
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafTranslation
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel
meta import Lean.LibrarySuggestions.Basic

/-! The leaf measures of the complete heterogeneous fake-leaf family of each chart are closed under
translation: a translated leaf is again a leaf of the full family with the pushed-forward
induced volume, and an empty leaf has zero volume. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "AllFakeLeafLeafTranslation"

public noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory Set
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafLeafTranslation
open LeanShared AllFakeLeafModel

variable {E I ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Finite I] [DecidableEq I] [Fintype ι] [DecidableEq ι]
  (planes : I → Submodule ℝ E) (plus : I → Set E)
  (cone : ∀ i, ConeData (planes i) (plus i))
  (coordinates : ∀ i, EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] planes i)
  (basis : ∀ i, OrthonormalBasis ι ℝ (planes i)) (i : I)

theorem volume_empty {U : Submodule ℝ E} (μ : Measure U) {Γ : Set E} (h : ¬ Nonempty Γ) :
    EmbeddedSubmanifoldVolume.volume U μ Γ = 0 := by
  unfold EmbeddedSubmanifoldVolume.volume
  split_ifs with embedded
  · unfold EmbeddedSubmanifoldVolume.intrinsic
    rw [dite_eq_right h, Measure.map_zero]
  · rfl

theorem leaves_measure (a : Heterogeneous.ChartIndex planes plus) :
    (AllFakeLeafHolderCoreBounds.leaves planes plus cone coordinates basis i a).measure
        (volume : Measure (EuclideanSpace ℝ ι)) =
      inducedVolume (planes i) volume (a i).val := by
  rw [AllFakeLeafHolderCoreBounds.leaves, Heterogeneous.leaves_measure,
    (coordinates i).measurePreserving.map_eq]

/-- The chart leaf family is closed under translation. -/
theorem translate (a : Heterogeneous.ChartIndex planes plus) (z : E) :
    ∃ a', ((AllFakeLeafHolderCoreBounds.leaves planes plus cone coordinates basis i a).measure
        (volume : Measure (EuclideanSpace ℝ ι))).map (fun x => x + z) =
      (AllFakeLeafHolderCoreBounds.leaves planes plus cone coordinates basis i a').measure
        (volume : Measure (EuclideanSpace ℝ ι)) := by
  classical
  by_cases nonempty : Nonempty (a i).val
  · obtain ⟨image, -, moved⟩ := exists_translated_leaf (planes i) (cone i)
      (volume : Measure (planes i)) (a i) z
    refine ⟨Function.update a i image, ?_⟩
    rw [leaves_measure, leaves_measure, Function.update_self]
    exact moved
  · refine ⟨a, ?_⟩
    rw [leaves_measure]
    change (EmbeddedSubmanifoldVolume.volume (planes i) volume (a i).val).map (fun x => x + z) =
      EmbeddedSubmanifoldVolume.volume (planes i) volume (a i).val
    rw [volume_empty _ nonempty, Measure.map_zero]

end ConditionedStochasticStabilityHyperbolic.AllFakeLeafLeafTranslation
