module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafNativeInputBounds
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel

/-! The heterogeneous native graph family uses exactly the canonical
induced Euclidean volume, for every chart and every full fake leaf. This
identity transports physical principal/nonlinked rows to the actual norm. -/
public noncomputable section
open Set MeasureTheory
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafHolderCoreBounds
open LeanShared AllFakeLeafModel
variable {E I ι : Type*} [Finite I] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (planes : I → Submodule ℝ E) (plus : I → Set E)
  (cone : ∀ i, ConeData (planes i) (plus i))
  (coordinates : ∀ i, EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] planes i)
  (basis : ∀ i, OrthonormalBasis ι ℝ (planes i))

theorem native_leaf_measure (i : I) (a : Heterogeneous.ChartIndex planes plus) :
    (leaves planes plus cone coordinates basis i a).measure volume =
      EmbeddedSubmanifoldVolume.volume (planes i) volume (a i).val := by
  have volumeMap : (volume : Measure (EuclideanSpace ℝ ι)).map (coordinates i) = volume :=
    (coordinates i).measurePreserving.map_eq
  rw [leaves, Heterogeneous.leaves_measure, volumeMap]
  rfl

end ConditionedStochasticStabilityHyperbolic.AllFakeLeafHolderCoreBounds
