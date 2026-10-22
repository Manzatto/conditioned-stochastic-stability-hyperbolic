module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafTransportedGeometry
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafHeterogeneousCharts
public import LeanShared.Analysis.CompactSchwartzHolderBlocks

/-! Actual compact-support Hölder bounds for the complete heterogeneous
fake-leaf family, with canonical Euclidean parameter measure. -/

public noncomputable section
open MeasureTheory
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafHolderCoreBounds
open LeanShared AllFakeLeafModel

variable {E I ι : Type*} [Finite I] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (planes : I → Submodule ℝ E) (plus : I → Set E)
  (cone : ∀ i, ConeData (planes i) (plus i))
  (coordinates : ∀ i, EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] planes i)
  (basis : ∀ i, OrthonormalBasis ι ℝ (planes i))

@[expose] def leaves := Heterogeneous.leaves planes plus cone
  (volume : Measure (EuclideanSpace ℝ ι)) coordinates basis
  (transportedGeometry planes (volume : Measure (EuclideanSpace ℝ ι)) coordinates basis)

variable {minus : Set E} (radial : ConeDyadicSymbols.RadialCutoff)
  {Cp : Set E} (angle : ConeDyadicSymbols.AngularCutoff Cp minus)
  {K : Set E} (compactK : IsCompact K) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
  (exponent : Bool → ℝ) (margin : ∀ sign, exponent sign ≤ b) (i : I)

include compactK hb hb1 margin in
theorem bounded : SchwartzAmbientBlocks.SmoothCoreBounded
    (volume : Measure (EuclideanSpace ℝ ι))
    (GraphJacobian.densityBound_nonneg (ι := ι) (Heterogeneous.commonSlope planes plus cone))
    (leaves planes plus cone coordinates basis i) K
    (ConeDyadicSymbols.symbols radial angle) exponent :=
  CompactSchwartzHolderBlocks.bounded volume _ (leaves planes plus cone coordinates basis i)
    radial angle compactK hb hb1 exponent margin

@[expose] def constant : ℝ := Classical.choose (CompactSchwartzHolderBlocks.bound
  (volume : Measure (EuclideanSpace ℝ ι))
  (GraphJacobian.densityBound_nonneg (ι := ι) (Heterogeneous.commonSlope planes plus cone))
  (leaves planes plus cone coordinates basis i) radial angle compactK hb hb1 exponent margin)

include hb hb1 margin in
theorem bound
    (bd : SchwartzAmbientBlocks.SmoothCoreBounded
      (volume : Measure (EuclideanSpace ℝ ι))
      (GraphJacobian.densityBound_nonneg (ι := ι) (Heterogeneous.commonSlope planes plus cone))
      (leaves planes plus cone coordinates basis i) K
      (ConeDyadicSymbols.symbols radial angle) exponent)
    (f : SchwartzJetSpace.supportedCore K) :
    ‖SchwartzAmbientBlocks.coreMap (volume : Measure (EuclideanSpace ℝ ι))
      (GraphJacobian.densityBound_nonneg (ι := ι) (Heterogeneous.commonSlope planes plus cone))
      (leaves planes plus cone coordinates basis i) K
      (ConeDyadicSymbols.symbols radial angle) exponent bd f‖ ≤
      constant planes plus cone coordinates basis radial angle compactK hb hb1 exponent margin i *
        ‖CompactSchwartzHolderCore.core compactK hb hb1 f‖ :=
  (Classical.choose_spec (CompactSchwartzHolderBlocks.bound volume _
    (leaves planes plus cone coordinates basis i) radial angle compactK hb hb1 exponent margin)).2 bd f

end ConditionedStochasticStabilityHyperbolic.AllFakeLeafHolderCoreBounds
