module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafCanonicalDistribution
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.LocalCompactEmbedding
public import LeanShared.Analysis.ConstructedSchwartzCutoff

/-! Strict weakening of the actual all-fake-leaf norm is compact and injective
with the original leaf family and Fourier cutoffs. Its finite distribution
order and smoothing identity are proved internally. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafCanonicalSameConeCompact
open LeanShared AllFakeLeafModel AllFakeLeafCanonicalDistribution
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι:Type*} [Fintype ι] [DecidableEq ι]
  (U:Submodule ℝ E) (C:Set E) (cone:ConeData U C) (basis:OrthonormalBasis ι ℝ U)
  {Cp Cm:Set E} (radial:ConeDyadicSymbols.RadialCutoff)
  (angle:ConeDyadicSymbols.AngularCutoff Cp Cm)
  {K:Set E} (compact:IsCompact K) (exponent:Bool→ℝ)
  {loss:ℝ} (positive:0<loss) (extra:Bool→ℝ) (nonnegative:∀b,0≤extra b)

theorem compact_injective :
    IsCompactOperator (DyadicCompletion.exactInclusion
      (core U C cone basis radial angle compact exponent) loss positive extra nonnegative) ∧
    Function.Injective (DyadicCompletion.exactInclusion
      (core U C cone basis radial angle compact exponent) loss positive extra nonnegative) := by
  let radius := max 0 compact.isBounded.exists_norm_le.choose
  have radiusNonnegative : 0≤radius := le_max_left _ _
  have supported (x:E) (hx:x∈K) : ‖x‖≤radius :=
    (compact.isBounded.exists_norm_le.choose_spec x hx).trans (le_max_right _ _)
  let L := Metric.closedBall (0:E) (radius+2)
  let cutoff := ConstructedSchwartzCutoff.cutoff radius radiusNonnegative (E:=E)
  let order := AllFakeLeafDyadicDistribution.growth exponent+1
  let words := LaplacianFiniteJet.testWords (stdOrthonormalBasis ℝ E) order
  let coefficient := AllFakeLeafDyadicDistribution.constant U C cone basis radial angle exponent*
    ((1+(radius+2))^(AllFakeLeafDistribution.order U)*
      (Fintype.card (LaplacianFiniteJet.Index (Fin (Module.finrank ℝ E)) 0)+
        Fintype.card (LaplacianFiniteJet.Index (Fin (Module.finrank ℝ E)) order)))
  apply LocalCompactEmbedding.compact_injective_exactInclusion volume
    (AllFakeLeafDyadicDistribution.slopeBound U C cone basis)
    (AllFakeLeafDyadicDistribution.family U C cone basis) K radial angle exponent
    (bounded U C cone basis radial angle compact exponent) words
    (show IsCompact L from isCompact_closedBall _ _) cutoff
    (fun x hx=>ConstructedSchwartzCutoff.supported radius radiusNonnegative x hx)
    (fun x hx=>ConstructedSchwartzCutoff.one radius radiusNonnegative (supported x hx))
    (pair U C cone basis radial angle compact exponent) coefficient
  · exact mul_nonneg
      (AllFakeLeafDyadicDistribution.constant_nonnegative U C cone basis radial angle exponent)
      (by positivity)
  · intro z test support
    exact AllFakeLeafDyadicDistribution.finite_order_bound U C cone basis radial angle K exponent
      (bounded U C cone basis radial angle compact exponent) (stdOrthonormalBasis ℝ E) L
      Metric.isClosed_closedBall (radius+2) (by linarith)
      (fun x hx=>by simpa only [L,Metric.mem_closedBall,dist_zero_right] using hx) z test support
  · intro f test
    exact AllFakeLeafDyadicDistribution.pairing_core U C cone basis radial angle K exponent
      (bounded U C cone basis radial angle compact exponent) f test
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafCanonicalSameConeCompact
