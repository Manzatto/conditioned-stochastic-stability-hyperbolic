module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ProductGapMarginal
public import ConditionedStochasticStabilityHyperbolic.Paper.LocalSpectralWitness
public import LeanShared.Probability.EigenvectorSupport

/-! The full literal local conclusion descends from an independently killed
product and an auxiliary saddle. Original-factor rank-one data, its left
measure, core support and qualified uniqueness are all constructed. -/

public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.ProductLocalPoint
open LeanShared ProductSpectralRetraction

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [CompactSpace X] [CompactSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
  [BorelSpace X] [BorelSpace Y] [SecondCountableTopology Y]
  (C : AbsorbingMarkovChains.CanonicalChain X)
  (D : AbsorbingMarkovChains.CanonicalChain Y)
  (CD : AbsorbingMarkovChains.CanonicalChain (X × Y))
  (sf : HasStrongFellerKernel C) (sd : HasStrongFellerKernel D)
  (scd : HasStrongFellerKernel CD)

include sf in
/-- Auxiliary and product spectral data yield the original QEM, its exact
raw spectral witness and support-qualified uniqueness. The product identity
is for the actual killed kernels. -/
theorem exists_point
    (independent : ∀ x y, CD.killedTransition (x, y) =
      (C.killedTransition x).prod (D.killedTransition y))
    (dy : RankOneSpectralData (strongFellerTransferOperator D sd) (1 : Y →ᵇ ℝ))
    (dxy : RankOneSpectralData (strongFellerTransferOperator CD scd) (1 : X × Y →ᵇ ℝ))
    (νxy : ProbabilityMeasure (X × Y))
    (product : (νxy : Measure (X × Y)) = eigenvectorMeasure
      (dxy.eigenmeasure (fun f hf z => by
        rw [strongFellerTransferOperator_represents]
        exact integral_nonneg hf)) dxy.eigenvector)
    (core : Set X) (hcore : core.Nonempty) (y : Y) (hy : 0 < dy.eigenvector y)
    (support : ∀ x ∈ core, (x, y) ∈ (νxy : Measure (X × Y)).support)
    (positive : ∀ x ∈ core, 0 < dxy.eigenvector (x, y))
    (R : ℝ) (hR : 0 < R) :
    ∃ ν : ProbabilityMeasure X, LocalConclusions.Point C R core ν ∧
      (ν : Measure X) = (νxy : Measure (X × Y)).map Prod.fst := by
  let : IsFiniteKernel C.killedTransition := by
    change IsFiniteKernel C.toKilledKernel.kernel
    infer_instance
  let : IsFiniteKernel D.killedTransition := by
    change IsFiniteKernel D.toKilledKernel.kernel
    infer_instance
  let PX := strongFellerTransferOperator C sf
  let PY := strongFellerTransferOperator D sd
  let PXY := strongFellerTransferOperator CD scd
  have posX : ∀ f : X →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ PX f x := by
    intro f hf x
    rw [strongFellerTransferOperator_represents]
    exact integral_nonneg hf
  have posXY : ∀ f : X × Y →ᵇ ℝ, (∀ z, 0 ≤ f z) → ∀ z, 0 ≤ PXY f z := by
    intro f hf z
    rw [strongFellerTransferOperator_represents]
    exact integral_nonneg hf
  have repXY (f : X × Y →ᵇ ℝ) (x : X) (y : Y) :
      PXY f (x, y) = ∫ z, f z ∂(C.killedTransition x).prod (D.killedTransition y) := by
    rw [strongFellerTransferOperator_represents, independent]
  let μxy := dxy.eigenmeasure posXY
  have : IsFiniteMeasure μxy := by dsimp only [μxy]; infer_instance
  have hrepXY : ∀ f : X × Y →ᵇ ℝ, dxy.mean f = ∫ z, f z ∂μxy :=
    dxy.eigenmeasure_represents posXY
  have hprod : (νxy : Measure (X × Y)) = eigenvectorMeasure μxy dxy.eigenvector := product
  obtain ⟨x₀, hx₀⟩ := hcore
  have hac : (νxy : Measure (X × Y)) ≪ μxy := by
    rw [hprod]
    exact withDensity_absolutelyContinuous _ _
  have pairing : 0 < dxy.mean (tensorLift dy.eigenvector (1 : X →ᵇ ℝ)) :=
    pairing_positive_of_supported_seed D.killedTransition PY PXY
      (strongFellerTransferOperator_represents D sd) dy dxy μxy hrepXY x₀ y
      (hac.support_mono (support x₀ hx₀)) hy
  let dx := descend C.killedTransition D.killedTransition PX PY PXY
    (strongFellerTransferOperator_represents C sf) (strongFellerTransferOperator_represents D sd)
    repXY dy dxy pairing
  let dr := dx.rescale R hR
  have posR : ∀ f : X →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ (R • PX) f x := by
    intro f hf x
    exact mul_nonneg hR.le (posX f hf x)
  let μ := dr.eigenmeasure posR
  have : IsFiniteMeasure μ := by dsimp only [μ]; infer_instance
  have hrep : ∀ f : X →ᵇ ℝ, dx.mean f = ∫ x, f x ∂μ := dr.eigenmeasure_represents posR
  have hg := dx.eigenvector_nonneg_of_positive posX
  have : IsProbabilityMeasure (eigenvectorMeasure μ dx.eigenvector) :=
    eigenvector_product_isProbability dx μ hrep hg
  let ν : ProbabilityMeasure X := ⟨eigenvectorMeasure μ dx.eigenvector, inferInstance⟩
  have hmap : (ν : Measure X) = (νxy : Measure (X × Y)).map Prod.fst := by
    rw [hprod]
    exact descended_product_eq_first_marginal C.killedTransition D.killedTransition PX PY PXY
      (strongFellerTransferOperator_represents C sf) (strongFellerTransferOperator_represents D sd)
      repXY dy dxy pairing μ μxy hrep hrepXY hg (dxy.eigenvector_nonneg_of_positive posXY)
  have hgcore : ∀ x ∈ core, 0 < dx.eigenvector x := by
    intro x hx
    exact descended_eigenvector_pos C.killedTransition D.killedTransition PX PY PXY
      (strongFellerTransferOperator_represents C sf) (strongFellerTransferOperator_represents D sd)
      repXY dy dxy pairing x y hy (positive x hx)
  have hsupp : core ⊆ (ν : Measure X).support := by
    rw [hmap]
    exact fun x hx => first_mem_support_map _ x y (support x hx)
  have hq : C.IsQuasiErgodic (ν : Measure X) :=
    QuasiErgodic.strongFeller_rankOne_isQuasiErgodic C sf dx μ hrep hg
  have unique : ∀ ζ : Measure X, C.IsQuasiErgodic ζ → core ⊆ ζ.support → ζ = (ν : Measure X) := by
    intro ζ hζ hsζ
    exact QuasiErgodic.eq_eigenvectorMeasure_of_basicSet_support C PX
      (strongFellerTransferOperator_represents C sf) dx μ hrep hg core ⟨x₀, hx₀⟩ hgcore ζ hζ hsζ
  refine ⟨ν, ?_, hmap⟩
  exact LocalConclusions.point_of_rankOne C R sf dr posR ν core rfl hq hsupp unique

end ConditionedStochasticStabilityHyperbolic.Paper.ProductLocalPoint
