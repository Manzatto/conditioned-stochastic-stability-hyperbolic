module

public import ConditionedStochasticStabilityHyperbolic.Global.LayerQuasiErgodic
public import ConditionedStochasticStabilityHyperbolic.Paper.LocalGapFamilyWindow

/-! The global layer producer and the local endpoint consumer use two
constructions of the same integral operator. Equality transports the actual
rank-one data and its Riesz eigenproduct; the probability is unchanged. -/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic

namespace RankOneSpectralData
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P Q : E →L[ℝ] E} {one : E}

def rewriteOperator (eq : P = Q) (d : RankOneSpectralData P one) :
    RankOneSpectralData Q one := eq ▸ d

@[simp] theorem rewriteOperator_vector (eq : P = Q) (d : RankOneSpectralData P one) :
    (d.rewriteOperator eq).eigenvector = d.eigenvector := by subst Q; rfl

@[simp] theorem rewriteOperator_rate (eq : P = Q) (d : RankOneSpectralData P one) :
    (d.rewriteOperator eq).rate = d.rate := by subst Q; rfl

@[simp] theorem rewriteOperator_mean (eq : P = Q) (d : RankOneSpectralData P one) :
    (d.rewriteOperator eq).mean = d.mean := by subst Q; rfl

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  {PX QX : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)}

@[simp] theorem rewriteOperator_eigenmeasure (eq : PX = QX)
    (d : RankOneSpectralData PX (1 : X →ᵇ ℝ))
    (hp : ∀ f : X →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ PX f x)
    (hq : ∀ f : X →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ QX f x) :
    (d.rewriteOperator eq).eigenmeasure hq = d.eigenmeasure hp := by subst QX; rfl
end RankOneSpectralData

namespace Global.LayerNormalizedGap
open LeanShared LayerQuasiErgodic
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (sf : HasStrongFellerKernel C)

omit [CompactSpace X] in
 theorem operator_eq : ComplexStrongFeller.transferOperator (𝕜 := ℝ) C sf =
    strongFellerTransferOperator C sf := by
  ext f x
  rw [ComplexStrongFeller.transferOperator_apply, strongFellerTransferOperator_represents]

/-- The exact probability already constructed by the global layer argument. -/
def probability
    (d : RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ) C sf)
      (1 : X →ᵇ ℝ)) : ProbabilityMeasure X :=
  ⟨productMeasure C sf d, (productMeasure_isQuasiErgodic C sf d).1⟩

@[simp] theorem probability_coe
    (d : RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ) C sf)
      (1 : X →ᵇ ℝ)) :
    ((probability C sf d : ProbabilityMeasure X) : Measure X) = productMeasure C sf d := rfl

/-- The produced prefix gap is precisely the local normalized gap on the
same eigenproduct probability. Only core positivity is passed through. -/
theorem normalizedGap
    (d : RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ) C sf)
      (1 : X →ᵇ ℝ))
    (core : Set X) (positive : ∀ x ∈ core, 0 < d.eigenvector x) :
    Paper.LocalConclusions.NormalizedGap C core (probability C sf d) := by
  refine ⟨sf, d.rewriteOperator (operator_eq C sf), ?_, ?_⟩
  · change productMeasure C sf d = _
    rw [RankOneSpectralData.rewriteOperator_eigenmeasure,
      RankOneSpectralData.rewriteOperator_vector]
    rfl
  · simpa only [RankOneSpectralData.rewriteOperator_vector] using positive

end Global.LayerNormalizedGap
end ConditionedStochasticStabilityHyperbolic
