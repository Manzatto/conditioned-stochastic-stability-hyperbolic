module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldLoweringTower
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldLoweredInclusion

/-! Literal physical weaker exponents identify the canonical weak completion
with a fresh physical anisotropic model. This supplies the norm equality
needed to apply the analytic producer at a second admissible exponent pair. -/

public noncomputable section
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff SchwartzMap BigOperators
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
open LeanShared DyadicCompletion CompletedChartPairTransfer FiniteRegularTransferRealization

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]

namespace Data

variable {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)

variable (a b : m.localization.indices → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
  (ea eb : m.localization.indices → Bool → ℝ)
  (hea : ∀ i j, 0 ≤ ea i j) (heb : ∀ i j, 0 ≤ eb i j)

@[expose] def towerEquivalence :
    closedCore ((m.intermediateModel a b ha hb ea eb hea heb).loweredCore b hb eb heb) ≃ₗᵢ[ℂ]
      closedCore (m.loweredCore (fun i => a i + b i) (fun i => add_pos (ha i) (hb i))
        (fun i j => ea i j + eb i j) (fun i j => add_nonneg (hea i j) (heb i j))) :=
  NormCompletionEquivalence.equivalence _ _ (fun c =>
    congrArg (fun q => ‖q c‖) (m.double_lowering_core a b ha hb ea eb hea heb))

@[expose] def towerSecondInclusion :
    closedCore (m.loweredCore a ha ea hea) →L[ℂ]
      closedCore (m.loweredCore (fun i => a i + b i) (fun i => add_pos (ha i) (hb i))
        (fun i j => ea i j + eb i j) (fun i j => add_nonneg (hea i j) (heb i j))) :=
  (m.towerEquivalence a b ha hb ea eb hea heb).toLinearIsometry.toContinuousLinearMap.comp
    ((m.intermediateModel a b ha hb ea eb hea heb).loweredInclusion b hb eb heb)

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ i, CompleteSpace (LocalReg i)] in
set_option maxHeartbeats 800000 in
private theorem towerSecondInclusion_core (c : Core (E := E) V) :
    m.towerSecondInclusion a b ha hb ea eb hea heb (coreLift (m.loweredCore a ha ea hea) c) =
      coreLift (m.loweredCore (fun i => a i + b i) (fun i => add_pos (ha i) (hb i))
        (fun i j => ea i j + eb i j) (fun i j => add_nonneg (hea i j) (heb i j))) c := by
  have h := (m.intermediateModel a b ha hb ea eb hea heb).loweredInclusion_core b hb eb heb c
  exact (congrArg (m.towerEquivalence a b ha hb ea eb hea heb) h).trans
    (NormCompletionEquivalence.equivalence_core _ _ _ c)

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ i, CompleteSpace (LocalReg i)] in
set_option maxHeartbeats 800000 in
private theorem tower_inclusions_comp :
    (m.towerSecondInclusion a b ha hb ea eb hea heb).comp (m.loweredInclusion a ha ea hea) =
      m.loweredInclusion (fun i => a i + b i) (fun i => add_pos (ha i) (hb i))
        (fun i j => ea i j + eb i j) (fun i j => add_nonneg (hea i j) (heb i j)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply (coreLift_dense m.qa).induction_on
    (p := fun x => m.towerSecondInclusion a b ha hb ea eb hea heb
      (m.loweredInclusion a ha ea hea x) =
        m.loweredInclusion (fun i => a i + b i) (fun i => add_pos (ha i) (hb i))
          (fun i j => ea i j + eb i j) (fun i j => add_nonneg (hea i j) (heb i j)) x) x
    (isClosed_eq ((m.towerSecondInclusion a b ha hb ea eb hea heb).continuous.comp
      (m.loweredInclusion a ha ea hea).continuous) (ContinuousLinearMap.continuous _))
  intro c
  exact (congrArg (m.towerSecondInclusion a b ha hb ea eb hea heb)
    (m.loweredInclusion_core a ha ea hea c)).trans
      ((towerSecondInclusion_core m a b ha hb ea eb hea heb c).trans
        (m.loweredInclusion_core (fun i => a i + b i) (fun i => add_pos (ha i) (hb i))
          (fun i j => ea i j + eb i j) (fun i j => add_nonneg (hea i j) (heb i j)) c).symm)

structure CompatibleInclusions {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (i : X →L[ℂ] Y) (j : Y →L[ℂ] Z) (k : X →L[ℂ] Z) : Type where
  composition : j.comp i = k

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ i, CompleteSpace (LocalReg i)] in
def inclusionTower : CompatibleInclusions (m.loweredInclusion a ha ea hea)
    (m.towerSecondInclusion a b ha hb ea eb hea heb)
    (m.loweredInclusion (fun i => a i + b i) (fun i => add_pos (ha i) (hb i))
      (fun i j => ea i j + eb i j) (fun i j => add_nonneg (hea i j) (heb i j))) :=
  ⟨tower_inclusions_comp m a b ha hb ea eb hea heb⟩

end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
