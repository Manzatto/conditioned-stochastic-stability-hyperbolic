module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelUniformBounds
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedKL
public import LeanShared.Analysis.CompactCorePerturbation
public import LeanShared.Analysis.DenseCoreRandomOperators
public import LeanShared.Analysis.FiniteBlockAnnealedEstimates
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelLetterBlocks

/-! The Keller–Liverani record of a strong physical model `m`, with weak stage
given by a second model `n` and a compact intertwining inclusion `j`.
The generators are the model's operators at the (clipped) letters `G ε z`.

* D6: compactness of `j`, the uniform bound on `n`, the intertwining and
  core continuity at the reference letter give convergence of the mixed norm
  of the averaged operators, for arbitrary probability laws.
* D7: every field of `ActualAnnealedInputs`.
* D8: the all-length two-norm bound and the weak power bound of the averages. -/
@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory Filter Topology
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelAnnealedRecord
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelUniformBounds
open LeanShared.AnnealedOperatorBounds

section Abstract
variable {X Y Z₀ : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y] [MeasurableSpace Z₀]
  {law₀ : ℝ≥0 → Measure Z₀} {hprob₀ : ∀ ε, IsProbabilityMeasure (law₀ ε)}
  {i : X →L[ℂ] Y} {scale₀ : ℝ}

/-- Averaging preserves uniform convergence of mixed-norm letter differences. -/
theorem averaged_tendsto (law₀ : ℝ≥0 → Measure Z₀) (hprob₀ : ∀ ε, IsProbabilityMeasure (law₀ ε))
    (Aε : ℝ≥0 → Z₀ → X →L[ℂ] X) (hmeas : ∀ ε x, AEStronglyMeasurable (fun z => Aε ε z x) (law₀ ε))
    (L : ℝ) (hA : ∀ ε z, ‖Aε ε z‖ ≤ L) (i : X →L[ℂ] Y) (A₀ : X →L[ℂ] X)
    (hzero : ∀ z, Aε 0 z = A₀)
    (uniform : Tendsto (fun p : ℝ≥0 × Z₀ => ‖i.comp (Aε p.1 p.2 - A₀)‖) ((𝓝 0) ×ˢ ⊤) (𝓝 0)) :
    Tendsto (fun ε => ‖i.comp (KellerLiverani1999.varyingNoiseOperator law₀ hprob₀ Aε hmeas L hA ε -
      KellerLiverani1999.varyingNoiseOperator law₀ hprob₀ Aε hmeas L hA 0)‖) (𝓝 0) (𝓝 0) := by
  have zero : KellerLiverani1999.varyingNoiseOperator law₀ hprob₀ Aε hmeas L hA 0 = A₀ := by
    let _ := hprob₀ 0
    apply ContinuousLinearMap.ext
    intro x
    change ∫ z, Aε 0 z x ∂(law₀ 0) = _
    simp only [hzero, integral_const, probReal_univ, one_smul]
  rw [Metric.tendsto_nhds]
  intro ζ hζ
  have half := (Metric.tendsto_nhds.mp uniform) (ζ / 2) (by positivity)
  obtain ⟨pa, hpa, pb, hpb, hall⟩ := Filter.eventually_prod_iff.mp half
  filter_upwards [hpa] with ε hε
  let _ := hprob₀ ε
  have each : ∀ z x, ‖i ((Aε ε z - A₀) x)‖ ≤ ζ / 2 * ‖x‖ := by
    intro z x
    have hz := hall hε (Filter.eventually_top.mp hpb z)
    rw [dist_zero_right, norm_norm] at hz
    exact ((i.comp (Aε ε z - A₀)).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hz.le (norm_nonneg x))
  have bound := pointwiseAnnealed_weak_perturbation (law₀ ε) (Aε ε) (hmeas ε) L (hA ε) i A₀
    (ζ / 2) (by positivity) each
  rw [dist_zero_right, norm_norm, zero]
  exact bound.trans_lt (half_lt_self hζ)

/-- D8: every record yields the all-length two-norm bound and the weak power
bound for the averaged operators on its window. -/
theorem all_lengths (r : KellerLiverani1999.ActualAnnealedInputs law₀ hprob₀ i scale₀)
    (ε : ℝ≥0) (hε : ε ≤ r.window) :
    let C := ∑ k ∈ Finset.range r.blockLength, (r.operatorBound / r.principal) ^ k
    let D := r.remainder / (r.weakRate ^ r.blockLength - r.principal ^ r.blockLength)
    0 ≤ C ∧ 0 ≤ D ∧ (∀ n x, ‖(KellerLiverani1999.varyingNoiseOperator law₀ hprob₀ r.generator
        r.measurable r.operatorBound r.generator_bound ε ^ n) x‖ ≤
        C * r.principal ^ n * ‖x‖ + D * r.weakRate ^ n * ‖i x‖) ∧
      ∀ n x, ‖i ((KellerLiverani1999.varyingNoiseOperator law₀ hprob₀ r.generator
        r.measurable r.operatorBound r.generator_bound ε ^ n) x)‖ ≤ r.weakOneStep ^ n * ‖i x‖ := by
  let _ := hprob₀ ε
  have two := FiniteBlockAnnealedEstimates.annealed_twoNorm_bound (law₀ ε) (r.generator ε)
    (r.measurable ε) i r.blockLength r.blockLength_pos r.principal r.weakRate r.weakOneStep
    r.operatorBound r.remainder r.principal_pos r.principal_weak r.weakOneStep_nonneg
    r.weakOneStep_rate r.operatorBound_nonneg r.remainder_nonneg (r.generator_bound ε)
    (r.weak_bound ε hε) (r.block_bound ε hε)
  exact ⟨two.1, two.2.1, two.2.2, FiniteBlockAnnealedEstimates.annealed_weak_power_bound (law₀ ε)
    (r.generator ε) (r.measurable ε) r.operatorBound (r.generator_bound ε) i r.weakOneStep
    r.weakOneStep_nonneg (r.weak_bound ε hε)⟩

end Abstract

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
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m n : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
  [MetricSpace Ω] {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
  [OpensMeasurableSpace Z] [SecondCountableTopology Z]
  (law : ℝ≥0 → Measure Z) (hprob : ∀ ε, IsProbabilityMeasure (law ε))
  (j : m.StrongSpace →L[ℂ] n.StrongSpace) (compact : IsCompactOperator j)
  (compat : ∀ a x, j (m.generator a x) = n.generator a (j x))
  (Lm Ln : ℝ) (hLm : 0 ≤ Lm) (hLn : 0 ≤ Ln)
  (boundM : GeneratorBound m Lm) (boundN : GeneratorBound n Ln)
  (G : ℝ≥0 → Z → Ω) (a₀ : Ω) (G0 : ∀ z, G 0 z = a₀) (contG : ∀ ε, Continuous (G ε))
  (closeG : Tendsto (fun p : ℝ≥0 × Z => G p.1 p.2) ((𝓝 0) ×ˢ ⊤) (𝓝 a₀))
  (coreM : ∀ c, Continuous (fun a => m.generator a (coreLift m.qa c)))
  (coreN : ∀ c, Continuous (fun a => n.generator a (coreLift n.qa c)))

include contG coreM in
/-- Evaluated-vector measurability of the letter generators. -/
theorem measurable (ε : ℝ≥0) (x : m.StrongSpace) :
    AEStronglyMeasurable (fun z => m.generator (G ε z) x) (law ε) :=
  DenseCoreRandomOperators.aestronglyMeasurable_of_continuous_core (law ε)
    (fun z => m.generator (G ε z)) (coreLift m.qa) (coreLift_dense m.qa)
    (fun c => (coreM c).comp (contG ε)) x

include compact compat boundN closeG coreN hLn in
/-- D6 before averaging: the mixed norm of the letter difference tends to zero
uniformly in the control. -/
theorem uniform_tendsto :
    Tendsto (fun p : ℝ≥0 × Z => ‖j.comp (m.generator (G p.1 p.2) - m.generator a₀)‖)
      ((𝓝 0) ×ˢ ⊤) (𝓝 0) :=
  CompactCorePerturbation.mixed_norm_tendsto_of_compatible_core j compact j
    (fun p : ℝ≥0 × Z => n.generator (G p.1 p.2)) (n.generator a₀)
    (fun p : ℝ≥0 × Z => m.generator (G p.1 p.2)) (m.generator a₀)
    (fun _ => ContinuousLinearMap.ext fun x => (compat _ x).symm)
    (ContinuousLinearMap.ext fun x => (compat a₀ x).symm) _ Ln hLn
    (Eventually.of_forall fun _ => boundN _) (coreLift n.qa) (coreLift_dense n.qa)
    (fun c => ((coreN c).tendsto a₀).comp closeG)

include compact compat boundN closeG coreN hLn G0 in
/-- D6: the mixed norm of the averaged-operator difference tends to zero. -/
theorem perturbation :
    Tendsto (fun ε => ‖j.comp (KellerLiverani1999.varyingNoiseOperator law hprob
        (fun ε z => m.generator (G ε z)) (measurable m law G contG coreM) Lm
        (fun _ _ => boundM _) ε -
      KellerLiverani1999.varyingNoiseOperator law hprob
        (fun ε z => m.generator (G ε z)) (measurable m law G contG coreM) Lm
        (fun _ _ => boundM _) 0)‖) (𝓝 0) (𝓝 0) :=
  averaged_tendsto law hprob (fun ε z => m.generator (G ε z)) (measurable m law G contG coreM) Lm
    (fun _ _ => boundM _) j (m.generator a₀) (fun z => congrArg m.generator (G0 z))
    (uniform_tendsto m n j compact compat Ln hLn boundN G a₀ closeG coreN)

variable (η : ℝ≥0) (positiveη : 0 < η) (N : ℕ) (positiveN : 0 < N) (ρ B weakRate scale : ℝ)
  (positiveρ : 0 < ρ) (nonnegativeB : 0 ≤ B) (ρweak : ρ < weakRate) (weakLn : Ln ≤ weakRate)
  (scaleOne : 1 ≤ scale) (ρscale : ρ < scale)
  (block : ∀ ε ≤ η, ∀ word : List Z, word.length = N → ∀ x,
    ‖FiniteBlockAnnealedEstimates.listWord (fun z => m.generator (G ε z)) word x‖ ≤
      ρ ^ N * ‖x‖ + B * ‖j x‖)

set_option maxHeartbeats 1600000 in
include compact compat boundN closeG coreN G0 in
/-- D7: the Keller–Liverani record of the physical model with weak stage `n`. -/
def record : KellerLiverani1999.ActualAnnealedInputs law hprob j scale where
  generator ε z := m.generator (G ε z)
  measurable := measurable m law G contG coreM
  window := η
  window_pos := positiveη
  blockLength := N
  blockLength_pos := positiveN
  principal := ρ
  weakRate := weakRate
  weakOneStep := Ln
  operatorBound := Lm
  remainder := B
  principal_pos := positiveρ
  principal_weak := ρweak
  weakOneStep_nonneg := hLn
  weakOneStep_rate := weakLn
  operatorBound_nonneg := hLm
  remainder_nonneg := nonnegativeB
  scale_ge_one := scaleOne
  principal_scale := ρscale
  generator_bound _ _ := boundM _
  weak_bound ε _ z x := (congrArg norm (compat (G ε z) x)).trans_le
    (((n.generator (G ε z)).le_opNorm (j x)).trans
      (mul_le_mul_of_nonneg_right (boundN _) (norm_nonneg _)))
  block_bound := block
  perturbation := perturbation m n law hprob j compact compat Lm Ln hLn boundM boundN G a₀ G0 contG
    closeG coreM coreN

/-- The record statement used by concrete consumers: the inclusion is compact
and a Keller–Liverani record exists whose generators are `m.generator (G ε z)`. -/
def CarrierRecord (scale : ℝ) : Prop :=
  IsCompactOperator j ∧ ∃ r : KellerLiverani1999.ActualAnnealedInputs law hprob j scale,
    ∀ ε z, r.generator ε z = m.generator (G ε z)

include compact compat boundN closeG coreN G0 block hLm hLn boundM contG coreM positiveη positiveN
  positiveρ nonnegativeB ρweak weakLn scaleOne ρscale in
theorem carrierRecord : CarrierRecord m n law hprob j G scale :=
  ⟨compact, record m n law hprob j compact compat Lm Ln hLm hLn boundM boundN G a₀ G0 contG closeG
    coreM coreN η positiveη N positiveN ρ B weakRate scale positiveρ nonnegativeB ρweak weakLn
    scaleOne ρscale block, fun _ _ => rfl⟩

include compact compat boundN closeG coreN G0 hLm hLn boundM contG coreM positiveη positiveN
  positiveρ nonnegativeB ρweak weakLn scaleOne ρscale in
/-- The record from block bounds of literal letter words, through the clipped letters. -/
theorem carrierRecord_of_words (hj : ∀ x, ‖j x‖ = ‖m.inclusionW x‖) (Ctrl : ℝ≥0 → Type*)
    (letterF : ∀ ε : ℝ≥0, 0 < ε → ε ≤ η → Ctrl ε → Ω)
    (resc : ∀ ε : ℝ≥0, 0 < ε → Z → Ctrl ε) (zeroC : Ctrl η)
    (hG : ∀ ε hp hl z, G ε z = letterF ε hp hl (resc ε hp z))
    (hG0' : ∀ z, G 0 z = letterF η positiveη le_rfl zeroC)
    (words : ∀ ε hp hl (control : Fin N → Ctrl ε),
      WordBound m (List.ofFn fun k => letterF ε hp hl (control k)) (ρ ^ N) B) :
    CarrierRecord m n law hprob j G scale :=
  carrierRecord m n law hprob j compact compat Lm Ln hLm hLn boundM boundN G a₀ G0 contG closeG
    coreM coreN η positiveη N positiveN ρ B weakRate scale positiveρ nonnegativeB ρweak weakLn
    scaleOne ρscale (PhysicalModelLetterBlocks.block_of_words m j hj Ctrl η positiveη letterF resc
      zeroC G hG hG0' N ρ B words)

end ConditionedStochasticStabilityHyperbolic.PhysicalModelAnnealedRecord
