module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelPairBounds

/-! Uniform one-step bounds of a physical model: chart-pair estimates for
every letter, with a common cap on the strong coefficient and one common
weak remainder, give one uniform bound on every core action and hence on
every constructed generator. -/
@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelUniformBounds
open LeanShared DyadicCompletion CompletedChartPairTransfer FiniteRegularTransferRealization
open PhysicalManifoldModel PhysicalModelPairBounds

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
  (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)

/-- Chart-pair estimates for one map and weight with a given strong coefficient. -/
structure PairEstimate (Fw : M → M) (gw : M → ℝ) (strong : ℝ)
    (remainder : m.localization.indices → m.localization.indices → ℝ) : Prop where
  pairMember : ∀ i j (f : SchwartzJetSpace.supportedCore
      (ConstructedManifoldLocalization.support m.atlas m.localization j)),
    ChartPairTransfer.pair (m.atlas i) (m.atlas j) (m.localization.cutoff i) Fw gw f.val ∈
      (m.localView i).range
  bound : ∀ i j f,
    ‖localRealize m.atlas m.localization m.localCore m.localBlocks i
      (RegularChartPairTransfer.localPair m.atlas m.localization Fw gw
        m.localView m.localView_injective pairMember i j f)‖ ≤
      strong * ‖m.localBlocks j f‖ + remainder i j * ‖m.weakLocalBlocksW j f‖

/-- The uniform one-step constant. -/
def oneStepConstant (Smax : ℝ) (remainder : m.localization.indices → m.localization.indices → ℝ) : ℝ :=
  (Fintype.card m.localization.indices : ℝ) ^ 2 * Smax + ∑ i, ∑ j, remainder i j

theorem times_one (X Y Z s q : ℝ) (h : X ≤ s * Y + q * Z) : X ≤ (s * 1) * Y + q * Z := by
  rwa [mul_one]

theorem drop_one (X Y Q a s : ℝ) (h : X ≤ (a * s * 1) * Y + Q) : X ≤ (a * s) * Y + Q := by
  rwa [mul_one] at h

theorem le_combine (P P' Q Y : ℝ) (le : P ≤ P') (nonnegative : 0 ≤ Y) (X : ℝ)
    (bound : X ≤ (P + Q) * Y) : X ≤ (P' + Q) * Y :=
  bound.trans (mul_le_mul_of_nonneg_right (add_le_add_left le Q) nonnegative)

/-- D4: a uniform family of one-letter estimates bounds every core action uniformly. -/
theorem analytic_of_estimates (Smax : ℝ)
    (remainder : m.localization.indices → m.localization.indices → ℝ)
    (hR : ∀ i j, 0 ≤ remainder i j)
    (estimates : ∀ a, ∃ strong, 0 ≤ strong ∧ strong ≤ Smax ∧
      PairEstimate m (m.maps a) m.weight strong remainder) :
    ∀ a c, ‖targetCore m.qa (SmoothSupportedManifoldCore.functions V) Reg m.view
      m.view_injective m.realize m.maps m.weight m.coreRegular a c‖ ≤
      oneStepConstant m Smax remainder * ‖m.qa c‖ := by
  intro a c
  have e := estimates a
  have one := one_step_bound m a e.choose_spec.2.2.pairMember e.choose 1 e.choose_spec.1
    zero_le_one remainder hR
    (fun i j c => times_one _ _ _ _ _ (e.choose_spec.2.2.bound i j (localized m j c))) c
  refine le_combine _ _ _ _ ?_ (norm_nonneg _) _ one
  rw [mul_one]
  exact mul_le_mul_of_nonneg_left e.choose_spec.2.1 (sq_nonneg _)

theorem oneStepConstant_nonneg (Smax : ℝ) (hS : 0 ≤ Smax)
    (remainder : m.localization.indices → m.localization.indices → ℝ)
    (hR : ∀ i j, 0 ≤ remainder i j) : 0 ≤ oneStepConstant m Smax remainder :=
  add_nonneg (mul_nonneg (sq_nonneg _) hS)
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hR i j)

/-- D4: every constructed generator obeys the uniform one-step bound. -/
theorem generator_bound (Smax : ℝ) (hS : 0 ≤ Smax)
    (remainder : m.localization.indices → m.localization.indices → ℝ)
    (hR : ∀ i j, 0 ≤ remainder i j)
    (estimates : ∀ a, ∃ strong, 0 ≤ strong ∧ strong ≤ Smax ∧
      PairEstimate m (m.maps a) m.weight strong remainder) (a : Ω) :
    ‖m.generator a‖ ≤ oneStepConstant m Smax remainder :=
  operator_norm_le m.qa (SmoothSupportedManifoldCore.functions V) Reg m.view m.view_injective
    m.realize m.maps m.weight m.coreRegular _ (analytic_of_estimates m Smax remainder hR estimates)
    (oneStepConstant_nonneg m Smax hS remainder hR) a

/-- D5: a word estimate (with the uniform one-letter estimates) gives the
completed two-norm word bound for the constructed generators. -/
theorem word_bound_of_estimates (Smax : ℝ)
    (remainder : m.localization.indices → m.localization.indices → ℝ)
    (hR : ∀ i j, 0 ≤ remainder i j)
    (estimates : ∀ a, ∃ strong, 0 ≤ strong ∧ strong ≤ Smax ∧
      PairEstimate m (m.maps a) m.weight strong remainder)
    (w : List Ω) (strong : ℝ) (hstrong : 0 ≤ strong)
    (wordRemainder : m.localization.indices → m.localization.indices → ℝ)
    (hW : ∀ i j, 0 ≤ wordRemainder i j)
    (word : PairEstimate m (ActualFiniteRegularWord.orbit m.maps w)
      (ActualWordMicrolocalBound.realWeight m.maps m.weight w) strong wordRemainder)
    (x : m.StrongSpace) :
    ‖FiniteBlockAnnealedEstimates.listWord m.generator w x‖ ≤
      ((Fintype.card m.localization.indices : ℝ) ^ 2 * strong) * ‖x‖ +
        (∑ i, ∑ j, wordRemainder i j) * ‖m.inclusionW x‖ := by
  have main := PhysicalModelPairBounds.word_bound m (oneStepConstant m Smax remainder)
    (analytic_of_estimates m Smax remainder hR estimates) w word.pairMember strong 1 hstrong
    zero_le_one wordRemainder hW
    (fun i j c => times_one _ _ _ _ _ (word.bound i j (localized m j c))) x
  exact drop_one _ _ _ _ _ main

/-- A uniform strong bound on every constructed generator. -/
def GeneratorBound (L : ℝ) : Prop := ∀ a : Ω, ‖m.generator a‖ ≤ L

/-- The completed two-norm bound of one word of constructed generators. -/
def WordBound (w : List Ω) (α β : ℝ) : Prop :=
  ∀ x : m.StrongSpace, ‖FiniteBlockAnnealedEstimates.listWord m.generator w x‖ ≤
    α * ‖x‖ + β * ‖m.inclusionW x‖

theorem WordBound.mono {w : List Ω} {α α' β β' : ℝ} (bound : WordBound m w α β)
    (hα : α ≤ α') (hβ : β ≤ β') : WordBound m w α' β' := fun x =>
  (bound x).trans (add_le_add (mul_le_mul_of_nonneg_right hα (norm_nonneg _))
    (mul_le_mul_of_nonneg_right hβ (norm_nonneg _)))

/-- D5 in `WordBound` form. -/
theorem wordBound_of_estimates (Smax : ℝ)
    (remainder : m.localization.indices → m.localization.indices → ℝ)
    (hR : ∀ i j, 0 ≤ remainder i j)
    (estimates : ∀ a, ∃ strong, 0 ≤ strong ∧ strong ≤ Smax ∧
      PairEstimate m (m.maps a) m.weight strong remainder)
    (w : List Ω) (strong : ℝ) (hstrong : 0 ≤ strong)
    (wordRemainder : m.localization.indices → m.localization.indices → ℝ)
    (hW : ∀ i j, 0 ≤ wordRemainder i j)
    (word : PairEstimate m (ActualFiniteRegularWord.orbit m.maps w)
      (ActualWordMicrolocalBound.realWeight m.maps m.weight w) strong wordRemainder) :
    WordBound m w ((Fintype.card m.localization.indices : ℝ) ^ 2 * strong)
      (∑ i, ∑ j, wordRemainder i j) := fun x =>
  word_bound_of_estimates m Smax remainder hR estimates w strong hstrong wordRemainder hW word x

end ConditionedStochasticStabilityHyperbolic.PhysicalModelUniformBounds
