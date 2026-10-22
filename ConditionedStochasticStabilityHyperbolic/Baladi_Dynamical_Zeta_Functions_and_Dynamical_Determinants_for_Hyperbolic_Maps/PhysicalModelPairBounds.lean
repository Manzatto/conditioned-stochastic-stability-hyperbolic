module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldModel
public import LeanShared.Geometry.CompletedManifoldWordEstimate

/-! Local chart-pair estimates for a physical model give its global
estimates: a pair bound for one literal map gives the one-step strong
bound of the corresponding core action, and pair bounds for the literal
chronological word give the completed two-norm word bound for the
constructed generators. The weak norm is the model's own weak inclusion. -/
@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelPairBounds
open LeanShared DyadicCompletion CompletedChartPairTransfer FiniteRegularTransferRealization
open PhysicalManifoldModel

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

/-- Localized smooth inputs of the model. -/
abbrev localized (j : m.localization.indices) :=
  ConstructedManifoldLocalization.localize m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) j

/-- The weak local block never exceeds the strong one: its dyadic weights are at most one. -/
theorem weak_le (i : m.localization.indices) (f) :
    ‖m.weakLocalBlocksW i f‖ ≤ ‖m.localBlocks i f‖ := by
  change ‖(DyadicCompletion.exactInclusion (m.localBlocks i) (m.lossW i) (m.lossW_positive i)
    (m.extraW i) (m.extraW_nonnegative i) (DyadicCompletion.coreLift (m.localBlocks i) f)).val‖ ≤ _
  refine lp.norm_le_of_forall_le (norm_nonneg _) (fun j => ?_)
  rw [DyadicCompletion.exactInclusion_apply, DyadicCompletion.coe_coreLift, norm_smul]
  have small : ‖((((2 : ℝ) ^ (-(m.lossW i + m.extraW i j.2) * j.1) : ℝ) : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have := m.lossW_positive i
    have := m.extraW_nonnegative i j.2
    have : (0 : ℝ) ≤ j.1 := Nat.cast_nonneg _
    nlinarith
  calc _ ≤ 1 * ‖m.localBlocks i f j‖ :=
        mul_le_mul_of_nonneg_right small (norm_nonneg _)
    _ ≤ ‖m.localBlocks i f‖ := by
        rw [one_mul]
        exact lp.norm_apply_le_norm ENNReal.top_ne_zero _ j

/-- The weak input vector of every core element is bounded by its strong core vector. -/
theorem weakCore_le (c : Core (E := E) V) :
    ‖CompletedMicrolocalEstimate.weakCore m.atlas m.localization m.atlas_mem
      (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
      m.weakLocalBlocksW c‖ ≤ ‖m.qa c‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun j => ?_)
  exact (weak_le m j _).trans (norm_le_pi_norm (m.qa c) j)

include m in
theorem modelZero (c : Core (E := E) V) (x : M) (hx : x ∉ S) :
    SmoothSupportedManifoldCore.functions V c x = 0 :=
  SmoothSupportedManifoldCore.zero_outside V c x (fun h => hx (m.region_subset_support h))

/-- The literal one-step core action as the single-map global action. -/
theorem regularAction_eq (a : Ω) (c : Core (E := E) V) :
    regularAction (SmoothSupportedManifoldCore.functions V) Reg m.view m.view_injective
      m.maps m.weight m.coreRegular a c =
    RegularChartPairTransfer.globalAction (SmoothSupportedManifoldCore.functions V)
      m.view m.view_injective (m.maps a) m.weight (m.coreRegular a) c := by
  apply m.view_injective
  funext x
  rw [regularAction_apply]
  exact (regularAction_apply (SmoothSupportedManifoldCore.functions V) Reg m.view
    m.view_injective (fun _ : Unit => m.maps a) m.weight (fun _ => m.coreRegular a) () c x).symm

theorem combine (X Y Y' Z P Q : ℝ) (bound : X ≤ P * Y' + Q * Z) (same : Y' = Y)
    (weak : Z ≤ Y) (nonnegative : 0 ≤ Q) : X ≤ (P + Q) * Y := by
  subst same
  nlinarith

/-- D4 core: a chart-pair bound for one literal map gives the one-step
strong bound of its core action. -/
theorem one_step_bound (a : Ω)
    (pairMember : ∀ i j (f : SchwartzJetSpace.supportedCore
        (ConstructedManifoldLocalization.support m.atlas m.localization j)),
      ChartPairTransfer.pair (m.atlas i) (m.atlas j) (m.localization.cutoff i)
        (m.maps a) m.weight f.val ∈ (m.localView i).range)
    (C cost : ℝ) (hC : 0 ≤ C) (hcost : 0 ≤ cost)
    (remainder : m.localization.indices → m.localization.indices → ℝ)
    (hR : ∀ i j, 0 ≤ remainder i j)
    (pairBound : ∀ i j c,
      ‖localRealize m.atlas m.localization m.localCore m.localBlocks i
        (RegularChartPairTransfer.localPair m.atlas m.localization (m.maps a) m.weight
          m.localView m.localView_injective pairMember i j (localized m j c))‖ ≤
        (C * cost) * ‖m.localBlocks j (localized m j c)‖ +
        remainder i j * ‖m.weakLocalBlocksW j (localized m j c)‖)
    (c : Core (E := E) V) :
    ‖targetCore m.qa (SmoothSupportedManifoldCore.functions V) Reg m.view m.view_injective
      m.realize m.maps m.weight m.coreRegular a c‖ ≤
      ((Fintype.card m.localization.indices : ℝ) ^ 2 * C * cost +
        ∑ i, ∑ j, remainder i j) * ‖m.qa c‖ := by
  have main := CompletedMicrolocalEstimate.weighted_core_bound m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    m.view m.regularCore m.regularCore_dense m.view_core m.evaluate m.evaluation
    m.localView m.localView_injective m.localCore m.localCore_dense m.localView_core
    m.localEvaluate m.localEvaluation m.coordinateConstant m.coordinateBound
    m.localBlocks m.blockConstant m.blockBound (modelZero m) m.view_injective
    (m.maps a) m.weight (m.coreRegular a) pairMember m.weakLocalBlocksW
    C cost hC hcost remainder hR pairBound c
  have liftNorm : ‖DyadicCompletion.coreLift m.qa c‖ = ‖m.qa c‖ := rfl
  have sumNonneg : 0 ≤ ∑ i, ∑ j, remainder i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hR i j
  have same : targetCore m.qa (SmoothSupportedManifoldCore.functions V) Reg m.view
      m.view_injective m.realize m.maps m.weight m.coreRegular a c =
      m.realize (RegularChartPairTransfer.globalAction (SmoothSupportedManifoldCore.functions V)
        m.view m.view_injective (m.maps a) m.weight (m.coreRegular a) c) :=
    congrArg m.realize (regularAction_eq m a c)
  exact combine _ _ _ _ _ _ ((congrArg norm same).trans_le main) liftNorm (weakCore_le m c) sumNonneg

/-- The model's weak inclusion, viewed in the product of local weak blocks. -/
abbrev weakVector : m.StrongSpace →L[ℂ] (∀ i : m.localization.indices,
    DyadicCompletion.closedCore (DyadicCompletion.finalCore (m.localBlocks i) (m.lossW i)
      (m.lossW_positive i) (m.extraW i) (m.extraW_nonnegative i))) :=
  (DyadicCompletion.closedCore (ManifoldCompactEmbedding.weakCore m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) μ
    m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks m.lossW_positive
    m.extraW m.extraW_nonnegative)).subtypeL.comp m.inclusionW

theorem weakVector_core (c : Core (E := E) V) :
    weakVector m (DyadicCompletion.coreLift m.qa c) =
      CompletedMicrolocalEstimate.weakCore m.atlas m.localization m.atlas_mem
        (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
        m.weakLocalBlocksW c :=
  congrArg Subtype.val (ManifoldCompactEmbedding.embedding_core m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) μ
    m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks m.lossW_positive
    m.extraW m.extraW_nonnegative c)

theorem weakVector_norm (x : m.StrongSpace) : ‖weakVector m x‖ = ‖m.inclusionW x‖ := rfl

/-- D5 core: chart-pair bounds for the literal chronological word give the
completed two-norm bound for the word of constructed generators. -/
theorem word_bound (L : ℝ)
    (analyticBound : ∀ a c, ‖targetCore m.qa (SmoothSupportedManifoldCore.functions V) Reg m.view
      m.view_injective m.realize m.maps m.weight m.coreRegular a c‖ ≤ L * ‖m.qa c‖)
    (w : List Ω)
    (pairMember : ∀ i j (f : SchwartzJetSpace.supportedCore
        (ConstructedManifoldLocalization.support m.atlas m.localization j)),
      ChartPairTransfer.pair (m.atlas i) (m.atlas j) (m.localization.cutoff i)
        (ActualFiniteRegularWord.orbit m.maps w) (ActualWordMicrolocalBound.realWeight m.maps m.weight w)
        f.val ∈ (m.localView i).range)
    (C cost : ℝ) (hC : 0 ≤ C) (hcost : 0 ≤ cost)
    (remainder : m.localization.indices → m.localization.indices → ℝ)
    (hR : ∀ i j, 0 ≤ remainder i j)
    (pairBound : ∀ i j c,
      ‖localRealize m.atlas m.localization m.localCore m.localBlocks i
        (RegularChartPairTransfer.localPair m.atlas m.localization
          (ActualFiniteRegularWord.orbit m.maps w) (ActualWordMicrolocalBound.realWeight m.maps m.weight w)
          m.localView m.localView_injective pairMember i j (localized m j c))‖ ≤
        (C * cost) * ‖m.localBlocks j (localized m j c)‖ +
        remainder i j * ‖m.weakLocalBlocksW j (localized m j c)‖)
    (x : m.StrongSpace) :
    ‖FiniteBlockAnnealedEstimates.listWord m.generator w x‖ ≤
      ((Fintype.card m.localization.indices : ℝ) ^ 2 * C * cost) * ‖x‖ +
        (∑ i, ∑ j, remainder i j) * ‖m.inclusionW x‖ := by
  have core := fun c => CompletedManifoldWordEstimate.word_core_bound m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    m.view m.regularCore m.regularCore_dense m.view_core m.evaluate m.evaluation
    m.localView m.localView_injective m.localCore m.localCore_dense m.localView_core
    m.localEvaluate m.localEvaluation m.coordinateConstant m.coordinateBound
    m.localBlocks m.blockConstant m.blockBound (modelZero m) m.view_injective
    m.maps m.weight m.invariant m.coreRegular m.regularConstant m.regularBound L analyticBound
    m.weakLocalBlocksW w pairMember C cost hC hcost remainder hR pairBound c
  exact CompletedManifoldWordEstimate.completed_word_bound m.qa m.generator (weakVector m)
    (CompletedMicrolocalEstimate.weakCore m.atlas m.localization m.atlas_mem
      (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
      m.weakLocalBlocksW) (weakVector_core m) w _ _ core x

end ConditionedStochasticStabilityHyperbolic.PhysicalModelPairBounds
