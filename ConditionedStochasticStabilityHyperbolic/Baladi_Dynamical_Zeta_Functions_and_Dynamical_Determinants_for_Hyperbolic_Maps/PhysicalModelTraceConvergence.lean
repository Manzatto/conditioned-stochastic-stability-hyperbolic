module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelTraceFamily
public import LeanShared.Analysis.TraceFamilySmoothing
public import LeanShared.Analysis.MollifierKernel
meta import Lean.LibrarySuggestions.Basic

/-! Convergence of the regularized trace smoothings. On core functions the smoothing is the
chart sum of `P L` applied to `cut_k · (κ ⋆ G_k(v))`, while `P L v` is the chart sum of
`P L G_k(v)` by the partition identity. The local differences are `O(ε)` and the smoothings
are uniformly bounded, so they converge strongly to `P L` on the whole strong space. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelTraceConvergence"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory Filter
open scoped Manifold ContDiff SchwartzMap Topology
attribute [local instance] Classical.propDecidable
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelBumpVectors
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelUniformBounds
  PhysicalModelAnalytic SchwartzJetSpace PhysicalModelFullTestPairing PhysicalModelLocalHolderTest

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
  (tc : TraceCharts m) {bt : ℝ} (hbt : 0 < bt) (hbt1 : bt ≤ 1)
  (lc : LocalCalculus m) (localBound : LocalPairing m bt) {L : ℝ} (bound : AnalyticBound m L)
  (a : Ω) (strong : ℝ) (remainder : m.localization.indices → m.localization.indices → ℝ)
  (hs : 0 ≤ strong) (hR : ∀ i j, 0 ≤ remainder i j)
  (estimate : PairEstimate m (m.maps a) m.weight strong remainder)
  {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
  (P : m.StrongSpace →L[ℂ] m.StrongSpace)

/-- One generator step after the zero extension of chart `k`. -/
abbrev chartStep (k : Fin (Fintype.card m.localization.indices)) :
    supportedCore (tsupport (tc.cut (chartEquiv m k) : E → ℂ)) →ₗ[ℂ] m.StrongSpace :=
  (m.generator a).toLinearMap.comp ((coreLift m.qa).comp (extension m (chartEquiv m k)
    (tc.cut (chartEquiv m k)) (tc.cutCompact (chartEquiv m k)) (tc.cutSupport (chartEquiv m k))
    (tc.cutRegion (chartEquiv m k))))

theorem smoothing_core (ρ : 𝓢(E, ℂ)) (ρc : HasCompactSupport (ρ : E → ℂ)) (ρ' : 𝓢(E, ℂ))
    (ρ'c : HasCompactSupport (ρ' : E → ℂ)) (v : Core (E := E) V) :
    (family m tc hbt hbt1 ρ ρc lc localBound bound a strong remainder hs hR estimate b P ρ'
      ρ'c).smoothing (coreLift m.qa v) =
      ∑ k, P (chartStep m tc a k (smoothed m tc hbt hbt1 ρ ρc localBound ρ' ρ'c k v)) :=
  (ChartTraceFamily.smoothing_apply' volume _ _ _ _ _ (coreLift m.qa v)).trans
    (Finset.sum_congr rfl fun k _ => chart_smoothing m tc hbt hbt1 ρ ρc lc localBound bound a
      strong remainder hs hR estimate b P ρ' ρ'c k v)

include bound in
theorem target_core
    (partition : ∀ x, m.weight x ≠ 0 → (∑ j : m.localization.indices,
      if m.maps a x ∈ (m.atlas j).source then
        tc.wt j (m.atlas j (m.maps a x)) * m.localization.cutoff j (m.maps a x) else 0) = 1)
    (v : Core (E := E) V) :
    P (m.generator a (coreLift m.qa v)) =
      ∑ k, P (chartStep m tc a k (weighted m (chartEquiv m k) (tc.cut (chartEquiv m k))
        (tc.wt (chartEquiv m k)) (tc.wtOne (chartEquiv m k)) v)) :=
  (congrArg P (partition_decomposition m tc bound a partition v)).trans
    ((TraceFamilySmoothing.clm_lin_sum P ((m.generator a).toLinearMap.comp (coreLift m.qa))
      (fun j => extension m j (tc.cut j) (tc.cutCompact j) (tc.cutSupport j) (tc.cutRegion j)
        (weighted m j (tc.cut j) (tc.wt j) (tc.wtOne j) v))).trans
      (Equiv.sum_comp (chartEquiv m) (fun j => P (((m.generator a).toLinearMap.comp
        (coreLift m.qa)) (extension m j (tc.cut j) (tc.cutCompact j) (tc.cutSupport j)
          (tc.cutRegion j) (weighted m j (tc.cut j) (tc.wt j) (tc.wtOne j) v))))).symm)

set_option maxHeartbeats 1600000 in
include lc b in
/-- The local difference between the smoothed and the exact chart pieces is `O(r + r')`. -/
theorem chart_difference (k : Fin (Fintype.card m.localization.indices)) (v : Core (E := E) V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : 𝓢(E, ℂ)) (ρc : HasCompactSupport (ρ : E → ℂ)) (ρ' : 𝓢(E, ℂ))
      (ρ'c : HasCompactSupport (ρ' : E → ℂ)) (r r' : ℝ)
      (_ : ∀ s, r < ‖s‖ → ρ s = 0) (_ : ∀ s, r' < ‖s‖ → ρ' s = 0) (_ : r + r' ≤ 1)
      (_ : ∫ s, ρ s = 1) (_ : ∫ s, ρ' s = 1) (_ : ∫ s, ‖ρ s‖ ≤ 1) (_ : ∫ s, ‖ρ' s‖ ≤ 1),
      ‖coreLift (cutBlocks m (chartEquiv m k) (tc.cut (chartEquiv m k))
        (tc.cutCompact (chartEquiv m k)) lc)
          (smoothed m tc hbt hbt1 ρ ρc localBound ρ' ρ'c k v -
            weighted m (chartEquiv m k) (tc.cut (chartEquiv m k)) (tc.wt (chartEquiv m k))
              (tc.wtOne (chartEquiv m k)) v)‖ ≤ C * (r + r') := by
  have : ∀ c, SFinite ((m.leaves (chartEquiv m k) c).measure μ) := lc.sfinite _
  have h := BlockNormCalculus.cutoff_convolution_estimates μ m.slope_nonnegative
    (m.leaves (chartEquiv m k)) (ConeDyadicSymbols.symbols (m.radial (chartEquiv m k))
      (m.angle (chartEquiv m k))) (m.exponent (chartEquiv m k)) (lc.translate _) (lc.bounded _)
    (tc.cut (chartEquiv m k)) (fun K hK => lc.multiplier _ _ K hK) b (tc.cutCompact (chartEquiv m k))
    (weighted m (chartEquiv m k) (tc.cut (chartEquiv m k)) (tc.wt (chartEquiv m k))
      (tc.wtOne (chartEquiv m k)) v)
    (fun x hx => tc.wtOne _ x (weighted_tsupport m _ _ _ _ v hx))
  refine ⟨h.choose, h.choose_spec.1, fun ρ ρc ρ' ρ'c r r' supp supp' small mass mass' l1 l1' => ?_⟩
  have C0 := h.choose_spec.1
  have est := h.choose_spec.2
  have κcont := MollifierKernel.continuous ρ ρ' ρ.continuous ρc ρ'.continuous ρ'c
  have κcs := MollifierKernel.hasCompactSupport ρ ρ' supp supp'
  have κmass : ∫ y, MollifierKernel.kernel ρ ρ' y = 1 := by
    rw [MollifierKernel.integral ρ ρ' ρ.continuous ρc ρ'.continuous ρ'c, mass, mass', one_mul]
  have κl1 : ∫ y, ‖MollifierKernel.kernel ρ ρ' y‖ ≤ 1 :=
    (MollifierKernel.norm_integral_le ρ ρ' ρ.continuous ρc ρ'.continuous ρ'c).trans
      (by
        have h0 : 0 ≤ ∫ s, ‖ρ' s‖ := integral_nonneg fun _ => norm_nonneg _
        have h1 : 0 ≤ ∫ s, ‖ρ s‖ := integral_nonneg fun _ => norm_nonneg _
        nlinarith)
  have bound2 := (est (MollifierKernel.kernel ρ ρ') κcont (κcont.integrable_of_hasCompactSupport κcs)
    κmass (r + r') small (fun y hy => MollifierKernel.zero_outside ρ ρ' supp supp' y hy)
    (smoothed m tc hbt hbt1 ρ ρc localBound ρ' ρ'c k v)
    (fun x => smoothed_apply m _ _ (tc.cutCompact _) _ (tc.wtOne _) hbt hbt1 localBound ρ _
      (testFamily_apply m tc hbt hbt1 ρ ρc _) ρ' ρc ρ'c v _ x)).2
  have rr0 : 0 ≤ r + r' := by
    by_contra neg
    push Not at neg
    have zero : ∀ y, MollifierKernel.kernel ρ ρ' y = 0 := fun y =>
      MollifierKernel.zero_outside ρ ρ' supp supp' y (neg.trans_le (norm_nonneg y))
    simp [zero] at κmass
  calc _ ≤ h.choose * (r + r') * ∫ y, ‖MollifierKernel.kernel ρ ρ' y‖ := bound2
    _ ≤ h.choose * (r + r') * 1 := mul_le_mul_of_nonneg_left κl1 (mul_nonneg C0 rr0)
    _ = h.choose * (r + r') := mul_one _

set_option maxHeartbeats 1600000 in
include lc in
/-- The weighted chart pieces are bounded by the strong norm. -/
theorem weighted_bound (k : Fin (Fintype.card m.localization.indices)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Core (E := E) V,
      ‖coreLift (cutBlocks m (chartEquiv m k) (tc.cut (chartEquiv m k))
        (tc.cutCompact (chartEquiv m k)) lc)
          (weighted m (chartEquiv m k) (tc.cut (chartEquiv m k)) (tc.wt (chartEquiv m k))
            (tc.wtOne (chartEquiv m k)) v)‖ ≤ C * ‖coreLift m.qa v‖ := by
  have h := lc.multiplier (chartEquiv m k) (tc.wt (chartEquiv m k))
    (ConstructedManifoldLocalization.support m.atlas m.localization (chartEquiv m k))
    (ConstructedManifoldLocalization.support_compact m.atlas m.localization (chartEquiv m k))
  refine ⟨max h.choose 0, le_max_right _ _, fun v => ?_⟩
  have mult := h.choose_spec (ConstructedManifoldLocalization.localize m.atlas m.localization
      m.atlas_mem (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
      (chartEquiv m k) v)
    (inclusion m (chartEquiv m k) (tc.cut (chartEquiv m k)) (tc.cutSupport (chartEquiv m k))
      (weighted m (chartEquiv m k) (tc.cut (chartEquiv m k)) (tc.wt (chartEquiv m k))
        (tc.wtOne (chartEquiv m k)) v)) rfl
  have core := local_le_core m v (chartEquiv m k)
  calc _ = ‖m.localBlocks (chartEquiv m k) (inclusion m (chartEquiv m k) (tc.cut (chartEquiv m k))
        (tc.cutSupport (chartEquiv m k)) (weighted m (chartEquiv m k) (tc.cut (chartEquiv m k))
          (tc.wt (chartEquiv m k)) (tc.wtOne (chartEquiv m k)) v))‖ :=
        (cutBlocks_norm m _ _ (tc.cutCompact _) (tc.cutSupport _) lc _).symm
    _ ≤ h.choose * ‖m.localBlocks (chartEquiv m k) (ConstructedManifoldLocalization.localize
        m.atlas m.localization m.atlas_mem (SmoothSupportedManifoldCore.functions V)
        (SmoothSupportedManifoldCore.smooth V) (chartEquiv m k) v)‖ := mult
    _ ≤ max h.choose 0 * ‖coreLift m.qa v‖ :=
        mul_le_mul (le_max_left _ _) core (norm_nonneg _) (le_max_right _ _)

set_option maxHeartbeats 1600000 in
include lc b in
/-- The smoothed chart pieces are uniformly bounded by the strong norm. -/
theorem chart_uniform (k : Fin (Fintype.card m.localization.indices)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : 𝓢(E, ℂ)) (ρc : HasCompactSupport (ρ : E → ℂ)) (ρ' : 𝓢(E, ℂ))
      (ρ'c : HasCompactSupport (ρ' : E → ℂ)) (r r' : ℝ)
      (_ : ∀ s, r < ‖s‖ → ρ s = 0) (_ : ∀ s, r' < ‖s‖ → ρ' s = 0) (_ : r + r' ≤ 1)
      (_ : ∫ s, ‖ρ s‖ ≤ 1) (_ : ∫ s, ‖ρ' s‖ ≤ 1) (v : Core (E := E) V),
      ‖coreLift (cutBlocks m (chartEquiv m k) (tc.cut (chartEquiv m k))
        (tc.cutCompact (chartEquiv m k)) lc)
          (smoothed m tc hbt hbt1 ρ ρc localBound ρ' ρ'c k v)‖ ≤ C * ‖coreLift m.qa v‖ := by
  have : ∀ c, SFinite ((m.leaves (chartEquiv m k) c).measure μ) := lc.sfinite _
  have hU := BlockNormCalculus.cutoff_convolution_uniform μ m.slope_nonnegative
    (m.leaves (chartEquiv m k)) (ConeDyadicSymbols.symbols (m.radial (chartEquiv m k))
      (m.angle (chartEquiv m k))) (m.exponent (chartEquiv m k)) (lc.translate _) (lc.bounded _)
    (tc.cut (chartEquiv m k)) (fun K hK => lc.multiplier _ _ K hK) (tc.cutCompact (chartEquiv m k))
  have hW := weighted_bound m tc lc k
  refine ⟨hU.choose * hW.choose, mul_nonneg hU.choose_spec.1 hW.choose_spec.1,
    fun ρ ρc ρ' ρ'c r r' supp supp' small l1 l1' v => ?_⟩
  have κcont := MollifierKernel.continuous ρ ρ' ρ.continuous ρc ρ'.continuous ρ'c
  have κcs := MollifierKernel.hasCompactSupport ρ ρ' supp supp'
  have κl1 : ∫ y, ‖MollifierKernel.kernel ρ ρ' y‖ ≤ 1 :=
    (MollifierKernel.norm_integral_le ρ ρ' ρ.continuous ρc ρ'.continuous ρ'c).trans (by
      have h0 : 0 ≤ ∫ s, ‖ρ' s‖ := integral_nonneg fun _ => norm_nonneg _
      have h1 : 0 ≤ ∫ s, ‖ρ s‖ := integral_nonneg fun _ => norm_nonneg _
      nlinarith)
  have unif := hU.choose_spec.2 (weighted m (chartEquiv m k) (tc.cut (chartEquiv m k))
      (tc.wt (chartEquiv m k)) (tc.wtOne (chartEquiv m k)) v) (MollifierKernel.kernel ρ ρ') κcont
    (κcont.integrable_of_hasCompactSupport κcs) (r + r') small
    (fun y hy => MollifierKernel.zero_outside ρ ρ' supp supp' y hy)
    (smoothed m tc hbt hbt1 ρ ρc localBound ρ' ρ'c k v)
    (fun x => smoothed_apply m _ _ (tc.cutCompact _) _ (tc.wtOne _) hbt hbt1 localBound ρ _
      (testFamily_apply m tc hbt hbt1 ρ ρc _) ρ' ρc ρ'c v _ x)
  have wb := hW.choose_spec.2 v
  have U0 := hU.choose_spec.1
  calc _ ≤ hU.choose * (∫ y, ‖MollifierKernel.kernel ρ ρ' y‖) *
        ‖coreLift (cutBlocks m (chartEquiv m k) (tc.cut (chartEquiv m k))
          (tc.cutCompact (chartEquiv m k)) lc) (weighted m (chartEquiv m k) (tc.cut (chartEquiv m k))
            (tc.wt (chartEquiv m k)) (tc.wtOne (chartEquiv m k)) v)‖ := unif
    _ ≤ hU.choose * 1 * (hW.choose * ‖coreLift m.qa v‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_left κl1 U0) wb (norm_nonneg _) (by positivity)
    _ = hU.choose * hW.choose * ‖coreLift m.qa v‖ := by ring

set_option maxHeartbeats 3200000 in
/-- The regularized trace smoothings converge strongly to `P L`. -/
theorem smoothing_tendsto
    (partition : ∀ x, m.weight x ≠ 0 → (∑ j : m.localization.indices,
      if m.maps a x ∈ (m.atlas j).source then
        tc.wt j (m.atlas j (m.maps a x)) * m.localization.cutoff j (m.maps a x) else 0) = 1)
    (ρs ρs' : ℕ → 𝓢(E, ℂ)) (ρc : ∀ n, HasCompactSupport (ρs n : E → ℂ))
    (ρ'c : ∀ n, HasCompactSupport (ρs' n : E → ℂ)) (r r' : ℕ → ℝ)
    (supp : ∀ n s, r n < ‖s‖ → ρs n s = 0) (supp' : ∀ n s, r' n < ‖s‖ → ρs' n s = 0)
    (small : ∀ n, r n + r' n ≤ 1) (hr : Tendsto (fun n => r n + r' n) atTop (𝓝 0))
    (mass : ∀ n, ∫ s, ρs n s = 1) (mass' : ∀ n, ∫ s, ρs' n s = 1)
    (l1 : ∀ n, ∫ s, ‖ρs n s‖ ≤ 1) (l1' : ∀ n, ∫ s, ‖ρs' n s‖ ≤ 1) (z : m.StrongSpace) :
    Tendsto (fun n => (family m tc hbt hbt1 (ρs n) (ρc n) lc localBound bound a strong remainder
      hs hR estimate b P (ρs' n) (ρ'c n)).smoothing z) atTop (𝓝 (P (m.generator a z))) := by
  let K : Fin (Fintype.card m.localization.indices) → ℝ := fun k =>
    strong + ∑ i, remainder i (chartEquiv m k)
  have hΛ : ∀ k h, ‖chartStep m tc a k h‖ ≤ K k * ‖coreLift (cutBlocks m (chartEquiv m k)
      (tc.cut (chartEquiv m k)) (tc.cutCompact (chartEquiv m k)) lc) h‖ := fun k h =>
    chart_bound m (chartEquiv m k) (tc.cut (chartEquiv m k)) (tc.cutCompact (chartEquiv m k))
      (tc.cutSupport (chartEquiv m k)) (tc.cutRegion (chartEquiv m k)) lc bound a strong remainder
      hs hR estimate h
  let cu : Fin (Fintype.card m.localization.indices) → ℝ := fun k =>
    (chart_uniform m tc hbt hbt1 lc localBound b k).choose
  let Ctot := ‖P‖ * ∑ k, |K k| * |cu k|
  have bound' : ∀ n, ‖(family m tc hbt hbt1 (ρs n) (ρc n) lc localBound bound a strong remainder
      hs hR estimate b P (ρs' n) (ρ'c n)).smoothingCLM‖ ≤ Ctot := fun n =>
    TraceFamilySmoothing.opNorm_le_of_dense _ (coreLift m.qa) (coreLift_dense m.qa) Ctot
      (mul_nonneg P.opNorm_nonneg (Finset.sum_nonneg fun _ _ => by positivity)) fun v =>
      (congrArg norm (smoothing_core m tc hbt hbt1 lc localBound bound a strong remainder hs hR
        estimate b P (ρs n) (ρc n) (ρs' n) (ρ'c n) v)).trans_le
      (TraceFamilySmoothing.sum_bound P (chartStep m tc a) (fun k => coreLift (cutBlocks m
        (chartEquiv m k) (tc.cut (chartEquiv m k)) (tc.cutCompact (chartEquiv m k)) lc)) K hΛ
        (fun k => smoothed m tc hbt hbt1 (ρs n) (ρc n) localBound (ρs' n) (ρ'c n) k v) cu
        ‖coreLift m.qa v‖ (fun k => (chart_uniform m tc hbt hbt1 lc localBound b k).choose_spec.2
          (ρs n) (ρc n) (ρs' n) (ρ'c n) (r n) (r' n) (supp n) (supp' n) (small n) (l1 n) (l1' n) v)
        (norm_nonneg _))
  have conv : ∀ d ∈ Set.range (coreLift m.qa), Tendsto (fun n => (family m tc hbt hbt1 (ρs n)
      (ρc n) lc localBound bound a strong remainder hs hR estimate b P (ρs' n) (ρ'c n)).smoothingCLM d)
      atTop (𝓝 ((P.comp (m.generator a)) d)) := by
    rintro _ ⟨v, rfl⟩
    have h := TraceFamilySmoothing.sum_tendsto P (chartStep m tc a) (fun k => coreLift (cutBlocks m
      (chartEquiv m k) (tc.cut (chartEquiv m k)) (tc.cutCompact (chartEquiv m k)) lc)) K hΛ
      (fun n k => smoothed m tc hbt hbt1 (ρs n) (ρc n) localBound (ρs' n) (ρ'c n) k v)
      (fun k => weighted m (chartEquiv m k) (tc.cut (chartEquiv m k)) (tc.wt (chartEquiv m k))
        (tc.wtOne (chartEquiv m k)) v)
      (fun k => (chart_difference m tc hbt hbt1 lc localBound b k v).choose) (fun n => r n + r' n) hr
      (fun n k => (chart_difference m tc hbt hbt1 lc localBound b k v).choose_spec.2 (ρs n) (ρc n)
        (ρs' n) (ρ'c n) (r n) (r' n) (supp n) (supp' n) (small n) (mass n) (mass' n) (l1 n) (l1' n))
    have target := target_core m tc bound a P partition v
    have h' := h.congr fun n => (smoothing_core m tc hbt hbt1 lc localBound bound a strong remainder hs
      hR estimate b P (ρs n) (ρc n) (ρs' n) (ρ'c n) v).symm
    rw [← target] at h'
    exact h'
  exact DenseUniformConvergence.tendsto _ (P.comp (m.generator a)) Ctot bound'
    (coreLift_dense m.qa) conv z

end ConditionedStochasticStabilityHyperbolic.PhysicalModelBumpVectors
