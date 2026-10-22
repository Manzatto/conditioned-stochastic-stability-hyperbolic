module
public import ConditionedStochasticStabilityHyperbolic.Paper.ProductNoiseBoundaryNull
public import ConditionedStochasticStabilityHyperbolic.Spectral.RestrictedNoiseNull
public import ConditionedStochasticStabilityHyperbolic.Global.NormalizedConullLocalQuasiErgodic
public import ConditionedStochasticStabilityHyperbolic.Global.LiteralNoiseLiveChain

/-! A generated original selected closed-layer gap gives the literal-stratum
QEM for the same probability. Boundary deletion is derived from ordinary
PRODUCT volume, so no original endpoint/reference source is needed. -/
public noncomputable section
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.ProductSelectedStratumQuasiErgodic
open LeanShared RegularNoise Global
variable {EP X Y ι κ : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [MetricSpace X] [MetricSpace Y] [ChartedSpace EP (X × Y)]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y] [BorelSpace (X × Y)]
  [Fintype ι] [Fintype κ]
  {TP : (X × Y) ≃ₜ (X × Y)} {r : ℝ}

omit [BorelSpace Y] in
 theorem identify
    (P : Maps (E := EP) (ι := ι ⊕ κ) TP r)
    (L : Laws (ι := ι)) (L' : Laws (ι := κ)) (σ : Measure (X × Y))
    (source : ControlSubmersionSources (E := EP) (ι := ι ⊕ κ) σ)
    (ε : ℝ≥0) (positive : 0 < ε) (window : ε ≤ P.window)
    (F : X × cube (ι := ι) ε → X) (G : Y × cube (ι := κ) ε → Y)
    (hF : Measurable F) (hG : Measurable G)
    (independent : ∀ (a : cube (ι := ι ⊕ κ) ε) (z : X × Y),
      P.family ε a.val z =
        (F (z.1, (NoiseCubeRescaling.splitCube (ε : ℝ) a).1),
         G (z.2, (NoiseCubeRescaling.splitCube (ε : ℝ) a).2)))
    (Live K U : Set X) [CompactSpace K]
    (hLive : MeasurableSet Live) (hK : MeasurableSet K) (hU : MeasurableSet U)
    (hKLive : K ⊆ Live) (hUK : U ⊆ K)
    (null : σ ((K \ U) ×ˢ (univ : Set Y)) = 0) (y : Y)
    (w : X → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (bound : ∀ x, w x ≤ R)
    (C : AbsorbingMarkovChains.CanonicalChain X) (sf : HasStrongFellerKernel C)
    (actual : C = NoiseKernel.chain (L.law ε) F hF Live hLive w hw R hR bound)
    (core : Set X) (nonempty : core.Nonempty) (coreU : core ⊆ U)
    (ν : ProbabilityMeasure K)
    (gap : LocalConclusions.NormalizedGap
      (RestrictedNoise.chain (L.law ε) F hF K hK (fun x => w x.val)
        (hw.comp measurable_subtype_coe) R hR (fun x => bound x.val))
      {x : K | x.val ∈ core} ν)
    (support : {x : K | x.val ∈ core} ⊆ (ν : Measure K).support) :
    ∃ νU : ProbabilityMeasure U,
      (νU : Measure U).map Subtype.val = (ν : Measure K).map Subtype.val ∧
      (RestrictedLayerChain.chain C U hU).IsQuasiErgodic (νU : Measure U) ∧
      {x : U | x.val ∈ core} ⊆ (νU : Measure U).support ∧
      ∀ ζ : Measure U, (RestrictedLayerChain.chain C U hU).IsQuasiErgodic ζ →
        {x : U | x.val ∈ core} ⊆ ζ.support → ζ = (νU : Measure U) := by
  have localEq := LiteralNoiseLiveChain.actual_local_chain_eq_global_restriction
    (L.law ε) F hF Live K hLive hK hKLive w hw R hR bound
  have rows : ∀ x, (RestrictedNoise.chain (L.law ε) F hF K hK (fun x => w x.val)
        (hw.comp measurable_subtype_coe) R hR (fun x => bound x.val)).killedTransition x
      (NestedLayerKernel.innerLevel U K)ᶜ = 0 := by
    intro x
    have zero := RestrictedNoise.row_null_of_noise_null (L.law ε) F hF K hK
      (fun x => w x.val) (hw.comp measurable_subtype_coe) R hR (fun x => bound x.val)
      (K \ U) (hK.diff hU) x
      (original_row_null_of_product P L L' σ source ε positive window F G hF hG
        independent (K \ U) (hK.diff hU) null y x.val)
    have same : (NestedLayerKernel.innerLevel U K)ᶜ =
        Subtype.val ⁻¹' (K \ U) := by
      ext z
      change (¬z.val ∈ U) ↔ z.val ∈ K ∧ z.val ∉ U
      exact ⟨fun h => ⟨z.property, h⟩, fun h => h.2⟩
    rwa [same]
  rw [localEq, ← actual] at gap rows
  exact NormalizedConullLocalQuasiErgodic.exists_direct_stratum_QEM C sf U K hUK hU hK
    rows core nonempty coreU ν gap support
end ConditionedStochasticStabilityHyperbolic.Paper.ProductSelectedStratumQuasiErgodic
