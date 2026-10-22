module

public import ConditionedStochasticStabilityHyperbolic.Global.ActualFiltrationSelectedQuasiErgodic
public import ConditionedStochasticStabilityHyperbolic.Global.PrefixClosedRawSource
public import ConditionedStochasticStabilityHyperbolic.Global.PrefixReferenceNullity
public import ConditionedStochasticStabilityHyperbolic.Global.PrefixUniqueness

/-! # The actual HG2 selected-prefix QEM from finite pressure sources

Only strata below the selected prefix contribute. The ambient map remains a
homeomorphism of the manifold; no homeomorphism of the trapping prefix is
assumed. Actual closed-local data and both killed aggregates construct the
prefix gap, full-process QEM, exact physical product and measurable limits.
-/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.ActualSelectedPrefixQuasiErgodic
open LeanShared ShiftedFiltrationGeometry ShiftedBoundaryGeometry FiltrationPressureConfinement ActualFiltrationGrowth
open ActualPrefixSubordinateAggregates KilledAbsorbingBaseGrowth ComplexStrongFeller RestrictedLayerChain NestedLayerKernel
open RawClosedSelectedQuasiErgodic LayerQuasiErgodic PrefixClosedRawSource LiveClosedLayerMeasure
open PrefixQuasiErgodic PrefixCorrespondence PrefixUniqueness
variable {X I : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

omit [CompactSpace X] in
private theorem power_norm_congr (C : AbsorbingMarkovChains.CanonicalChain X)
    (hSF : HasStrongFellerKernel C) (U V : Set X) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (h : U = V) (b : ℝ) (n : ℕ) :
    ‖(b • transferOperator (𝕜 := ℝ) (chain C U hU) (strongFeller C hSF U hU))^n‖ =
      ‖(b • transferOperator (𝕜 := ℝ) (chain C V hV) (strongFeller C hSF V hV))^n‖ := by subst V; rfl

omit [CompactSpace X] in
theorem exists_actual_selected_prefix_QEM
    (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ N : ℕ)
    (D : AdaptedSource T A Λ ℓ) (k : ℕ) (hkℓ : k ≤ ℓ) (j : Fin ℓ) (hjk : j.val < k)
    (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
    (hzeroA : ∀ x, C.killedTransition x A = 0)
    (hnoUp : ∀ i, i ≤ k → ∀ x ∈ levels T A Λ ℓ N D i,
      C.killedTransition x (levels T A Λ ℓ N D i)ᶜ = 0)
    (R : ℝ) (hR : 0 < R)
    (d : RankOneSpectralData (R • transferOperator (𝕜 := ℝ)
      (chain C (closedLayer T A Λ ℓ N D j) (closedLayer_measurable T A Λ ℓ N D j))
      (strongFeller C hSF (closedLayer T A Λ ℓ N D j) (closedLayer_measurable T A Λ ℓ N D j)))
      (1 : closedLayer T A Λ ℓ N D j →ᵇ ℝ))
    {β : ℝ} (hβ : 0 < β) (hβd : β < d.rate)
    (hleaf : ∀ i : Fin ℓ, i.val < k → i ≠ j → ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      ‖(R • transferOperator (𝕜 := ℝ)
        (chain C (stratum T A Λ ℓ N D i) (stratum_measurable T A Λ ℓ N D hA i))
        (strongFeller C hSF (stratum T A Λ ℓ N D i)
          (stratum_measurable T A Λ ℓ N D hA i))) ^ n‖ ≤ B * β^n)
    (σ : Measure X) (q : X × X → ENNReal)
    (hdensity : ∀ x, C.killedTransition x = σ.withDensity (fun y => q (x, y)))
    (hpre : ∀ S : Set X, σ S = 0 → σ (T ⁻¹' S) = 0)
    (hnull : ∀ i, 0 < i → i ≤ ℓ → σ (frontier (D.levels i)) = 0)
    (μ : Measure (closedLayer T A Λ ℓ N D j)) [IsFiniteMeasure μ]
    (hmean : ∀ f : closedLayer T A Λ ℓ N D j →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ)
    (hΛ : (Λ (D.index j)).Nonempty)
    (hpos : ∀ x : closedLayer T A Λ ℓ N D j, x.val ∈ Λ (D.index j) → 0 < d.eigenvector x)
    (hsupport : {x : closedLayer T A Λ ℓ N D j | x.val ∈ Λ (D.index j)} ⊆
      (eigenvectorMeasure μ d.eigenvector).support) :
    let V := levels T A Λ ℓ N D k
    letI : CompactSpace V := isCompact_iff_compactSpace.mp
      (levels_positive_compact T A Λ ℓ N D k (by omega) hkℓ)
    let hV := ambient_levels_measurable T A hA Λ ℓ N D k
    let CP := chain C V hV
    let sfP := strongFeller C hSF V hV
    ∃ dg : RankOneSpectralData (transferOperator (𝕜 := ℝ) CP sfP) (1 : V →ᵇ ℝ),
      dg.rate = R⁻¹ * d.rate ∧
      C.IsQuasiErgodic ((productMeasure CP sfP dg).map Subtype.val) ∧
      (productMeasure CP sfP dg).map Subtype.val = (eigenvectorMeasure μ d.eigenvector).map Subtype.val ∧
      Λ (D.index j) ⊆ ((productMeasure CP sfP dg).map Subtype.val).support ∧
      (∀ η : Measure X, C.IsQuasiErgodic η → Λ (D.index j) ⊆ η.support →
        η = (productMeasure CP sfP dg).map Subtype.val) ∧
      (∀ x : V, x.val ∈ Λ (D.index j) → 0 < dg.eigenvector x) ∧
      ∀ f : X → ℝ, Measurable f → (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) → ∀ x : V,
        0 < dg.eigenvector x → Tendsto (MeasurableCanonical.pathAverage C f x.val) atTop
          (𝓝 (∫ y, f y ∂(productMeasure CP sfP dg).map Subtype.val)) := by
  dsimp only
  let M := levels T A Λ ℓ N D
  let V := M k
  have hV := ambient_levels_measurable T A hA Λ ℓ N D k
  let CP := chain C V hV
  let sfP := strongFeller C hSF V hV
  let L0 := M j.val
  let L1 := M (j.val + 1)
  have hL0 := ambient_levels_measurable T A hA Λ ℓ N D j.val
  have hL1 := ambient_levels_measurable T A hA Λ ℓ N D (j.val + 1)
  let S := L1 \ L0
  have hS : MeasurableSet S := hL1.diff hL0
  have hVcompact : IsCompact V := levels_positive_compact T A Λ ℓ N D k (by omega) hkℓ
  let : CompactSpace V := isCompact_iff_compactSpace.mp hVcompact
  have hKV : closure S ⊆ V := closure_minimal
    (fun x hx => levels_monotone T A Λ ℓ N D (by omega : j.val + 1 ≤ k) hx.1) hVcompact.isClosed
  have hSV : S ⊆ V := subset_closure.trans hKV
  let B0 := innerLevel L0 V
  let B1 := innerLevel L1 V
  have hB0 : MeasurableSet B0 := hL0.preimage measurable_subtype_coe
  have hB1 : MeasurableSet B1 := hL1.preimage measurable_subtype_coe
  let Sp := B1 \ B0
  have hSp : MeasurableSet Sp := hB1.diff hB0
  let dp := actualPrefixData C hSF S V hV hKV R hR d
  have hμfinite : IsFiniteMeasure μ := inferInstance
  let μ0 : Measure (closure S : Set X) := μ
  let : IsFiniteMeasure μ0 := hμfinite
  let μp : Measure (closure Sp) := liveClosedMeasure S V hKV μ0
  let : IsFiniteMeasure μp := liveClosedMeasure_finite S V hKV μ0
  have hmP : ∀ f : closure Sp →ᵇ ℝ, dp.mean f = ∫ y, f y ∂μp :=
    actualPrefixData_represents C hSF S V hV hKV R hR d μ hmean
  have hrateP : dp.rate = d.rate := actualPrefixData_rate C hSF S V hV hKV R hR d
  have hzeroP : ∀ x : closure Sp,
      (chain CP (closure Sp) isClosed_closure.measurableSet).killedTransition x
        (innerLevel Sp (closure Sp))ᶜ = 0 :=
    PrefixReferenceNullity.actual_prefix_closed_complement_zero C S V hS hV hSV σ q hdensity
      (closed_layer_extra_zero T A hA Λ ℓ N D σ hpre hnull j)
  obtain ⟨γ, CA, CD, hγ, hγd, hCA, hCD, hpowA, hpowD⟩ :=
    exists_actual_prefix_two_subordinate_bounds T A hA Λ ℓ N D k hkℓ j hjk C hSF R hβ hβd
      (fun i _ hi => hnoUp i hi) hleaf
  obtain ⟨CA', hCA', hpowA'⟩ := exists_prefix_bound_of_live_interval_bound C hSF A L0
    hA.measurableSet hL0 hzeroA R hCA hγ hpowA
  have hsmallA : ∀ n : ℕ, ‖(R • transferOperator (𝕜 := ℝ) (chain CP B0 hB0)
      (strongFeller CP sfP B0 hB0))^n‖ ≤ CA' * γ^n := by
    intro n
    exact (nested_power_norm_eq (𝕜 := ℝ) L0 V
      (levels_monotone T A Λ ℓ N D (by omega)) C hSF hL0 hV R n).trans_le (hpowA' n)
  let G := V \ L1
  have hG : MeasurableSet G := hV.diff hL1
  have hupperEq : innerLevel G V = B1ᶜ := by
    ext x
    exact ⟨fun h => h.2, fun h => ⟨x.property, h⟩⟩
  have hsmallD : ∀ n : ℕ, ‖(R • transferOperator (𝕜 := ℝ) (chain CP B1ᶜ hB1.compl)
      (strongFeller CP sfP B1ᶜ hB1.compl))^n‖ ≤ CD * γ^n := by
    intro n
    have he := power_norm_congr CP sfP (innerLevel G V) B1ᶜ
      (hG.preimage measurable_subtype_coe) hB1.compl hupperEq R n
    exact he.symm.trans_le ((nested_power_norm_eq (𝕜 := ℝ) G V sdiff_subset C hSF hG hV R n).trans_le (hpowD n))
  have hs0 : ∀ x ∈ B0, CP.killedTransition x B0ᶜ = 0 := by
    intro x hx
    exact ae_iff.mp (LiteralFiltrationGrowth.restricted_level_support C L0 V hL0 hV
      (hnoUp j.val (by omega)) x hx)
  have hs1 : ∀ x ∈ B1, ∀ᵐ y ∂CP.killedTransition x, y ∈ B1 :=
    LiteralFiltrationGrowth.restricted_level_support C L1 V hL1 hV (hnoUp (j.val + 1) (by omega))
  have hg0 : ∀ x, 0 ≤ dp.eigenvector x := dp.eigenvector_nonneg_of_positive (by
    intro f hf x
    change 0 ≤ R * transferOperator (𝕜 := ℝ) (chain CP (closure Sp) isClosed_closure.measurableSet)
      (strongFeller CP sfP (closure Sp) isClosed_closure.measurableSet) f x
    exact mul_nonneg hR.le (integral_nonneg hf))
  let Core : Set Sp := {x | x.val.val ∈ Λ (D.index j)}
  have hcoreS : Λ (D.index j) ⊆ S := by
    rw [← literal_core T A Λ ℓ N D j]
    exact fun _ hx => hx.1 0
  have hCore : Core.Nonempty := by
    obtain ⟨x, hx⟩ := hΛ
    exact ⟨⟨⟨x, hSV (hcoreS hx)⟩, hcoreS hx⟩, hx⟩
  have hCorePos : ∀ p ∈ Core, 0 < dp.eigenvector ⟨p.val, subset_closure p.property⟩ := by
    intro p hp
    let q : closure S := ⟨p.val.val, subset_closure p.property⟩
    have he : liveClosedPoint S V hKV q = ⟨p.val, subset_closure p.property⟩ := by
      apply Subtype.ext; apply Subtype.ext; rfl
    rw [← he, actualPrefixData_vector C hSF S V hV hKV R hR d q]
    exact hpos q hp
  have hCoreSupport : ∀ p ∈ Core,
      (⟨p.val, subset_closure p.property⟩ : closure Sp) ∈ (eigenvectorMeasure μp dp.eigenvector).support := by
    intro p hp
    let q : closure S := ⟨p.val.val, subset_closure p.property⟩
    have he : liveClosedPoint S V hKV q = ⟨p.val, subset_closure p.property⟩ := by
      apply Subtype.ext; apply Subtype.ext; rfl
    change (⟨p.val, subset_closure p.property⟩ : closure (innerLevel S V)) ∈
      (eigenvectorMeasure μp dp.eigenvector).support
    rw [← he]
    exact actualPrefixData_core_support C hSF S V hV hKV R hR d μ0 q (hsupport hp)
  obtain ⟨dg, hrate, hq, hprod, _hsupportP, _huniqueP, hv, _hlimP⟩ :=
    exists_selected_QEM_from_raw_closed_local CP sfP B0 B1 hB0 hB1
      (fun x hx => levels_monotone T A Λ ℓ N D (Nat.le_succ _) hx)
      hs0 hs1 hzeroP R hR dp hCA' hCD hγ.le hγ.le
      (hγd.trans_eq hrateP.symm) (hγd.trans_eq hrateP.symm) hsmallA hsmallD μp hmP hg0 Core hCore hCorePos hCoreSupport
  have hprefix : ∀ x ∈ V, C.killedTransition x Vᶜ = 0 := hnoUp k le_rfl
  have hqFull := full_process_isQuasiErgodic_of_prefix C V hV hprefix _ hq
  have hprodFull : (productMeasure CP sfP dg).map Subtype.val =
      (eigenvectorMeasure μ d.eigenvector).map Subtype.val := by
    rw [hprod, Measure.map_map measurable_subtype_coe measurable_subtype_coe]
    exact actualPrefixData_product_map C hSF S V hV hKV R hR d μ
  have hCorePositive : ∀ x : V, x.val ∈ Λ (D.index j) → 0 < dg.eigenvector x := by
    intro x hx
    let p : Sp := ⟨x, hcoreS hx⟩
    rw [hv p]
    exact mul_pos (inv_pos.mpr (mul_pos (inv_pos.mpr hR) dp.rate_pos)) (hCorePos p hx)
  have hCoreInterior : Λ (D.index j) ⊆ interior V := by
    intro x hx
    have hc : x ∈ isolatedCore T S := (literal_core T A Λ ℓ N D j).symm ▸ hx
    have hp := levels_positive_adapted T A Λ ℓ N D k (by omega) hkℓ
      (levels_monotone T A Λ ℓ N D (by omega : j.val + 1 ≤ k) (hc.2 1).1)
    simpa only [iterate_one, T.apply_symm_apply] using hp
  have hfullsupport : Λ (D.index j) ⊆ ((productMeasure CP sfP dg).map Subtype.val).support := by
    rw [hprodFull]
    intro x hx
    exact LayerProductCorrespondence.subtype_support_maps_into _
      (hsupport (show (⟨x, subset_closure (hcoreS hx)⟩ : closure S).val ∈ Λ (D.index j) from hx))
  refine ⟨dg, hrate.trans (congrArg (fun t => R⁻¹ * t) hrateP), hqFull, hprodFull, hfullsupport, ?_, hCorePositive, ?_⟩
  · intro η hη hsupp
    obtain ⟨x, hx⟩ := hΛ
    let p : V := ⟨x, hSV (hcoreS hx)⟩
    exact full_QEM_eq_prefix_product_of_support C hSF V hV hprefix dg η hη p (hsupp hx)
      (hCoreInterior hx) (hCorePositive p hx)
  · intro f hf hb x hx
    exact full_process_limit_from_prefix C V hV hprefix sfP dg f hf hb x hx

end ConditionedStochasticStabilityHyperbolic.Global.ActualSelectedPrefixQuasiErgodic
