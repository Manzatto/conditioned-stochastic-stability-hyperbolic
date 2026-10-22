module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ComparedLocalQuasiErgodic
public import ConditionedStochasticStabilityHyperbolic.Spectral.InverseCollarDensityPositivity

/-! Core support for literal chain measures using an inverse positive collar. -/

@[expose] public noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.ComparedCollarSupport

open LeanShared LocalPositiveEigenfunction Restriction ComparedLocalQuasiErgodic
open LeanShared.ControlledPlaqueClosure

variable {X Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω]

theorem exists_noise_tolerance_for_inverse_collar_support_from_actual_data
    (T : X ≃ₜ X) (V K G U : Set X) [CompactSpace K]
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K)
    (hcoreV : isolatedCore T K ⊆ V) (hcoreG : isolatedCore T K ⊆ G)
    (htrans : forwardTransitiveOn T (isolatedCore T K)) (hUV : closure U ⊆ V)
    (hUG : closure U ⊆ G) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (noise : Measure Ω) [IsProbabilityMeasure noise] [noise.IsOpenPosMeasure]
      (F : X × Ω → X) (hF : Measurable F) (w : K → ℝ) (hw : Measurable w)
      (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R),
      let C := RestrictedNoise.chain noise F hF K hK.measurableSet w hw R hR hwR
      let J := LeanShared.WeightedConditioning.normalizedKernel
        (LeanShared.RandomMapKernel.killed noise F hF K hK.measurableSet)
        (SubtypeKernel.zeroExtend K w) R
        (SubtypeKernel.measurable_zeroExtend K hK.measurableSet w hw)
      ∀ (hSF : HasStrongFellerKernel C)
        (d : RankOneSpectralData (strongFellerTransferOperator C hSF) (1 : K →ᵇ ℝ))
        (ν : Measure K) [IsFiniteMeasure ν],
      (∀ f : K →ᵇ ℝ, d.mean f = ∫ y, f y ∂ν) →
      (eigenvectorMeasure ν d.eigenvector).support ⊆ retainedRegion K U →
      (∀ x : K, x.val ∈ isolatedCore T K → 0 < d.eigenvector x) →
      ∀ (H : X × Ω → X) (_hH : Measurable H),
      (∀ x ∈ K, ∀ ω, dist (H (x, ω)) (T.symm x) < δ) →
      LocalPositiveCollar.ForwardCollarPlaqueInputs T.symm H V K G →
      ∀ (Wnoise : X × Ω → ℝ) (_hWnoise : Measurable Wnoise) (B : ℝ),
      (∀ x ∈ K, ∀ ω, Wnoise (x, ω) ≤ B) →
      (∀ x ∈ K, x ∈ G → ∀ ω, 0 < Wnoise (x, ω)) →
      let L := LeanShared.WeightedRandomMapKernel.killed noise Wnoise H K hK.measurableSet
      ∀ (σ : Measure X) [IsFiniteMeasure σ] (m : X → ℝ),
      σ.support = K → Measurable m → (∀ x, 0 ≤ m x) → ContinuousOn m K →
      ν.map Subtype.val = eigenvectorMeasure σ m →
      LeanShared.KernelAdjointDensity.IsAdjoint J L σ →
      ContinuousOn (fun x => ∫ y, m y ∂L x) K →
      {x : K | x.val ∈ isolatedCore T K} ⊆ (eigenvectorMeasure ν d.eigenvector).support := by
  obtain ⟨δ, hδ, hcert⟩ := InverseCollarDensityPositivity.exists_noise_tolerance_for_collar_core_subset_product_support
    (Ω := Ω) T V K G hV hVK hK hcoreV hcoreG htrans
  refine ⟨δ, hδ, ?_⟩
  intro noise _ _ F hF w hw R hR hwR
  dsimp only
  intro hSF d ν _ hm hlocal hgpos H hH hclose hp Wnoise hWnoise B hB hWpos
    σ _ m hσ hmMeas hm0 hmc hrepr hdual hLmc
  let C := RestrictedNoise.chain noise F hF K hK.measurableSet w hw R hR hwR
  let J := LeanShared.WeightedConditioning.normalizedKernel
    (LeanShared.RandomMapKernel.killed noise F hF K hK.measurableSet)
    (SubtypeKernel.zeroExtend K w) R
    (SubtypeKernel.measurable_zeroExtend K hK.measurableSet w hw)
  let : IsFiniteKernel J := LeanShared.WeightedConditioning.normalizedKernel_isFinite
    _ _ R _ hR (SubtypeKernel.zeroExtend_le K w R hR.le hwR)
    (LeanShared.RandomMapKernel.killed_mass_le_one noise F hF K hK.measurableSet)
  let : IsFiniteKernel C.killedTransition := by
    change IsFiniteKernel C.toKilledKernel.kernel
    infer_instance
  let g := SubtypeKernel.zeroExtend K d.eigenvector
  have hgMeas : Measurable g :=
    SubtypeKernel.measurable_zeroExtend K hK.measurableSet _ d.eigenvector.continuous.measurable
  have hg0K : ∀ x : K, 0 ≤ d.eigenvector x :=
    d.eigenvector_nonneg_of_positive (representedTransfer_positive C.killedTransition
      (strongFellerTransferOperator C hSF) (strongFellerTransferOperator_represents C hSF))
  have hg0 : ∀ x, 0 ≤ g x := by
    intro x
    by_cases hx : x ∈ K
    · rw [show g x = d.eigenvector ⟨x, hx⟩ from SubtypeKernel.zeroExtend_coe K _ ⟨x, hx⟩]
      exact hg0K ⟨x, hx⟩
    · rw [show g x = 0 from SubtypeKernel.zeroExtend_of_not_mem K _ x hx]
  have hgcont : ContinuousOn g K := continuousOn_zeroExtend K d.eigenvector
  have hrightK (x : K) : ∫ y, d.eigenvector y ∂C.killedTransition x =
      d.rate * d.eigenvector x := by
    rw [← strongFellerTransferOperator_represents C hSF]
    simpa only [BoundedContinuousFunction.smul_apply, smul_eq_mul] using
      congrArg (fun f : K →ᵇ ℝ => f x) d.right_eigenvector
  have hright : ∀ x ∈ K, ∫ y, g y ∂J x = d.rate * g x := by
    intro x hx
    change ∫ y, SubtypeKernel.zeroExtend K d.eigenvector y ∂J x =
      d.rate * SubtypeKernel.zeroExtend K d.eigenvector x
    rw [SubtypeKernel.zeroExtend_coe K d.eigenvector ⟨x, hx⟩]
    exact ambient_right_law noise F hF K hK.measurableSet w hw R hR hwR
        d.eigenvector d.rate hrightK ⟨x, hx⟩
  have hleftK := rankOne_left_eigenmeasure d C.killedTransition
    (strongFellerTransferOperator_represents C hSF) ν hm
  have hleft : J ∘ₘ eigenvectorMeasure σ m = ENNReal.ofReal d.rate • eigenvectorMeasure σ m := by
    rw [← hrepr]
    exact map_left_eigenmeasure C.killedTransition J Subtype.val measurable_subtype_coe
      (map_live_killedTransition noise F hF K hK.measurableSet w hw R hR hwR) ν _ hleftK
  have hnorm : ∫ x, g x ∂eigenvectorMeasure σ m = 1 := by
    rw [← hrepr, integral_zeroExtend_map K hK.measurableSet, ← hm, d.mean_eigenvector]
  have hproduct : eigenvectorMeasure (eigenvectorMeasure σ m) g =
      (eigenvectorMeasure ν d.eigenvector).map Subtype.val := by
    rw [← hrepr]
    exact (map_eigenvectorMeasure_zeroExtend K hK.measurableSet ν d.eigenvector
      d.eigenvector.continuous.measurable).symm
  have hlocalAmbient : (eigenvectorMeasure (eigenvectorMeasure σ m) g).support ⊆ V ∩ G := by
    rw [hproduct]
    exact ambient_product_localization K U (V ∩ G) (fun x hx => ⟨hUV hx, hUG hx⟩) ν d.eigenvector hlocal
  have hJtarget : ∀ x ∈ K, (J x).restrict K = J x := by
    intro x _
    change (ENNReal.ofReal (SubtypeKernel.zeroExtend K w x / R) •
      ((LeanShared.RandomMapKernel.transition noise F hF x).restrict K)).restrict K = _
    rw [Measure.restrict_smul, Measure.restrict_restrict hK.measurableSet, inter_self]
    rfl
  have hcorepos : ∀ x ∈ isolatedCore T K, 0 < g x := by
    intro x hx
    have hxK : x ∈ K := forwardTrapped_subset T K hx.1
    rw [show g x = d.eigenvector ⟨x, hxK⟩ from SubtypeKernel.zeroExtend_coe K _ ⟨x, hxK⟩]
    exact hgpos ⟨x, hxK⟩ hx
  have hsupp := hcert noise H hH hclose hp Wnoise hWnoise B hB hWpos
    J σ hσ hJtarget hdual g m hgMeas hmMeas hg0 hm0 hgcont hmc hLmc d.rate d.rate_pos
    hleft hright hnorm hlocalAmbient hcorepos
  intro x hx
  apply mem_support_of_mem_support_map K _ x
  rw [← hproduct]
  exact hsupp hx

end ConditionedStochasticStabilityHyperbolic.ComparedCollarSupport
