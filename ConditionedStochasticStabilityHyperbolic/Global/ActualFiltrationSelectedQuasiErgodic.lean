module

public import ConditionedStochasticStabilityHyperbolic.Global.ActualPrefixSubordinateAggregates
public import ConditionedStochasticStabilityHyperbolic.Global.KilledAbsorbingBaseGrowth
public import ConditionedStochasticStabilityHyperbolic.Global.RawClosedSelectedQuasiErgodic

/-! # The actual finite-pressure filtration constructs the global selected QEM

The actual ambient process keeps its fixed absorbing base. Actual stratum
bounds produce both subordinate aggregates; transition density and proved
boundary nullity produce conull dominant restriction; the actual produced
closed-local source then constructs the global gap and physical probability.
No global gap, actual-stratum gap, global QEM or recursive certificate is input.
-/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.ActualFiltrationSelectedQuasiErgodic
open LeanShared ShiftedFiltrationGeometry ShiftedBoundaryGeometry FiltrationPressureConfinement
open ActualFiltrationGrowth ActualPrefixSubordinateAggregates KilledAbsorbingBaseGrowth
open ComplexStrongFeller RestrictedLayerChain NestedLayerKernel ClosedLayerReference
open RawClosedSelectedQuasiErgodic LayerQuasiErgodic
variable {X I : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

omit [CompactSpace X] in
private theorem power_norm_congr (C : AbsorbingMarkovChains.CanonicalChain X)
    (hSF : HasStrongFellerKernel C) (U V : Set X) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (h : U = V) (b : ℝ) (n : ℕ) :
    ‖(b • transferOperator (𝕜 := ℝ) (chain C U hU) (strongFeller C hSF U hU))^n‖ =
      ‖(b • transferOperator (𝕜 := ℝ) (chain C V hV) (strongFeller C hSF V hV))^n‖ := by
  subst V
  rfl

theorem exists_actual_global_selected_QEM
    (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ N : ℕ)
    (D : AdaptedSource T A Λ ℓ) (j : Fin ℓ)
    (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
    (hzeroA : ∀ x, C.killedTransition x A = 0)
    (hnoUp : ∀ i, i ≤ ℓ → ∀ x ∈ levels T A Λ ℓ N D i,
      C.killedTransition x (levels T A Λ ℓ N D i)ᶜ = 0)
    (R : ℝ) (hR : 0 < R)
    (d : RankOneSpectralData (R • transferOperator (𝕜 := ℝ)
      (chain C (closedLayer T A Λ ℓ N D j) (closedLayer_measurable T A Λ ℓ N D j))
      (strongFeller C hSF (closedLayer T A Λ ℓ N D j) (closedLayer_measurable T A Λ ℓ N D j)))
      (1 : closedLayer T A Λ ℓ N D j →ᵇ ℝ))
    {β : ℝ} (hβ : 0 < β) (hβlam : β < d.rate)
    (hleaf : ∀ i : Fin ℓ, i ≠ j → ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
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
    ∃ dg : RankOneSpectralData (transferOperator (𝕜 := ℝ) C hSF) (1 : X →ᵇ ℝ),
      dg.rate = R⁻¹ * d.rate ∧ C.IsQuasiErgodic (productMeasure C hSF dg) ∧
      productMeasure C hSF dg = (eigenvectorMeasure μ d.eigenvector).map Subtype.val ∧
      Λ (D.index j) ⊆ (productMeasure C hSF dg).support ∧
      (∀ η : Measure X, C.IsQuasiErgodic η → Λ (D.index j) ⊆ η.support → η = productMeasure C hSF dg) ∧
      (∀ x : stratum T A Λ ℓ N D j, dg.eigenvector x.val =
        (R⁻¹ * d.rate)⁻¹ * d.eigenvector ⟨x.val, subset_closure x.property⟩) ∧
      ∀ f : X → ℝ, Measurable f → (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) → ∀ x,
        0 < dg.eigenvector x → Tendsto (MeasurableCanonical.pathAverage C f x) atTop
          (𝓝 (∫ y, f y ∂productMeasure C hSF dg)) := by
  let M := levels T A Λ ℓ N D
  let L0 := M j.val
  let L1 := M (j.val + 1)
  let S := L1 \ L0
  let K := closure S
  have hL0 := ambient_levels_measurable T A hA Λ ℓ N D j.val
  have hL1 := ambient_levels_measurable T A hA Λ ℓ N D (j.val + 1)
  obtain ⟨γ, CA, CD, hγ, hγd, hCA, hCD, hpowA, hpowD⟩ :=
    exists_actual_prefix_two_subordinate_bounds T A hA Λ ℓ N D ℓ le_rfl j j.isLt C hSF R hβ hβlam
      (fun i _ hi => hnoUp i hi) (fun i _ hi => hleaf i hi)
  obtain ⟨CA', hCA', hpowA'⟩ := exists_prefix_bound_of_live_interval_bound C hSF A L0
    hA.measurableSet hL0 hzeroA R hCA hγ hpowA
  have hterminal : M ℓ = univ := by
    change levels T A Λ ℓ N D ℓ = univ
    have hj := j.isLt
    rw [levels, shiftedFiltration_pos T N A D.levels (by omega), D.terminal, preimage_univ]
  have hupper : ∀ n : ℕ, ‖(R • transferOperator (𝕜 := ℝ) (chain C L1ᶜ hL1.compl)
      (strongFeller C hSF L1ᶜ hL1.compl))^n‖ ≤ CD * γ^n := by
    intro n
    have hp := hpowD n
    have he : M ℓ \ M (j.val + 1) = L1ᶜ := by rw [hterminal]; ext x; exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩
    have hc := power_norm_congr C hSF (M ℓ \ M (j.val + 1)) L1ᶜ
      ((ambient_levels_measurable T A hA Λ ℓ N D ℓ).diff hL1) hL1.compl he R n
    exact hc.symm.trans_le hp
  let CK := chain C K isClosed_closure.measurableSet
  let sfK := strongFeller C hSF K isClosed_closure.measurableSet
  have hμfinite : IsFiniteMeasure μ := inferInstance
  let μ' : Measure (closure (L1 \ L0) : Set X) := μ
  let : IsFiniteMeasure μ' := hμfinite
  let UK := innerLevel S K
  have hUK : MeasurableSet UK := (hL1.diff hL0).preimage measurable_subtype_coe
  have hzero : ∀ x : K, CK.killedTransition x UKᶜ = 0 :=
    NullBoundaryLayer.boundary_mass_zero_of_density CK UK
      (σ.comap (Subtype.val : K → X)) (fun x => q (x.1.val, x.2.val))
      (restricted_density_law C K isClosed_closure.measurableSet σ q hdensity)
      (relative_stratum_complement_zero σ S K isClosed_closure.measurableSet
        (closed_layer_extra_zero T A hA Λ ℓ N D σ hpre hnull j))
  have hg0 : ∀ x, 0 ≤ d.eigenvector x := d.eigenvector_nonneg_of_positive (by
    intro f hf x
    change 0 ≤ R * transferOperator (𝕜 := ℝ) CK sfK f x
    exact mul_nonneg hR.le (LayerRankOne.actual_transfer_positive CK sfK f hf x))
  let Core : Set S := {x | x.val ∈ Λ (D.index j)}
  have hcoreS : Λ (D.index j) ⊆ S := by
    rw [← literal_core T A Λ ℓ N D j]
    exact fun _ hx => hx.1 0
  have hCore : Core.Nonempty := by
    obtain ⟨x, hx⟩ := hΛ
    exact ⟨⟨x, hcoreS hx⟩, hx⟩
  obtain ⟨dg, hrate, hq, hprod, hsupp, huniq, hv, hlim⟩ :=
    exists_selected_QEM_from_raw_closed_local C hSF L0 L1 hL0 hL1
      (levels_monotone T A Λ ℓ N D (Nat.le_succ _))
      (hnoUp j.val (by omega))
      (fun x hx => by rw [ae_iff]; exact hnoUp (j.val + 1) (by omega) x hx)
      hzero R hR d hCA' hCD hγ.le hγ.le hγd hγd hpowA' hupper μ' hmean hg0 Core hCore
      (fun x hx => hpos _ hx) (fun x hx => hsupport hx)
  have himage : Subtype.val '' Core = Λ (D.index j) := by
    ext x
    exact ⟨by rintro ⟨p, hp, rfl⟩; exact hp,
      fun hx => ⟨⟨x, hcoreS hx⟩, hx, rfl⟩⟩
  exact ⟨dg, hrate, hq, hprod, himage ▸ hsupp,
    fun η hη hηsupport => huniq η hη (himage.symm ▸ hηsupport), hv, hlim⟩

end ConditionedStochasticStabilityHyperbolic.Global.ActualFiltrationSelectedQuasiErgodic
