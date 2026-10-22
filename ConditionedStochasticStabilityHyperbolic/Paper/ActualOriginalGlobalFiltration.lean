module
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualOriginalGlobalChain
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularGlobalFiltration

/-! The actual original endpoint process preserves every adapted level on
one noise germ. This source is constructed directly from the original cube
closeness, compact adapted levels and explicit strict trapping; it needs no
original anisotropic model or representation. -/
public noncomputable section
open Set Filter MeasureTheory IsManifold Function
open scoped Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise.ActualOriginalGlobalChain
open LeanShared Global
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] {T : M ≃ₜ M} {r : ℝ}
  (F : Maps (E := E) (ι := ι) T r)
local instance rawFiltrationProbability (L : Laws (ι := ι)) (ε : ℝ≥0) :
    IsProbabilityMeasure (L.law ε) := L.probability ε

omit [MeasurableSpace M] [BorelSpace M] in
private theorem raw_close (δ : ℝ) (positive : 0 < δ) :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, 0 < ε ∧ ε ≤ F.window ∧
      ∀ x : M, ∀ control : cube (ι := ι) ε, dist (F.family ε control.val x) (T x) < δ := by
  have hmul : Tendsto (fun ε : ℝ≥0 => F.constant * (ε : ℝ)) (𝓝 0) (𝓝 0) := by
    simpa only [NNReal.coe_zero, mul_zero] using
      (NNReal.continuous_coe.tendsto (0 : ℝ≥0)).const_mul F.constant
  have window : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ε < F.window :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds F.window_positive)
  have small : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, F.constant * (ε : ℝ) < δ :=
    (hmul.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds positive)
  filter_upwards [self_mem_nhdsWithin, window, small] with ε hε hwindow hsmall
  exact ⟨hε, hwindow.le, fun x control => (F.uniform_close ε hε hwindow.le control x).trans_lt hsmall⟩

omit [MeasurableSpace M] [BorelSpace M] in
private theorem preserves_levels (N : ℕ) (A : Set M) (levels : ℕ → Set M) (ℓ : ℕ)
    (compact : ∀ i, 0 < i → i ≤ ℓ → IsCompact (levels i))
    (adapted : ∀ i, 0 < i → i ≤ ℓ → MapsTo T (levels i) (interior (levels i))) :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, 0 < ε ∧ ε ≤ F.window ∧
      ∀ control : cube (ι := ι) ε, ∀ i, 0 < i → i ≤ ℓ →
        MapsTo (fun x => F.family ε control.val x)
          (shiftedFiltration T N A levels i) (shiftedFiltration T N A levels i) := by
  obtain ⟨δ, positive, preserve⟩ := exists_pos_finite_adapted_margin T T.continuous
    (fun j : Fin ℓ => shiftedFiltration T N A levels (j.val + 1))
    (fun j => by
      rw [shiftedFiltration_pos T N A levels (by omega : 0 < j.val + 1)]
      exact isCompact_preimage_iterate T (compact _ (by omega) (by omega)) N)
    (fun j => by
      rw [shiftedFiltration_pos T N A levels (by omega : 0 < j.val + 1)]
      intro x hx
      apply preimage_interior_subset_interior_preimage (T.continuous.iterate N)
      change (T : M → M)^[N] (T x) ∈ interior (levels (j.val + 1))
      rw [← iterate_succ_apply, iterate_succ_apply']
      exact adapted _ (by omega) (by omega) hx)
  filter_upwards [raw_close F δ positive] with ε close
  refine ⟨close.1, close.2.1, ?_⟩
  intro control i hi hiℓ x hx
  let j : Fin ℓ := ⟨i - 1, by omega⟩
  have equality : j.val + 1 = i := by dsimp [j]; omega
  have hp := preserve (fun x => F.family ε control.val x)
    (fun _j y _hy => close.2.2 y control) j
  rw [equality] at hp
  exact interior_subset (hp hx)

/-- Every level, including the fixed absorbing zero level, is preserved by
the actual original process. The driving law is chosen only after the noise
germ; no endpoint spectral source or no-upward certificate is supplied. -/
theorem eventually_all_levels [CompactSpace M]
    (L : Laws (ι := ι)) (N : ℕ) (A : Set M) (hA : IsOpen A)
    (strict : MapsTo T (closure A) A) (levels : ℕ → Set M) (ℓ : ℕ)
    (compact : ∀ i, 0 < i → i ≤ ℓ → IsCompact (levels i))
    (adapted : ∀ i, 0 < i → i ≤ ℓ → MapsTo T (levels i) (interior (levels i)))
    (w : M → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (bound : ∀ x, w x ≤ R) :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ i, i ≤ ℓ → ∀ x ∈ shiftedFiltration T N A levels i,
      (chain F L Aᶜ hA.measurableSet.compl w hw R hR bound ε).killedTransition x
        (shiftedFiltration T N A levels i)ᶜ = 0 := by
  obtain ⟨δ, positive, preserveA⟩ := ActualAbsorbingKernelSupport.exists_pos_uniform_absorbing_map_tolerance
    T T.continuous A hA strict
  filter_upwards [preserves_levels F N A levels ℓ compact adapted, raw_close F δ positive]
    with ε preserve close
  intro i hi
  rw [chain_eq F L Aᶜ hA.measurableSet.compl w hw R hR bound ε close.1 close.2.1]
  by_cases zero : i = 0
  · subst i
    rw [shiftedFiltration_zero]
    exact ActualAbsorbingKernelSupport.no_surviving_departure_of_absorbing_invariant
      (L.law ε) _ (F.raw_measurable ε close.1 close.2.1) A hA.measurableSet
      w hw R hR bound
      (fun y hy control => preserveA (fun x => F.family ε control.val x)
        (fun z _hz => close.2.2 z control) hy)
  · have positiveIndex : 0 < i := Nat.pos_of_ne_zero zero
    have compactLevel : IsCompact (shiftedFiltration T N A levels i) := by
      rw [shiftedFiltration_pos T N A levels positiveIndex]
      exact isCompact_preimage_iterate T (compact i positiveIndex hi) N
    exact noise_chain_no_upward_transition (L.law ε) _ (F.raw_measurable ε close.1 close.2.1)
      A hA.measurableSet w hw R hR bound _ compactLevel.isClosed.measurableSet
      (fun control => preserve.2.2 control i positiveIndex hi)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise.ActualOriginalGlobalChain
