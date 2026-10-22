module

public import ConditionedStochasticStabilityHyperbolic.Neighborhoods.TwoSidedAnalysisCollar

/-! Retained analysis collars inside arbitrary compact live regions. No
regular-closed representation of a filtration layer is required. -/

@[expose] public noncomputable section
open Set Metric Function
namespace ConditionedStochasticStabilityHyperbolic
variable {X : Type*} [MetricSpace X]

theorem exists_orbitNeighborhood_compact (T : X ≃ₜ X) (K V : Set X)
    (hK : IsCompact K) (hVK : V ⊆ K) {Λ : Set X} (hΛ : Λ.Nonempty) (hcore : LeanShared.isolatedCore T K = Λ)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : closure (thickening ρ Λ) ⊆ V) :
    ∃ N : ℕ, 0 < N ∧
      IsOpen (orbitNeighborhood T Λ ρ N) ∧
      Λ ⊆ orbitNeighborhood T Λ ρ N ∧
      closure (orbitNeighborhood T Λ ρ N) ⊆ V ∧
      (T '' closure (orbitNeighborhood T Λ ρ N)) ∩
        LeanShared.forwardTrapped T K ⊆ orbitNeighborhood T Λ ρ N := by
  obtain ⟨N, hN, htail⟩ := LeanShared.exists_pos_stable_tail_subset T
    (K := K) (U := thickening (ρ / 2) Λ)
    hK isOpen_thickening
    (by rw [hcore]; exact self_subset_thickening (half_pos hρ) Λ)
  have hUball := orbitNeighborhood_subset_thickening (T := (T : X → X)) hΛ ρ hN
  have hUV : closure (orbitNeighborhood T Λ ρ N) ⊆ V :=
    (closure_mono hUball).trans hball
  refine ⟨N, hN, isOpen_orbitNeighborhood T.continuous Λ ρ N, ?_, hUV, ?_⟩
  · intro x hx j
    have hxcore : x ∈ LeanShared.isolatedCore T K := by rwa [hcore]
    have hjΛ : (T : X → X)^[j.val] x ∈ Λ := by
      rw [← hcore]
      exact LeanShared.iterate_mem_isolatedCore T K hxcore j.val
    simpa only [infDist_zero_of_mem hjΛ, mul_zero] using hρ
  · rintro y ⟨⟨x, hx, rfl⟩, hTx⟩ j
    have hxstable : x ∈ LeanShared.forwardTrapped T K :=
      LeanShared.mem_forwardTrapped_of_mem_of_image_mem (hVK (hUV hx)) hTx
    have hq : 1 < stepWeight N := stepWeight_gt_one hN
    have hqpos : 0 < stepWeight N := lt_trans zero_lt_one hq
    have hqρ : ρ < stepWeight N * ρ := by nlinarith
    have hshift : (T : X → X)^[j.val] (T x) = (T : X → X)^[j.val + 1] x :=
      (iterate_succ_apply T j.val x).symm
    rw [hshift]
    have hbound : stepWeight N ^ (j.val + 1) *
        infDist ((T : X → X)^[j.val + 1] x) Λ ≤ ρ := by
      by_cases hj : j.val + 1 < N
      · exact closure_orbitNeighborhood_le T.continuous hx ⟨j.val + 1, hj⟩
      · have hlast : j.val + 1 = N := by omega
        rw [hlast, stepWeight_pow hN]
        have hdist : infDist ((T : X → X)^[N] x) Λ < ρ / 2 :=
          (mem_thickening_iff_infDist_lt hΛ).mp (htail ⟨x, hxstable, rfl⟩)
        linarith
    rw [pow_succ] at hbound
    nlinarith


theorem exists_twoSided_positive_compact_collar
    (T : X ≃ₜ X) (K W Λ : Set X) (hK : IsCompact K) (hW : IsOpen W)
    (hΛc : IsCompact Λ) (hΛ : Λ.Nonempty) (hΛW : Λ ⊆ W) (hWK : W ⊆ K)
    (hcore : LeanShared.isolatedCore T K = Λ)
    (w : X → ℝ) (hw : Continuous w) (hwΛ : ∀ x ∈ Λ, 0 < w x) :
    ∃ (G B : Set X), IsOpen G ∧ Λ ⊆ G ∧ closure G ⊆ W ∧
      (∀ x ∈ closure G, 0 < w x ∧ 0 < w (T.symm x)) ∧
      IsOpen B ∧ Λ ⊆ B ∧ closure B ⊆ G ∧
      (T '' closure B) ∩ LeanShared.forwardTrapped T K ⊆ B := by
  let P := W ∩ {x | 0 < w x} ∩ {x | 0 < w (T.symm x)}
  have hP : IsOpen P := (hW.inter (isOpen_lt continuous_const hw)).inter
    (isOpen_lt continuous_const (hw.comp T.symm.continuous))
  have hΛP : Λ ⊆ P := by
    intro x hx
    have hxi : T.symm x ∈ Λ := by
      rw [← hcore] at hx ⊢
      exact LeanShared.mapsTo_isolatedCore_symm T K hx
    exact ⟨⟨hΛW hx, hwΛ x hx⟩, hwΛ (T.symm x) hxi⟩
  obtain ⟨ρ, hρ, hρP⟩ := hΛc.exists_cthickening_subset_open hP hΛP
  let G := thickening ρ Λ
  have hG : IsOpen G := isOpen_thickening
  have hΛG : Λ ⊆ G := self_subset_thickening hρ Λ
  have hGP : closure G ⊆ P := (closure_thickening_subset_cthickening ρ Λ).trans hρP
  have hGW : closure G ⊆ W := fun _ hx => (hGP hx).1.1
  have hpositive : ∀ x ∈ closure G, 0 < w x ∧ 0 < w (T.symm x) :=
    fun _ hx => ⟨(hGP hx).1.2, (hGP hx).2⟩
  obtain ⟨ρ₂, hρ₂, hρ₂G⟩ := hΛc.exists_cthickening_subset_open hG hΛG
  have hballG : closure (thickening ρ₂ Λ) ⊆ G :=
    (closure_thickening_subset_cthickening ρ₂ Λ).trans hρ₂G
  obtain ⟨N, _hN, hB, hΛB, hBG, hsep⟩ := exists_orbitNeighborhood_compact T K G hK
    (subset_closure.trans (hGW.trans hWK)) hΛ hcore hρ₂ hballG
  exact ⟨G, orbitNeighborhood T Λ ρ₂ N, hG, hΛG, hGW, hpositive, hB, hΛB, hBG, hsep⟩

end ConditionedStochasticStabilityHyperbolic
