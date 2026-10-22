module

public import LeanShared.Dynamics.IsolatingNeighborhood
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Filtration shifts with a fixed absorbing level

Forward preimages shift the positive filtration levels while level zero stays
equal to the actual absorbing region. All two-sided layer cores are unchanged,
including the first layer. Nesting uses forward invariance of the absorbing
set. Positive-level adapted inclusions are preserved; no interior inclusion
or compactness of the absorbing level is asserted without its own hypothesis.
-/

@[expose] public section

open Set Function

namespace LeanShared

variable {X : Type*} [TopologicalSpace X]

/-- Shifting a region by a finite forward preimage does not change its full
two-sided trapped core. No compactness or forward invariance is needed. -/
theorem isolatedCore_preimage_iterate (T : X ≃ₜ X) (K : Set X) (N : ℕ) :
    isolatedCore T ((T : X → X)^[N] ⁻¹' K) = isolatedCore T K := by
  have hcancel (y : X) : (T : X → X)^[N] ((T.symm : X → X)^[N] y) = y :=
    T.right_inv.iterate N y
  ext x
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · have hy := iterate_symm_mem_isolatedCore T ((T : X → X)^[N] ⁻¹' K) hx N
      intro j
      have h := hy.1 j
      change (T : X → X)^[N] ((T : X → X)^[j] ((T.symm : X → X)^[N] x)) ∈ K at h
      rw [← iterate_add_apply, Nat.add_comm N j, iterate_add_apply,
        hcancel x] at h
      exact h
    · intro j
      have h := hx.2 (N + j)
      change (T : X → X)^[N] ((T.symm : X → X)^[N + j] x) ∈ K at h
      rw [iterate_add_apply, hcancel ((T.symm : X → X)^[j] x)] at h
      exact h
  · intro hx
    refine ⟨?_, ?_⟩
    · intro j
      exact forwardTrapped_subset T K
        (iterate_mem_isolatedCore T K (iterate_mem_isolatedCore T K hx j) N).1
    · intro j
      exact forwardTrapped_subset T K
        (iterate_mem_isolatedCore T K (iterate_symm_mem_isolatedCore T K hx j) N).1

theorem isolatedCore_inter (T : X ≃ₜ X) (K L : Set X) :
    isolatedCore T (K ∩ L) = isolatedCore T K ∩ isolatedCore T L := by
  ext x
  constructor
  · intro hx
    exact ⟨⟨fun n => (hx.1 n).1, fun n => (hx.2 n).1⟩,
      ⟨fun n => (hx.1 n).2, fun n => (hx.2 n).2⟩⟩
  · intro hx
    exact ⟨fun n => ⟨hx.1.1 n, hx.2.1 n⟩, fun n => ⟨hx.1.2 n, hx.2.2 n⟩⟩

/-- Difference is an intersection with a complement at every orbit time.
This is not the generally false difference of the two isolated cores. -/
theorem isolatedCore_sdiff (T : X ≃ₜ X) (K L : Set X) :
    isolatedCore T (K \ L) = isolatedCore T K ∩ isolatedCore T Lᶜ :=
  isolatedCore_inter T K Lᶜ

/-- In particular the first layer is unchanged when its upper level is shifted
and its absorbing lower level is held fixed. -/
theorem isolatedCore_preimage_iterate_sdiff (T : X ≃ₜ X) (K A : Set X) (N : ℕ) :
    isolatedCore T (((T : X → X)^[N] ⁻¹' K) \ A) = isolatedCore T (K \ A) := by
  rw [isolatedCore_sdiff, isolatedCore_preimage_iterate, ← isolatedCore_sdiff]

/-- Both adjacent positive levels may be shifted without changing their layer. -/
theorem isolatedCore_sdiff_preimages (T : X ≃ₜ X) (K L : Set X) (N : ℕ) :
    isolatedCore T (((T : X → X)^[N] ⁻¹' K) \ ((T : X → X)^[N] ⁻¹' L)) =
      isolatedCore T (K \ L) := by
  rw [← preimage_sdiff, isolatedCore_preimage_iterate]

/-- The shifted level is the backward image under the inverse iterate. -/
theorem preimage_iterate_eq_image_symm_iterate (T : X ≃ₜ X) (K : Set X) (N : ℕ) :
    (T : X → X)^[N] ⁻¹' K = (T.symm : X → X)^[N] '' K := by
  ext x
  constructor
  · intro hx
    refine ⟨(T : X → X)^[N] x, hx, ?_⟩
    exact T.left_inv.iterate N x
  · rintro ⟨y, hy, rfl⟩
    have hcancel : (T : X → X)^[N] ((T.symm : X → X)^[N] y) = y :=
      T.right_inv.iterate N y
    change (T : X → X)^[N] ((T.symm : X → X)^[N] y) ∈ K
    rwa [hcancel]

theorem isCompact_preimage_iterate (T : X ≃ₜ X) {K : Set X} (hK : IsCompact K) (N : ℕ) :
    IsCompact ((T : X → X)^[N] ⁻¹' K) := by
  rw [preimage_iterate_eq_image_symm_iterate]
  exact hK.image (T.symm.continuous.iterate N)

/-- The exact interior identity uses the homeomorphism at every iterate. -/
theorem preimage_iterate_interior (T : X ≃ₜ X) (K : Set X) (N : ℕ) :
    (T : X → X)^[N] ⁻¹' interior K = interior ((T : X → X)^[N] ⁻¹' K) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      change T ⁻¹' ((T : X → X)^[N] ⁻¹' interior K) =
        interior (T ⁻¹' ((T : X → X)^[N] ⁻¹' K))
      rw [ih, T.preimage_interior]

/-- Positive levels move by a common forward preimage; the absorbing level
keeps its original state-space meaning. -/
def shiftedFiltration (T : X ≃ₜ X) (N : ℕ) (A : Set X) (M : ℕ → Set X) (i : ℕ) : Set X :=
  if i = 0 then A else (T : X → X)^[N] ⁻¹' M i

/-- Layer `i` lies between filtration levels `i` and `i+1`. -/
def filtrationLayer (M : ℕ → Set X) (i : ℕ) : Set X := M (i + 1) \ M i

@[simp] theorem shiftedFiltration_zero (T : X ≃ₜ X) (N : ℕ) (A : Set X) (M : ℕ → Set X) :
    shiftedFiltration T N A M 0 = A := by simp [shiftedFiltration]

theorem shiftedFiltration_pos (T : X ≃ₜ X) (N : ℕ) (A : Set X) (M : ℕ → Set X)
    {i : ℕ} (hi : 0 < i) : shiftedFiltration T N A M i = (T : X → X)^[N] ⁻¹' M i := by
  simp [shiftedFiltration, Nat.ne_of_gt hi]

/-- Compactness of positive levels is preserved without any assumption on `A`. -/
theorem shiftedFiltration_positive_compact (T : X ≃ₜ X) (N : ℕ)
    (A : Set X) (M : ℕ → Set X) (hM : ∀ i > 0, IsCompact (M i)) :
    ∀ i > 0, IsCompact (shiftedFiltration T N A M i) := by
  intro i hi
  rw [shiftedFiltration_pos T N A M hi]
  exact isCompact_preimage_iterate T (hM i hi) N

/-- A positive terminal level equal to the whole space stays equal to it. -/
theorem shiftedFiltration_terminal (T : X ≃ₜ X) (N : ℕ) (A : Set X) (M : ℕ → Set X)
    {i : ℕ} (hi : 0 < i) (htop : M i = univ) : shiftedFiltration T N A M i = univ := by
  rw [shiftedFiltration_pos T N A M hi, htop, preimage_univ]

/-- The fixed absorption set remains the zeroth level at every shift. -/
theorem shiftedFiltration_absorbing (T : X ≃ₜ X) (N : ℕ) (A : Set X) (M : ℕ → Set X)
    (hA : MapsTo T A A) : MapsTo T (shiftedFiltration T N A M 0)
      (shiftedFiltration T N A M 0) := by
  simpa only [shiftedFiltration_zero] using hA

/-- Nesting survives the fixed-zero-level shift when the absorbing set is
forward invariant and contained in the first positive level. -/
theorem shiftedFiltration_monotone (T : X ≃ₜ X) (N : ℕ) (A : Set X) (M : ℕ → Set X)
    (hM : Monotone M) (hA1 : A ⊆ M 1) (hA : MapsTo T A A) :
    Monotone (shiftedFiltration T N A M) := by
  intro i j hij x hx
  by_cases hj : j = 0
  · have hi : i = 0 := by omega
    simpa [hi, hj] using hx
  · rw [shiftedFiltration_pos T N A M (by omega : 0 < j)]
    by_cases hi : i = 0
    · rw [hi, shiftedFiltration_zero] at hx
      exact hM (by omega : 1 ≤ j) (hA1 (hA.iterate N hx))
    · rw [shiftedFiltration_pos T N A M (by omega : 0 < i)] at hx
      exact hM hij hx

/-- Every layer core is preserved. Shift zero denotes the same augmented
filtration with absorbing level `A`, rather than replacing it by `M 0`. -/
theorem isolatedCore_shiftedFiltration_layer (T : X ≃ₜ X) (N : ℕ)
    (A : Set X) (M : ℕ → Set X) (i : ℕ) :
    isolatedCore T (filtrationLayer (shiftedFiltration T N A M) i) =
      isolatedCore T (filtrationLayer (shiftedFiltration T 0 A M) i) := by
  cases i with
  | zero =>
      simp only [filtrationLayer, shiftedFiltration_zero, zero_add]
      rw [shiftedFiltration_pos T N A M (by omega : 0 < 1),
        shiftedFiltration_pos T 0 A M (by omega : 0 < 1)]
      simpa using isolatedCore_preimage_iterate_sdiff T (M 1) A N
  | succ i =>
      rw [filtrationLayer, filtrationLayer,
        shiftedFiltration_pos T N A M (by omega : 0 < i + 1 + 1),
        shiftedFiltration_pos T N A M (by omega : 0 < i + 1),
        shiftedFiltration_pos T 0 A M (by omega : 0 < i + 1 + 1),
        shiftedFiltration_pos T 0 A M (by omega : 0 < i + 1)]
      simpa using isolatedCore_sdiff_preimages T (M (i + 1 + 1)) (M (i + 1)) N

/-- Adapted positive levels remain adapted after the preimage shift. This
assertion deliberately does not impose an interior condition on level zero. -/
theorem shiftedFiltration_positive_adapted (T : X ≃ₜ X) (N : ℕ)
    (A : Set X) (M : ℕ → Set X)
    (hadapt : ∀ i > 0, MapsTo T (M i) (interior (M i))) :
    ∀ i > 0, MapsTo T (shiftedFiltration T N A M i)
      (interior (shiftedFiltration T N A M i)) := by
  intro i hi
  rw [shiftedFiltration_pos T N A M hi]
  intro x hx
  apply preimage_interior_subset_interior_preimage (T.continuous.iterate N)
  change (T : X → X)^[N] (T x) ∈ interior (M i)
  rw [← iterate_succ_apply, iterate_succ_apply']
  exact hadapt i hi hx

section Metric

variable {Y : Type*} [MetricSpace Y]

/-- Each compact positive adapted level has a genuine uniform perturbation
margin, obtained from its compact image inside its open interior. -/
theorem exists_pos_shiftedFiltration_level_margin (T : Y ≃ₜ Y) (N : ℕ)
    (A : Set Y) (M : ℕ → Set Y)
    (hcompact : ∀ i > 0, IsCompact (M i))
    (hadapt : ∀ i > 0, MapsTo T (M i) (interior (M i))) (i : ℕ) (hi : 0 < i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ F : Y → Y,
      (∀ x ∈ shiftedFiltration T N A M i, dist (F x) (T x) < δ) →
      MapsTo F (shiftedFiltration T N A M i) (interior (shiftedFiltration T N A M i)) := by
  have hK := shiftedFiltration_positive_compact T N A M hcompact i hi
  have hmap := shiftedFiltration_positive_adapted T N A M hadapt i hi
  obtain ⟨δ, hδ, hthick⟩ := (hK.image T.continuous).exists_thickening_subset_open
    isOpen_interior hmap.image_subset
  refine ⟨δ, hδ, ?_⟩
  intro F hF x hx
  apply hthick
  exact Metric.mem_thickening_iff.mpr ⟨T x, ⟨x, hx, rfl⟩, hF x hx⟩

end Metric

end LeanShared
