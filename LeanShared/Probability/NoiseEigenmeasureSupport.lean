module

public import LeanShared.Probability.NoiseAccessibility
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Exact support parents for compact noise images

The left eigenmeasure law forces its support into the closed image of its
support and the noise space. Compactness upgrades a closure assertion to
exact parents. Neither positive departure weights nor full-support noise
are needed for this backward assertion. Forward support propagation is a
separate assertion.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace LeanShared.NoiseEigenmeasureSupport

variable {X Y Ω : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Ω] [CompactSpace Ω]

/-- A left eigenmeasure is supported in any closed set which contains almost
every transition from almost every departure state. -/
theorem support_subset_of_eigenmeasure (K : Kernel X X) (μ : Measure X)
    (r : ℝ≥0∞) (hr : r ≠ 0) (heigen : K ∘ₘ μ = r • μ)
    (S : Set X) (hS : IsClosed S)
    (hstep : ∀ᵐ x ∂μ, ∀ᵐ y ∂K x, y ∈ S) : μ.support ⊆ S := by
  have ha := Measure.ae_comp_of_ae_ae hS.measurableSet hstep
  rw [heigen] at ha
  exact μ.support_subset_of_isClosed hS ((Measure.ae_ennreal_smul_measure_iff hr).mp ha)

/-- Positive transition mass throughout a departure neighbourhood propagates
support forward under the actual left eigenmeasure law. -/
theorem mem_support_of_positive_transitions (K : Kernel X X) (μ : Measure X)
    (r : ℝ≥0∞) (heigen : K ∘ₘ μ = r • μ) (x p : X) (hx : x ∈ μ.support)
    (haccess : ∀ V : Set X, IsOpen V → p ∈ V →
      ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ ∀ z ∈ N, 0 < K z V) : p ∈ μ.support := by
  rw [Measure.support_eq_forall_isOpen]
  intro V hpV hV
  obtain ⟨N, hN, hxN, hNV⟩ := haccess V hV hpV
  have hμN := (Measure.mem_support_iff_forall x).mp hx N (hN.mem_nhds hxN)
  have hp : 0 < ∫⁻ z, K z V ∂μ :=
    (lintegral_pos_iff_support (K.measurable_coe hV.measurableSet)).mpr
      (hμN.trans_le (measure_mono (fun z hz => (hNV z hz).ne')))
  have he : (∫⁻ z, K z V ∂μ) = r * μ V := by
    rw [← Measure.bind_apply hV.measurableSet K.aemeasurable]
    rw [heigen, Measure.smul_apply, smul_eq_mul]
  rw [he] at hp
  apply pos_iff_ne_zero.mpr
  intro hz
  rw [hz, mul_zero] at hp
  exact lt_irrefl _ hp

/-- Compact source support and compact noise supply an exact parent for
every supported point. `i` allows the actual live-state subtype to be
embedded in an ambient space where the noisy map is defined. -/
theorem exists_support_parent (K : Kernel X X) (μ : Measure X)
    (hμcompact : IsCompact μ.support) (hμae : ∀ᵐ x ∂μ, x ∈ μ.support)
    (r : ℝ≥0∞) (hr : r ≠ 0) (heigen : K ∘ₘ μ = r • μ)
    (i : X → Y) (hi : Continuous i) (F : X × Ω → Y) (hF : Continuous F)
    (hstep : ∀ x ∈ μ.support, ∀ᵐ y ∂K x, ∃ ω, F (x, ω) = i y)
    (p : X) (hp : p ∈ μ.support) :
    ∃ x ∈ μ.support, ∃ ω : Ω, F (x, ω) = i p := by
  let S : Set Y := F '' (μ.support ×ˢ (univ : Set Ω))
  have hS : IsClosed S := ((hμcompact.prod isCompact_univ).image hF).isClosed
  have hsub : μ.support ⊆ i ⁻¹' S := by
    apply support_subset_of_eigenmeasure K μ r hr heigen _ (hS.preimage hi)
    filter_upwards [hμae] with x hx
    filter_upwards [hstep x hx] with y hy
    obtain ⟨ω, hω⟩ := hy
    exact ⟨(x, ω), ⟨hx, mem_univ _⟩, hω⟩
  obtain ⟨⟨x, ω⟩, hsource, heq⟩ := hsub hp
  exact ⟨x, hsource.1, ω, heq⟩

omit [BorelSpace X] [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Ω]
  [CompactSpace Ω] in
/-- Exact support parents recursively produce an infinite backward support
orbit with one admissible noise parameter at every step. -/
theorem exists_backward_support_orbit (μ : Measure X) (i : X → Y) (F : X × Ω → Y)
    (hparent : ∀ p ∈ μ.support, ∃ x ∈ μ.support, ∃ ω, F (x, ω) = i p)
    (p : X) (hp : p ∈ μ.support) :
    ∃ z : ℕ → X, ∃ noise : ℕ → Ω, z 0 = p ∧
      (∀ n, z n ∈ μ.support) ∧ (∀ n, F (z (n + 1), noise n) = i (z n)) := by
  let parent (q : μ.support) : μ.support :=
    ⟨Classical.choose (hparent q.val q.property),
      (Classical.choose_spec (hparent q.val q.property)).1⟩
  have hnoise (q : μ.support) : ∃ ω, F ((parent q).val, ω) = i q.val :=
    (Classical.choose_spec (hparent q.val q.property)).2
  let a : ℕ → μ.support := fun n => parent^[n] ⟨p, hp⟩
  refine ⟨fun n => (a n).val, fun n => Classical.choose (hnoise (a n)), rfl,
    (fun n => (a n).property), ?_⟩
  intro n
  change F ((a (n + 1)).val, Classical.choose (hnoise (a n))) = i (a n).val
  have he : a (n + 1) = parent (a n) := Function.iterate_succ_apply' parent n _
  rw [he]
  exact Classical.choose_spec (hnoise (a n))

end LeanShared.NoiseEigenmeasureSupport
