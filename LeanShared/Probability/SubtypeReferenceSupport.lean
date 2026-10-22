module

public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Comap

/-! Ambient reference volume gives support on every open live interior after
passing to a measurable closed collar subtype. Null boundary components are
allowed; no full-support assertion on the entire collar is used. -/

@[expose] public noncomputable section
open Set MeasureTheory Topology
namespace LeanShared.SubtypeReferenceSupport
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
theorem open_subset_support_comap (σ : Measure X) [σ.IsOpenPosMeasure]
    (K V : Set X) (hK : MeasurableSet K) (hV : IsOpen V) (hVK : V ⊆ K) :
    ∀ x : K, x.val ∈ V → x ∈ (σ.comap (Subtype.val : K → X)).support := by
  intro x hx
  rw [Measure.support_eq_forall_isOpen]
  intro O hxO hO
  rw [(MeasurableEmbedding.subtype_coe hK).comap_apply]
  obtain ⟨A, hA, hpre⟩ := isOpen_induced_iff.mp hO
  have hxA : x.val ∈ A := by
    change x ∈ (Subtype.val : K → X) ⁻¹' A
    rwa [hpre]
  have hpos : 0 < σ (A ∩ V) := (hA.inter hV).measure_pos σ ⟨x.val, hxA, hx⟩
  apply hpos.trans_le
  apply measure_mono
  intro y hy
  refine ⟨⟨y, hVK hy.2⟩, ?_, rfl⟩
  rw [← hpre]
  exact hy.1

end LeanShared.SubtypeReferenceSupport
