module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.Separation.Regular

/-! A finite smooth partition is fixed on an OPEN neighborhood of the
compact deterministic survivor set. Its derivatives are independent of
later random words. CompactFiberCapture then derives the nearby-word
capture region; no random partition or random robustness is an input. -/

public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff BigOperators Topology
namespace LeanShared.FiniteSmoothCapturePartition
variable {E M J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] [Fintype J]

theorem exists_partition (K : Set M) (hK : IsCompact K) (v : J → Set M)
    (hv : ∀ i, IsOpen (v i)) (hcover : K ⊆ ⋃ i, v i) :
    ∃ (capture : Set M) (β : J → M → ℝ), IsOpen capture ∧ K ⊆ capture ∧
      (∀ i, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ (β i)) ∧
      (∀ i x, 0 ≤ β i x ∧ β i x ≤ 1) ∧
      (∀ i, tsupport (β i) ⊆ v i) ∧
      (∀ x ∈ capture, ∑ i, β i x = 1) := by
  obtain ⟨capture, hopen, hinner, houter⟩ := hK.exists_isOpen_closure_subset
    ((isOpen_iUnion hv).mem_nhdsSet.mpr hcover)
  obtain ⟨β, hβ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, E))
    isClosed_closure v hv houter
  refine ⟨capture, fun i => β i, hopen, hinner, ?_, ?_, hβ, ?_⟩
  · intro i
    exact (β i).contMDiff
  · intro i x
    exact ⟨β.nonneg i x, β.le_one i x⟩
  · intro x hx
    simpa only [finsum_eq_sum_of_fintype] using β.sum_eq_one (subset_closure hx)

end LeanShared.FiniteSmoothCapturePartition

public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff BigOperators
namespace LeanShared.FiniteSmoothCapturePartition
variable {E M J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] [Fintype J]

/-- Canonical fixed-cover data, with empty capture on invalid covers. -/
structure Data (K : Set M) (v : J → Set M) where
  capture : Set M
  beta : J → M → ℝ
  open_capture : IsOpen capture
  smooth : ∀ i, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ (beta i)
  bounds : ∀ i x, 0 ≤ beta i x ∧ beta i x ≤ 1
  support : ∀ i, tsupport (beta i) ⊆ v i
  one : ∀ x ∈ capture, ∑ i, beta i x = 1
  reference : (∀ i, IsOpen (v i)) → K ⊆ ⋃ i, v i → K ⊆ capture

def data (K : Set M) (hK : IsCompact K) (v : J → Set M) : Data (E := E) K v :=
  Classical.choice (by
    classical
    by_cases hv : ∀ i, IsOpen (v i)
    · by_cases hcover : K ⊆ ⋃ i, v i
      · obtain ⟨O, β, ho, hk, hs, hb, hsup, hone⟩ := exists_partition (E := E) K hK v hv hcover
        exact ⟨⟨O, β, ho, hs, hb, hsup, hone, fun _ _ => hk⟩⟩
      · exact ⟨⟨∅, fun _ _ => 0, isOpen_empty, fun _ => contMDiff_const,
          fun _ _ => ⟨le_rfl, zero_le_one⟩,
          fun _ => by simp, fun _ hx => False.elim hx,
          fun _ hc => False.elim (hcover hc)⟩⟩
    · exact ⟨⟨∅, fun _ _ => 0, isOpen_empty, fun _ => contMDiff_const,
        fun _ _ => ⟨le_rfl, zero_le_one⟩,
        fun _ => by simp, fun _ hx => False.elim hx,
        fun ho _ => False.elim (hv ho)⟩⟩)

end LeanShared.FiniteSmoothCapturePartition
