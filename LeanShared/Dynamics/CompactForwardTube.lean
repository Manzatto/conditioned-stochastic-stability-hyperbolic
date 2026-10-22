module

public import LeanShared.Dynamics.IsolatingNeighborhood

/-! Compact first-exit sets entering a forward invariant open set have a
uniform entrance time. Their finite orbit tubes produce compact forward
invariant saturations. -/

public noncomputable section
open Set Function
namespace LeanShared.CompactForwardTube
variable {X : Type*} [TopologicalSpace X]

theorem exists_uniform_entrance (T : X → X) (continuous : Continuous T)
    {B U : Set X} (compact : IsCompact B) (openU : IsOpen U)
    (invariant : MapsTo T U U) (entrance : ∀ x ∈ B, ∃ n : ℕ, T^[n] x ∈ U) :
    ∃ N : ℕ, MapsTo (T^[N]) B U := by
  have monotone : Monotone (fun n : ℕ => T^[n] ⁻¹' U) := by
    apply monotone_nat_of_le_succ
    intro n x hx
    change T^[n+1] x ∈ U
    simpa only [iterate_succ_apply'] using invariant hx
  exact compact.elim_directed_cover (fun n : ℕ => T^[n] ⁻¹' U)
    (fun n => openU.preimage (continuous.iterate n))
    (fun x hx => mem_iUnion.mpr (entrance x hx)) monotone.directed_le

theorem exists_compact_saturation (T : X → X) (continuous : Continuous T)
    {C P B : Set X} (compactC : IsCompact C) (compactP : IsCompact P)
    (compactB : IsCompact B) (forwardC : MapsTo T C C)
    (exit : MapsTo T P (P ∪ B)) {N : ℕ} (capture : MapsTo (T^[N]) B C) :
    ∃ H : Set X, IsCompact H ∧ C ∪ P ⊆ H ∧ MapsTo T H H ∧
      H ⊆ C ∪ ⋃ n : ℕ, T^[n] '' P ∪ T^[n] '' B := by
  let H := C ∪ P ∪ ⋃ n ∈ Finset.range (N + 1), T^[n] '' B
  have compactH : IsCompact H := (compactC.union compactP).union
    ((Finset.range (N+1)).isCompact_biUnion
      (fun n _ => compactB.image (continuous.iterate n)))
  have contains : C ∪ P ⊆ H := subset_union_left
  refine ⟨H, compactH, contains, ?_, ?_⟩
  · intro x hx
    rcases hx with (inC | inP) | inTube
    · exact Or.inl (Or.inl (forwardC inC))
    · rcases exit inP with stays | leaves
      · exact Or.inl (Or.inr stays)
      · exact Or.inr (mem_iUnion₂.mpr ⟨0, Finset.mem_range.mpr (by omega),
          T x, leaves, rfl⟩)
    · obtain ⟨n, hn, y, hy, rfl⟩ := mem_iUnion₂.mp inTube
      have bound : n ≤ N := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn
      by_cases last : n = N
      · subst n
        exact Or.inl (Or.inl (forwardC (capture hy)))
      · apply Or.inr
        exact mem_iUnion₂.mpr ⟨n+1, Finset.mem_range.mpr (by omega), y, hy,
          iterate_succ_apply' T n y⟩
  · intro x hx
    rcases hx with (inC | inP) | inTube
    · exact Or.inl inC
    · exact Or.inr (mem_iUnion.mpr ⟨0, Or.inl ⟨x, inP, rfl⟩⟩)
    · obtain ⟨n, _, hn⟩ := mem_iUnion₂.mp inTube
      exact Or.inr (mem_iUnion.mpr ⟨n, Or.inr hn⟩)

end LeanShared.CompactForwardTube
