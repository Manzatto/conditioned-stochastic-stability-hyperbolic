module

public import LeanShared.Dynamics.FinitePastTrappingPotential
public import Mathlib.Topology.Order.Compact

/-! A compact isolated set with no external backward-trapped points has
arbitrarily small compact strict trapping neighborhoods. A finite weighted
past-distance potential constructs the neighborhood and proves one-step
strict trapping; no trapping-neighborhood existence is assumed. -/

public noncomputable section
open Set Function Metric
namespace LeanShared.CompactPastTrappingNeighborhood
variable {X : Type*} [MetricSpace X] [CompactSpace X]

theorem exists_neighborhood (T : X ≃ₜ X) {K O : Set X}
    (compact : IsCompact K) (nonempty : K.Nonempty)
    (core_inside : isolatedCore T K ⊆ interior K)
    (no_external_past : forwardTrapped T.symm K ⊆ isolatedCore T K)
    (openO : IsOpen O) (contains : isolatedCore T K ⊆ O) :
    ∃ D : Set X, IsCompact D ∧ isolatedCore T K ⊆ interior D ∧
      D ⊆ O ∩ interior K ∧ MapsTo T D (interior D) ∧
      isolatedCore T D = isolatedCore T K := by
  let safe := O ∩ interior K ∩ T ⁻¹' interior K
  have openSafe : IsOpen safe :=
    (openO.inter isOpen_interior).inter (isOpen_interior.preimage T.continuous)
  have pastSafe : forwardTrapped T.symm K ⊆ safe := by
    intro x hx
    have core := no_external_past hx
    exact ⟨⟨contains core, core_inside core⟩, core_inside (mapsTo_isolatedCore T K core)⟩
  have compactZero : IsCompact (finiteForwardCore T.symm K 0) :=
    compact.of_isClosed_subset (isClosed_finiteForwardCore T.symm.continuous compact.isClosed 0)
      (fun _ hx => hx 0 (le_refl _))
  obtain ⟨N, _positiveN, captured⟩ := exists_pos_tail_subset_open compactZero
    (fun n => isClosed_finiteForwardCore T.symm.continuous compact.isClosed n)
    (antitone_finiteForwardCore T.symm K) openSafe (by
      simpa only [iInter_finiteForwardCore] using pastSafe)
  let q := FinitePastTrappingPotential.potential T K N
  have continuousQ : Continuous q := FinitePastTrappingPotential.continuous T K N
  have nonnegativeQ (x : X) : 0 ≤ q x := FinitePastTrappingPotential.nonnegative T K N x
  have zeroSafe {x : X} (zero : q x = 0) : x ∈ safe :=
    captured ((FinitePastTrappingPotential.zero_iff T K compact.isClosed nonempty N x).mp zero)
  obtain ⟨a, positiveA, lower⟩ := openSafe.isClosed_compl.isCompact.exists_forall_le'
    continuousQ.continuousOn (a := (0 : ℝ)) (by
      intro x outside
      exact lt_of_le_of_ne (nonnegativeQ x) (fun zero => outside (zeroSafe zero.symm)))
  let δ := a / 2
  have positive : 0 < δ := half_pos positiveA
  let D := {x : X | q x ≤ δ}
  have safeD : D ⊆ safe := by
    intro x hx
    by_contra outside
    have minimum := lower x outside
    change q x ≤ a / 2 at hx
    linarith
  have strict_sublevel : {x : X | q x < δ} ⊆ interior D :=
    interior_maximal (fun _ hx => show q _ ≤ δ from hx.le)
      (isOpen_lt continuousQ continuous_const)
  have coreD : isolatedCore T K ⊆ interior D := by
    intro x hx
    apply strict_sublevel
    have zero : q x = 0 :=
      (FinitePastTrappingPotential.zero_iff T K compact.isClosed nonempty N x).mpr
        (fun n _ => hx.2 n)
    change q x < δ
    rw [zero]
    exact positive
  refine ⟨D, (isClosed_le continuousQ continuous_const).isCompact, coreD,
    fun x hx => (safeD hx).1, ?_, ?_⟩
  · intro x hx
    apply strict_sublevel
    have contracted : q (T x) ≤ (1 / 2 : ℝ) * q x :=
      FinitePastTrappingPotential.contracts T K N (interior_subset (safeD hx).2)
    change q x ≤ δ at hx
    change q (T x) < δ
    linarith
  · apply Subset.antisymm
    · intro x hx
      exact ⟨fun n => interior_subset (safeD (hx.1 n)).1.2,
        fun n => interior_subset (safeD (hx.2 n)).1.2⟩
    · intro x hx
      exact ⟨fun n => interior_subset (coreD (iterate_mem_isolatedCore T K hx n)),
        fun n => interior_subset (coreD (iterate_symm_mem_isolatedCore T K hx n))⟩

end LeanShared.CompactPastTrappingNeighborhood
