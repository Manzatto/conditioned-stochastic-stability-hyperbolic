module

public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Trapped sets in a compact isolating neighborhood

These results use a homeomorphism and a compact set, without hyperbolicity.
The isolated core is expressed using forward and backward natural-number iterates.
-/

@[expose] public section

open Set Function

namespace LeanShared

variable {X : Type*}

/-- Points whose entire forward orbit stays in `K`. -/
def forwardTrapped (f : X → X) (K : Set X) : Set X :=
  {x | ∀ n : ℕ, f^[n] x ∈ K}

/-- Points whose forward and backward orbits stay in `K`. -/
def isolatedCore [TopologicalSpace X] (T : X ≃ₜ X) (K : Set X) : Set X :=
  forwardTrapped T K ∩ forwardTrapped T.symm K

theorem forwardTrapped_subset (f : X → X) (K : Set X) :
    forwardTrapped f K ⊆ K := fun _ hx => hx 0

theorem mapsTo_forwardTrapped (f : X → X) (K : Set X) :
    MapsTo f (forwardTrapped f K) (forwardTrapped f K) := by
  intro x hx n
  simpa only [← iterate_succ_apply] using hx (n + 1)

theorem mem_forwardTrapped_of_mem_of_image_mem {f : X → X} {K : Set X}
    {x : X} (hx : x ∈ K) (hfx : f x ∈ forwardTrapped f K) :
    x ∈ forwardTrapped f K := by
  intro n
  cases n with
  | zero => exact hx
  | succ n => simpa only [iterate_succ_apply] using hfx n

variable [TopologicalSpace X]

theorem isClosed_forwardTrapped {f : X → X} {K : Set X}
    (hf : Continuous f) (hK : IsClosed K) : IsClosed (forwardTrapped f K) := by
  have heq : forwardTrapped f K = ⋂ n : ℕ, f^[n] ⁻¹' K := by
    ext x
    simp [forwardTrapped]
  rw [heq]
  exact isClosed_iInter fun n => hK.preimage (hf.iterate n)

theorem isCompact_forwardTrapped [T2Space X] {f : X → X} {K : Set X}
    (hf : Continuous f) (hK : IsCompact K) : IsCompact (forwardTrapped f K) :=
  hK.of_isClosed_subset (isClosed_forwardTrapped hf hK.isClosed)
    (forwardTrapped_subset f K)

theorem mapsTo_isolatedCore (T : X ≃ₜ X) (K : Set X) :
    MapsTo T (isolatedCore T K) (isolatedCore T K) := by
  intro x hx
  refine ⟨mapsTo_forwardTrapped T K hx.1, ?_⟩
  intro n
  cases n with
  | zero => simpa only [iterate_zero, iterate_one, id_eq] using hx.1 1
  | succ n => simpa only [iterate_succ_apply, T.symm_apply_apply] using hx.2 n

theorem mapsTo_isolatedCore_symm (T : X ≃ₜ X) (K : Set X) :
    MapsTo T.symm (isolatedCore T K) (isolatedCore T K) := by
  intro x hx
  refine ⟨?_, mapsTo_forwardTrapped T.symm K hx.2⟩
  intro n
  cases n with
  | zero => simpa only [iterate_zero, iterate_one, id_eq] using hx.2 1
  | succ n => simpa only [iterate_succ_apply, T.apply_symm_apply] using hx.1 n

theorem iterate_mem_isolatedCore (T : X ≃ₜ X) (K : Set X)
    {x : X} (hx : x ∈ isolatedCore T K) (n : ℕ) :
    (T : X → X)^[n] x ∈ isolatedCore T K := by
  induction n with
  | zero => exact hx
  | succ n ih =>
      simpa only [iterate_succ_apply'] using mapsTo_isolatedCore T K ih

theorem iterate_symm_mem_isolatedCore (T : X ≃ₜ X) (K : Set X)
    {x : X} (hx : x ∈ isolatedCore T K) (n : ℕ) :
    (T.symm : X → X)^[n] x ∈ isolatedCore T K := by
  induction n with
  | zero => exact hx
  | succ n ih =>
      simpa only [iterate_succ_apply'] using mapsTo_isolatedCore_symm T K ih

/-- Forward images of the forward-trapped set form a decreasing sequence. -/
theorem antitone_image_forwardTrapped (T : X ≃ₜ X) (K : Set X) :
    Antitone (fun n : ℕ => (T : X → X)^[n] '' forwardTrapped T K) := by
  apply antitone_nat_of_succ_le
  intro n x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨T y, mapsTo_forwardTrapped T K hy, iterate_succ_apply T n y |>.symm⟩

/-- The intersection of the stable tails is exactly the two-sided isolated core. -/
theorem iInter_image_forwardTrapped (T : X ≃ₜ X) (K : Set X) :
    (⋂ n : ℕ, (T : X → X)^[n] '' forwardTrapped T K) = isolatedCore T K := by
  ext x
  constructor
  · intro hx
    have hxn := mem_iInter.mp hx
    refine ⟨by simpa using hxn 0, ?_⟩
    intro n
    obtain ⟨y, hy, heq⟩ := hxn n
    have hinv := T.left_inv.iterate n y
    change (T.symm : X → X)^[n] ((T : X → X)^[n] y) = y at hinv
    rw [heq] at hinv
    rw [hinv]
    exact forwardTrapped_subset T K hy
  · intro hx
    apply mem_iInter.mpr
    intro n
    exact ⟨(T.symm : X → X)^[n] x,
      (iterate_symm_mem_isolatedCore T K hx n).1, T.right_inv.iterate n x⟩

/-- A decreasing closed family inside a compact set eventually lies in any open
set containing its intersection. -/
theorem exists_pos_tail_subset_open [T2Space X] {C : ℕ → Set X} {U : Set X}
    (hC : IsCompact (C 0)) (hclosed : ∀ n, IsClosed (C n))
    (hanti : Antitone C) (hU : IsOpen U) (hcore : (⋂ n, C n) ⊆ U) :
    ∃ N : ℕ, 0 < N ∧ C N ⊆ U := by
  have hdis : Disjoint (C 0 \ U) (⋂ n, C n) := by
    apply disjoint_left.mpr
    intro x hx hxi
    exact hx.2 (hcore hxi)
  obtain ⟨n, hn⟩ := (hC.diff hU).elim_directed_family_closed C hclosed hdis
    (fun i j => ⟨max i j, hanti (le_max_left i j), hanti (le_max_right i j)⟩)
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  intro x hx
  by_contra hxU
  exact disjoint_left.mp hn ⟨hanti (Nat.zero_le _) hx, hxU⟩
    (hanti (Nat.le_succ n) hx)

/-- Stable tails approach the isolated core, in the neighborhood sense. -/
theorem exists_pos_stable_tail_subset [T2Space X] (T : X ≃ₜ X) {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hcore : isolatedCore T K ⊆ U) :
    ∃ N : ℕ, 0 < N ∧ (T : X → X)^[N] '' forwardTrapped T K ⊆ U := by
  apply exists_pos_tail_subset_open
  · simpa using isCompact_forwardTrapped T.continuous hK
  · intro n
    exact ((isCompact_forwardTrapped T.continuous hK).image
      (T.continuous.iterate n)).isClosed
  · exact antitone_image_forwardTrapped T K
  · exact hU
  · simpa only [iInter_image_forwardTrapped] using hcore

end LeanShared
