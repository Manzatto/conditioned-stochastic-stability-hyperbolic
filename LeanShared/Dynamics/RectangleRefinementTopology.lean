module

public import LeanShared.Dynamics.BasicHyperbolicProperRectangles
public import Mathlib.Topology.Baire.Lemmas

/-! Topology of the four-way refinement: hit classifiers are closed
compact bracket images.  Finite Boolean atoms regularize to a cover by
proper closed sets with pairwise disjoint interiors and boundary-only
overlaps.  Rectangle closure is supplied by LocalBracketInterior when
these atoms are applied to the actual common bracket.
-/

public noncomputable section
namespace LeanShared.RectangleFourWayRefinement
open Set Function
variable {X : Type*} (bracket : X × X → X)
    (idempotent : ∀ x, bracket (x, x) = x)
    (band : ∀ x y u v, bracket (bracket (x, y), bracket (u, v)) = bracket (x, v))

include idempotent band

theorem stableHit_eq_image (S : Set X) :
    {x | StableHit bracket S x} = bracket '' (S ×ˢ univ) := by
  ext x
  constructor
  · rintro ⟨z, hz, hit⟩
    have identity := band x z x x
    rw [hit, idempotent x] at identity
    exact ⟨(z, x), ⟨hz, mem_univ x⟩, identity⟩
  · rintro ⟨⟨z, w⟩, ⟨hz, _⟩, rfl⟩
    exact ⟨z, hz, (bracket_left bracket idempotent band z w z).trans (idempotent z)⟩

theorem unstableHit_eq_image (S : Set X) :
    {x | UnstableHit bracket S x} = bracket '' (univ ×ˢ S) := by
  ext x
  constructor
  · rintro ⟨z, hz, hit⟩
    have identity := band x x z x
    rw [hit, idempotent x] at identity
    exact ⟨(x, z), ⟨mem_univ x, hz⟩, identity⟩
  · rintro ⟨⟨w, z⟩, ⟨_, hz⟩, rfl⟩
    exact ⟨z, hz, (bracket_right bracket idempotent band w z z).trans (idempotent z)⟩

theorem stableHit_isClosed [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (continuous : Continuous bracket) (S : Set X) (closed : IsClosed S) :
    IsClosed {x | StableHit bracket S x} := by
  rw [stableHit_eq_image bracket idempotent band]
  exact ((closed.isCompact.prod isCompact_univ).image continuous).isClosed

theorem unstableHit_isClosed [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (continuous : Continuous bracket) (S : Set X) (closed : IsClosed S) :
    IsClosed {x | UnstableHit bracket S x} := by
  rw [unstableHit_eq_image bracket idempotent band]
  exact ((isCompact_univ.prod closed.isCompact).image continuous).isClosed

end LeanShared.RectangleFourWayRefinement

namespace LeanShared.FiniteClosedRefinement
open Set Function
open scoped Topology
variable {X I : Type*} [TopologicalSpace X]

/-- Exact finite membership atoms for a family of closed classifiers. -/
@[expose] def atom (classifiers : I → Set X) (status : I → Bool) : Set X :=
  ⋂ i, if status i = true then classifiers i else (classifiers i)ᶜ

omit [TopologicalSpace X] in
theorem atom_disjoint (classifiers : I → Set X) (status other : I → Bool)
    (different : status ≠ other) : Disjoint (atom classifiers status) (atom classifiers other) := by
  classical
  obtain ⟨i, atIndex⟩ : ∃ i, status i ≠ other i :=
    not_forall.mp (fun all => different (funext all))
  apply Set.disjoint_left.mpr
  intro x hx hy
  have first := mem_iInter.mp hx i
  have second := mem_iInter.mp hy i
  cases h : status i <;> cases h' : other i <;> simp_all

/-- Away from the finite classifier frontiers, a point is interior to its atom. -/
theorem outside_frontiers_mem_interior [Finite I] (classifiers : I → Set X) (x : X)
    (outside : ∀ i, x ∉ frontier (classifiers i)) :
    ∃ status : I → Bool, x ∈ interior (atom classifiers status) := by
  classical
  let status : I → Bool := fun i => decide (x ∈ classifiers i)
  refine ⟨status, ?_⟩
  rw [atom, interior_iInter_of_finite]
  apply mem_iInter.mpr
  intro i
  by_cases inside : x ∈ classifiers i
  · simp only [status, decide_eq_true inside, ite_true]
    exact (mem_interior_iff_notMem_frontier inside).mpr (outside i)
  · simp only [status, decide_eq_false inside, ite_eq_right (by decide : (false : Bool) ≠ true)]
    exact (mem_interior_iff_notMem_frontier (show x ∈ (classifiers i)ᶜ from inside)).mpr
      (by simpa only [frontier_compl] using outside i)

theorem dense_iUnion_atom_interior [Fintype I] [BaireSpace X]
    (classifiers : I → Set X) (closed : ∀ i, IsClosed (classifiers i)) :
    Dense (⋃ status : I → Bool, interior (atom classifiers status)) := by
  have dense : Dense (⋂ i, (frontier (classifiers i))ᶜ) :=
    dense_iInter_of_isOpen (fun _ => isClosed_frontier.isOpen_compl)
      (fun i => interior_eq_empty_iff_dense_compl.mp (interior_frontier (closed i)))
  apply dense.mono
  intro x hx
  obtain ⟨status, inside⟩ := outside_frontiers_mem_interior classifiers x
    (fun i => mem_iInter.mp hx i)
  exact mem_iUnion.mpr ⟨status, inside⟩

/-- The proper regularizations of all atoms cover the whole space. -/
theorem regularized_cover [Fintype I] [BaireSpace X]
    (classifiers : I → Set X) (closed : ∀ i, IsClosed (classifiers i)) :
    (⋃ status : I → Bool, closure (interior (atom classifiers status))) = univ := by
  rw [← closure_iUnion_of_finite]
  exact (dense_iUnion_atom_interior classifiers closed).closure_eq

/-- Closing disjoint atom interiors leaves pairwise disjoint interiors. -/
theorem regularized_interiors_disjoint (classifiers : I → Set X) (status other : I → Bool)
    (different : status ≠ other) :
    Disjoint (interior (closure (interior (atom classifiers status))))
      (interior (closure (interior (atom classifiers other)))) := by
  have original := (atom_disjoint classifiers status other different).mono interior_subset interior_subset
  have left := original.closure_left isOpen_interior
  have smaller := left.mono_left interior_subset
  exact (smaller.closure_right isOpen_interior).mono_right interior_subset

/-- Distinct regularized atoms meet only on both boundaries. -/
theorem regularized_overlap_boundary (classifiers : I → Set X) (status other : I → Bool)
    (different : status ≠ other) :
    closure (interior (atom classifiers status)) ∩ closure (interior (atom classifiers other)) =
      frontier (closure (interior (atom classifiers status))) ∩
        frontier (closure (interior (atom classifiers other))) := by
  have original := (atom_disjoint classifiers status other different).mono interior_subset interior_subset
  have leftDisjoint := ((original.closure_right isOpen_interior).mono_right interior_subset).closure_left
    isOpen_interior
  have rightDisjoint := ((original.closure_left isOpen_interior).mono_left interior_subset).closure_right
    isOpen_interior
  rw [isClosed_closure.frontier_eq, isClosed_closure.frontier_eq]
  ext x
  constructor
  · rintro ⟨left, right⟩
    exact ⟨⟨left, fun interior => Set.disjoint_left.mp rightDisjoint interior right⟩,
      ⟨right, fun interior => Set.disjoint_left.mp leftDisjoint left interior⟩⟩
  · rintro ⟨⟨left, _⟩, ⟨right, _⟩⟩
    exact ⟨left, right⟩

end LeanShared.FiniteClosedRefinement
