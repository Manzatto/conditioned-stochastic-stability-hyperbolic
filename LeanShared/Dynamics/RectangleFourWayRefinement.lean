module

public import LeanShared.Dynamics.RectangleBracketAlgebra

/-! The finite four-way stable/unstable splitting in Bowen's rectangle
refinement.  Every cell, and every intersection of cells, is closed under
the proved bracket algebra.  The cell with both hits is exactly the
intersecting rectangle.  No Markov-transition assertion is assumed.
-/

public noncomputable section
namespace LeanShared.RectangleFourWayRefinement
open Set
variable {X : Type*}

/-- Closure under a local rectangle bracket. -/
@[expose] def IsRectangle (bracket : X × X → X) (S : Set X) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, bracket (x, y) ∈ S

/-- The local stable slice through `x` meets `S`. -/
@[expose] def StableHit (bracket : X × X → X) (S : Set X) (x : X) : Prop :=
  ∃ z ∈ S, bracket (x, z) = z

/-- The local unstable slice through `x` meets `S`. -/
@[expose] def UnstableHit (bracket : X × X → X) (S : Set X) (x : X) : Prop :=
  ∃ z ∈ S, bracket (z, x) = z

/-- The four choices of whether the stable and unstable slices meet `S`. -/
@[expose] def cell (bracket : X × X → X) (S : Set X) (status : Bool × Bool) : Set X :=
  {x | (StableHit bracket S x ↔ status.1 = true) ∧
    (UnstableHit bracket S x ↔ status.2 = true)}

variable (bracket : X × X → X)
    (idempotent : ∀ x, bracket (x, x) = x)
    (band : ∀ x y u v, bracket (bracket (x, y), bracket (u, v)) = bracket (x, v))

include idempotent band

theorem bracket_left (x y z : X) : bracket (bracket (x, y), z) = bracket (x, z) := by
  simpa only [idempotent z] using band x y z z

theorem bracket_right (x y z : X) : bracket (z, bracket (x, y)) = bracket (z, y) := by
  simpa only [idempotent z] using band z z x y

theorem stableHit_bracket (S : Set X) (x y : X) :
    StableHit bracket S (bracket (x, y)) ↔ StableHit bracket S x := by
  simp only [StableHit, bracket_left bracket idempotent band]

theorem unstableHit_bracket (S : Set X) (x y : X) :
    UnstableHit bracket S (bracket (x, y)) ↔ UnstableHit bracket S y := by
  simp only [UnstableHit, bracket_right bracket idempotent band]

/-- All four pieces are rectangles, including pieces defined by misses. -/
theorem cell_rectangle (S : Set X) (status : Bool × Bool) :
    IsRectangle bracket (cell bracket S status) := by
  intro x hx y hy
  exact ⟨(stableHit_bracket bracket idempotent band S x y).trans hx.1,
    (unstableHit_bracket bracket idempotent band S x y).trans hy.2⟩

omit idempotent band in
theorem cell_cover (S : Set X) : (⋃ status : Bool × Bool, cell bracket S status) = univ := by
  classical
  apply eq_univ_of_forall
  intro x
  refine mem_iUnion.mpr ⟨(decide (StableHit bracket S x), decide (UnstableHit bracket S x)), ?_⟩
  simp only [cell, mem_ofPred_eq, decide_eq_true_eq, iff_self, and_self]

omit idempotent band in
theorem cell_disjoint (S : Set X) (i j : Bool × Bool) (different : i ≠ j) :
    Disjoint (cell bracket S i) (cell bracket S j) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have sameStable := hx.1.symm.trans hy.1
  have sameUnstable := hx.2.symm.trans hy.2
  rcases i with ⟨is, iu⟩
  rcases j with ⟨js, ju⟩
  cases is <;> cases iu <;> cases js <;> cases ju <;> simp_all

/-- For a rectangle, meeting both slices is equivalent to membership. -/
theorem both_hits_iff (S : Set X) (rectangle : IsRectangle bracket S) (x : X) :
    StableHit bracket S x ∧ UnstableHit bracket S x ↔ x ∈ S := by
  constructor
  · rintro ⟨⟨a, ha, stable⟩, ⟨b, hb, unstable⟩⟩
    have same := band x a b x
    rw [stable, unstable, idempotent x] at same
    exact same ▸ rectangle a ha b hb
  · intro inside
    exact ⟨⟨x, inside, idempotent x⟩, ⟨x, inside, idempotent x⟩⟩

theorem both_cell_eq (S : Set X) (rectangle : IsRectangle bracket S) :
    cell bracket S (true, true) = S := by
  ext x
  simpa only [cell, mem_ofPred_eq, Prod.fst, Prod.snd, iff_true] using
    both_hits_iff bracket idempotent band S rectangle x

omit idempotent band in
theorem IsRectangle.iInter {I : Sort*} (S : I → Set X)
    (rectangles : ∀ i, IsRectangle bracket (S i)) : IsRectangle bracket (⋂ i, S i) := by
  intro x hx y hy
  exact mem_iInter.mpr (fun i => rectangles i x (mem_iInter.mp hx i) y (mem_iInter.mp hy i))

/-- Any simultaneous finite hit/miss itinerary is still a rectangle. -/
theorem refined_rectangle {I : Sort*} (S : I → Set X) (status : I → Bool × Bool) :
    IsRectangle bracket (⋂ i, cell bracket (S i) (status i)) :=
  IsRectangle.iInter bracket _ (fun i => cell_rectangle bracket idempotent band (S i) (status i))

omit idempotent band in
theorem refined_cover {I : Sort*} (S : I → Set X) :
    (⋃ status : I → Bool × Bool, ⋂ i, cell bracket (S i) (status i)) = univ := by
  classical
  apply eq_univ_of_forall
  intro x
  let status : I → Bool × Bool := fun i =>
    (decide (StableHit bracket (S i) x), decide (UnstableHit bracket (S i) x))
  refine mem_iUnion.mpr ⟨status, mem_iInter.mpr (fun i => ?_)⟩
  simp only [status, cell, mem_ofPred_eq, decide_eq_true_eq, iff_self, and_self]

omit idempotent band in
theorem refined_disjoint {I : Sort*} (S : I → Set X)
    (status other : I → Bool × Bool) (different : status ≠ other) :
    Disjoint (⋂ i, cell bracket (S i) (status i)) (⋂ i, cell bracket (S i) (other i)) := by
  classical
  obtain ⟨i, differentAt⟩ : ∃ i, status i ≠ other i :=
    not_forall.mp (fun all => different (funext all))
  exact (cell_disjoint bracket (S i) (status i) (other i) differentAt).mono
    (iInter_subset _ i) (iInter_subset _ i)

end LeanShared.RectangleFourWayRefinement
