module

public import LeanShared.Dynamics.LocalRectangleClassifiers

/-! Assemble the actual base-rectangle and stable/unstable classifiers.
Their finite membership atoms are local rectangles, because each hit
inherits one bracket coordinate and both hits mean membership in the
other base rectangle.  This supplies the geometric input to the proved
topological atom regularization.
-/

public noncomputable section
namespace LeanShared.FiniteClosedRefinement
open Set
variable {X I : Type*}

theorem mem_atom_iff (classifiers : I → Set X) (status : I → Bool) (x : X) :
    x ∈ atom classifiers status ↔ ∀ i, x ∈ classifiers i ↔ status i = true := by
  constructor
  · intro hx i
    have inside := mem_iInter.mp hx i
    by_cases state : status i = true
    · simp only [ite_eq_left state] at inside
      exact ⟨fun _ => state, fun _ => inside⟩
    · simp only [ite_eq_right state] at inside
      exact ⟨fun h => (inside h).elim, fun h => (state h).elim⟩
  · intro pattern
    apply mem_iInter.mpr
    intro i
    by_cases state : status i = true
    · simpa only [ite_eq_left state] using (pattern i).mpr state
    · simp only [ite_eq_right state]
      exact fun h => state ((pattern i).mp h)

theorem atom_membership_agrees (classifiers : I → Set X) (status : I → Bool) (x y : X)
    (hx : x ∈ atom classifiers status) (hy : y ∈ atom classifiers status) (i : I) :
    x ∈ classifiers i ↔ y ∈ classifiers i :=
  ((mem_atom_iff classifiers status x).mp hx i).trans
    (((mem_atom_iff classifiers status y).mp hy i).symm)

end LeanShared.FiniteClosedRefinement

namespace LeanShared.ExpansiveLocalProduct
open Set Function FiniteClosedRefinement
open scoped Topology
variable {X I : Type*} [MetricSpace X] {η : ℝ}
variable (bracket : NearbyPairs (X := X) η → X) (rectangles : I → Set X)
    (localRectangles : ∀ i, IsLocalRectangle bracket (rectangles i))
    (small : ∀ i, ∀ x ∈ rectangles i, ∀ y ∈ rectangles i, dist x y < η)

/-- Finite classifiers: base membership, stable hit, and unstable hit. -/
@[expose] def rectangleClassifiers : I ⊕ ((I × I) × Bool) → Set X
  | .inl i => rectangles i
  | .inr ((i, j), false) => stableClassifier bracket (rectangles i) (localRectangles i) (small i) (rectangles j)
  | .inr ((i, j), true) => unstableClassifier bracket (rectangles i) (localRectangles i) (small i) (rectangles j)

variable (idempotent : ∀ (x : X) (h : dist x x < η), bracket ⟨(x, x), h⟩ = x)
    (band : ConditionalBand bracket)
include idempotent band

theorem rectangleClassifiers_isClosed (continuous : Continuous bracket)
    (compact : ∀ i, IsCompact (rectangles i)) (k : I ⊕ ((I × I) × Bool)) :
    IsClosed (rectangleClassifiers bracket rectangles localRectangles small k) := by
  cases k with
  | inl i => exact (compact i).isClosed
  | inr k =>
    rcases k with ⟨⟨i, j⟩, kind⟩
    cases kind
    · exact stableClassifier_isClosed bracket (rectangles i) (localRectangles i) (small i)
        idempotent band continuous (compact i) (rectangles j) (compact j).isClosed
    · exact unstableClassifier_isClosed bracket (rectangles i) (localRectangles i) (small i)
        idempotent band continuous (compact i) (rectangles j) (compact j).isClosed

private theorem bothClassifier_iff (i j : I) (x : X) (inside : x ∈ rectangles i) :
    (x ∈ stableClassifier bracket (rectangles i) (localRectangles i) (small i) (rectangles j) ∧
      x ∈ unstableClassifier bracket (rectangles i) (localRectangles i) (small i) (rectangles j)) ↔
        x ∈ rectangles j := by
  change x ∈ stableClassifier bracket (rectangles i) (localRectangles i) (small i) (rectangles j) ∩
    unstableClassifier bracket (rectangles i) (localRectangles i) (small i) (rectangles j) ↔ _
  rw [classifiers_inter_eq bracket (rectangles i) (localRectangles i) (small i) idempotent band
    (rectangles j) (localRectangles j)]
  simp only [mem_inter_iff, inside, true_and]

/-- The exact finite classifier atoms are actual local rectangles. -/
theorem rectangleAtom_isLocalRectangle (cover : (⋃ i, rectangles i) = univ)
    (status : (I ⊕ ((I × I) × Bool)) → Bool) :
    IsLocalRectangle bracket (atom (rectangleClassifiers bracket rectangles localRectangles small) status) := by
  intro x hx y hy hxy
  let classifiers := rectangleClassifiers bracket rectangles localRectangles small
  have agrees (k : I ⊕ ((I × I) × Bool)) : x ∈ classifiers k ↔ y ∈ classifiers k :=
    atom_membership_agrees classifiers status x y hx hy k
  have inside : x ∈ ⋃ i, rectangles i := cover.symm ▸ mem_univ x
  obtain ⟨i, hxi⟩ := mem_iUnion.mp inside
  have hyi : y ∈ rectangles i := (agrees (.inl i)).mp hxi
  let z := bracket ⟨(x, y), hxy⟩
  have hzi : z ∈ rectangles i := localRectangles i x hxi y hyi hxy
  have baseAgrees (j : I) : z ∈ rectangles j ↔ x ∈ rectangles j := by
    have stable := stableClassifier_inherit bracket (rectangles i) (localRectangles i) (small i)
      idempotent band (rectangles j) x y hxi hyi hxy
    have unstable := (unstableClassifier_inherit bracket (rectangles i) (localRectangles i) (small i)
      idempotent band (rectangles j) x y hxi hyi hxy).trans (agrees (.inr ((i, j), true))).symm
    exact (bothClassifier_iff bracket rectangles localRectangles small idempotent band i j z hzi).symm.trans
      ((and_congr stable unstable).trans
        (bothClassifier_iff bracket rectangles localRectangles small idempotent band i j x hxi))
  have pattern (k : I ⊕ ((I × I) × Bool)) : z ∈ classifiers k ↔ x ∈ classifiers k := by
    cases k with
    | inl j => exact baseAgrees j
    | inr k =>
      rcases k with ⟨⟨a, b⟩, kind⟩
      by_cases hxa : x ∈ rectangles a
      · have hya : y ∈ rectangles a := (agrees (.inl a)).mp hxa
        cases kind
        · exact stableClassifier_inherit bracket (rectangles a) (localRectangles a) (small a)
            idempotent band (rectangles b) x y hxa hya hxy
        · exact (unstableClassifier_inherit bracket (rectangles a) (localRectangles a) (small a)
            idempotent band (rectangles b) x y hxa hya hxy).trans
              (agrees (.inr ((a, b), true))).symm
      · have hza : z ∉ rectangles a := fun hz => hxa ((baseAgrees a).mp hz)
        cases kind
        · exact iff_of_false
            (fun hit => hza (stableClassifier_subset bracket (rectangles a) (localRectangles a) (small a) _ hit))
            (fun hit => hxa (stableClassifier_subset bracket (rectangles a) (localRectangles a) (small a) _ hit))
        · exact iff_of_false
            (fun hit => hza (unstableClassifier_subset bracket (rectangles a) (localRectangles a) (small a) _ hit))
            (fun hit => hxa (unstableClassifier_subset bracket (rectangles a) (localRectangles a) (small a) _ hit))
  exact (mem_atom_iff classifiers status z).mpr
    (fun k => (pattern k).trans ((mem_atom_iff classifiers status x).mp hx k))

omit idempotent band in
/-- Every nonempty atom is contained in one of the original small rectangles. -/
theorem rectangleAtom_subset (cover : (⋃ i, rectangles i) = univ)
    (status : (I ⊕ ((I × I) × Bool)) → Bool)
    (nonempty : (atom (rectangleClassifiers bracket rectangles localRectangles small) status).Nonempty) :
    ∃ i, atom (rectangleClassifiers bracket rectangles localRectangles small) status ⊆ rectangles i := by
  obtain ⟨x, hx⟩ := nonempty
  have inside : x ∈ ⋃ i, rectangles i := cover.symm ▸ mem_univ x
  obtain ⟨i, hi⟩ := mem_iUnion.mp inside
  refine ⟨i, fun y hy => ?_⟩
  exact (atom_membership_agrees _ status x y hx hy (.inl i)).mp hi

omit idempotent band in
theorem rectangleAtom_small (cover : (⋃ i, rectangles i) = univ)
    (status : (I ⊕ ((I × I) × Bool)) → Bool) :
    ∀ x ∈ atom (rectangleClassifiers bracket rectangles localRectangles small) status,
      ∀ y ∈ atom (rectangleClassifiers bracket rectangles localRectangles small) status, dist x y < η := by
  intro x hx y hy
  obtain ⟨i, subset⟩ := rectangleAtom_subset bracket rectangles localRectangles small cover status ⟨x, hx⟩
  exact small i x (subset hx) y (subset hy)

end LeanShared.ExpansiveLocalProduct
