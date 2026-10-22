module

public import LeanShared.Dynamics.MarkovCodingPeriodicFibers
public import LeanShared.Dynamics.RectangleRefinementTopology

/-! The exact closed-classifier origin of raw rectangles is retained in
a finite, enumeration-independent form.  Multiple time-zero symbols can
code a point only on the finite classifier boundary union, a closed set
with empty interior. -/

public noncomputable section
namespace LeanShared.MarkovFinitePathRealization
open Set Function BilateralShadowingCoding FiniteClosedRefinement
open scoped Topology
variable {X I K : Type*} [MetricSpace X]

@[expose] def HasClosedClassifierOrigin (rectangles : I → Set X) : Prop :=
  ∃ d : ℕ, ∃ classifiers : Fin d → Set X, (∀ j, IsClosed (classifiers j)) ∧
    ∃ statuses : I ≃ (Fin d → Bool), ∀ i, rectangles i = atom classifiers (statuses i)

theorem raw_atoms_have_closed_classifier_origin [Fintype K] (classifiers : K → Set X)
    (closed : ∀ j, IsClosed (classifiers j)) :
    HasClosedClassifierOrigin (fun status : K → Bool => atom classifiers status) := by
  classical
  let e := Fintype.equivFin K
  let C : Fin (Fintype.card K) → Set X := fun j => classifiers (e.symm j)
  let statuses : (K → Bool) ≃ (Fin (Fintype.card K) → Bool) :=
    { toFun := fun status j => status (e.symm j)
      invFun := fun status j => status (e j)
      left_inv := fun _ => by ext j; simp only [Equiv.symm_apply_apply]
      right_inv := fun _ => by ext j; simp only [Equiv.apply_symm_apply] }
  refine ⟨Fintype.card K, C, fun j => closed _, statuses, fun status => ?_⟩
  ext x
  simp only [atom, mem_iInter]
  constructor
  · exact fun h j => h (e.symm j)
  · intro h j
    have atIndex := h (e j)
    change x ∈ (if status (e.symm (e j)) = true then classifiers (e.symm (e j))
      else (classifiers (e.symm (e j)))ᶜ) at atIndex
    simpa only [Equiv.symm_apply_apply] using atIndex

theorem atom_closure_overlap_frontier (classifiers : K → Set X) (s t : K → Bool)
    (different : s ≠ t) (x : X) (left : x ∈ closure (atom classifiers s))
    (right : x ∈ closure (atom classifiers t)) : ∃ i, x ∈ frontier (classifiers i) := by
  classical
  obtain ⟨i, distinct⟩ : ∃ i, s i ≠ t i := not_forall.mp (fun h => different (funext h))
  have first : atom classifiers s ⊆ if s i = true then classifiers i else (classifiers i)ᶜ :=
    iInter_subset _ i
  have second : atom classifiers t ⊆ if t i = true then classifiers i else (classifiers i)ᶜ :=
    iInter_subset _ i
  have hleft := closure_mono first left
  have hright := closure_mono second right
  refine ⟨i, ?_⟩
  rw [frontier_eq_closure_inter_closure]
  cases hs : s i <;> cases ht : t i <;> simp_all

theorem classifier_coding_boundary [BaireSpace X] (T : X ≃ₜ X) (rectangles : I → Set X)
    (origin : HasClosedClassifierOrigin rectangles)
    (code : Path (Transition T rectangles) → X)
    (windows : ∀ a radius, code a ∈ closure (itineraryWindow T rectangles a.val radius)) :
    ∃ boundary : Set X, IsClosed boundary ∧ interior boundary = ∅ ∧
      ∀ a b, code a = code b → a.val 0 ≠ b.val 0 → code a ∈ boundary := by
  obtain ⟨d, C, closed, statuses, atoms⟩ := origin
  let boundary := ⋃ i, frontier (C i)
  have closedBoundary : IsClosed boundary := isClosed_iUnion_of_finite (fun _ => isClosed_frontier)
  have denseOutside : Dense boundaryᶜ := by
    rw [show boundaryᶜ = ⋂ i, (frontier (C i))ᶜ by simp only [boundary, compl_iUnion]]
    exact dense_iInter_of_isOpen (fun _ => isClosed_frontier.isOpen_compl)
      (fun i => interior_eq_empty_iff_dense_compl.mp (interior_frontier (closed i)))
  refine ⟨boundary, closedBoundary, interior_eq_empty_iff_dense_compl.mpr denseOutside, ?_⟩
  intro a b samePoint different
  have first := closed_window_coordinate T rectangles a.val 0 (code a) (windows a 0) 0 (by omega) (by omega)
  have second := closed_window_coordinate T rectangles b.val 0 (code b) (windows b 0) 0 (by omega) (by omega)
  simp only [zpow_zero, Homeomorph.one_apply] at first second
  rw [atoms] at first second
  rw [← samePoint] at second
  obtain ⟨i, inside⟩ := atom_closure_overlap_frontier C _ _
    (fun equal => different (statuses.injective equal)) (code a) first second
  exact mem_iUnion.mpr ⟨i, inside⟩

end LeanShared.MarkovFinitePathRealization
