module

public import LeanShared.Dynamics.MarkovCodingProperties

/-! The actual full-interior subalphabet of a finite closed-classifier
partition.  Baire avoidance gives a dense set of points whose whole
integer orbit has literal labels in this subalphabet, and constructs
their actual bilateral graph paths.
-/

public noncomputable section
namespace LeanShared.FiniteClosedRefinement
open Set Function BilateralShadowingCoding MarkovFinitePathRealization
open scoped Topology
variable {X I : Type*} [MetricSpace X] [BaireSpace X] [Fintype I]

@[expose] def InteriorSymbol (classifiers : I → Set X) :=
  {status : I → Bool // (interior (atom classifiers status)).Nonempty}

instance interiorSymbolFintype (classifiers : I → Set X) : Fintype (InteriorSymbol classifiers) := by
  classical
  exact inferInstanceAs (Fintype {status : I → Bool // (interior (atom classifiers status)).Nonempty})

@[expose] def interiorRectangles (classifiers : I → Set X) (i : InteriorSymbol classifiers) : Set X :=
  atom classifiers i.val

@[expose] def fullOrbitInteriors (T : X ≃ₜ X) (classifiers : I → Set X) : Set X :=
  {x | ∀ k : ℤ, (T ^ k) x ∈ ⋃ status : I → Bool, interior (atom classifiers status)}

theorem fullOrbitInteriors_dense (T : X ≃ₜ X) (classifiers : I → Set X)
    (closed : ∀ i, IsClosed (classifiers i)) : Dense (fullOrbitInteriors T classifiers) := by
  let U := ⋃ status : I → Bool, interior (atom classifiers status)
  have openU : IsOpen U := isOpen_iUnion (fun _ => isOpen_interior)
  have denseU : Dense U := dense_iUnion_atom_interior classifiers closed
  have identity : fullOrbitInteriors T classifiers = ⋂ k : ℤ, (T ^ k) ⁻¹' U := by
    ext x
    simp only [fullOrbitInteriors, mem_ofPred_eq, mem_iInter, mem_preimage, U]
  rw [identity]
  exact dense_iInter_of_isOpen (fun k => openU.preimage (T ^ k).continuous)
    (fun k => denseU.preimage (T ^ k).isOpenMap)

omit [BaireSpace X] [Fintype I] in
theorem fullOrbitInteriors_path (T : X ≃ₜ X) (classifiers : I → Set X) (x : X)
    (inside : x ∈ fullOrbitInteriors T classifiers) :
    ∃ a : Path (Transition T (interiorRectangles classifiers)),
      ∀ k : ℤ, (T ^ k) x ∈ interior (interiorRectangles classifiers (a.val k)) := by
  classical
  choose labels membership using fun k : ℤ => mem_iUnion.mp (inside k)
  let label : ℤ → InteriorSymbol classifiers :=
    fun k => ⟨labels k, (T ^ k) x, membership k⟩
  have edge (k : ℤ) : Transition T (interiorRectangles classifiers) (label k) (label (k + 1)) := by
    refine ⟨(T ^ k) x, interior_subset (membership k), ?_⟩
    have step : (T ^ (k + 1)) x = T ((T ^ k) x) := by
      rw [add_comm k 1, zpow_add, zpow_one, Homeomorph.mul_apply]
    rw [← step]
    exact interior_subset (membership (k + 1))
  exact ⟨⟨label, edge⟩, membership⟩

omit [BaireSpace X] [Fintype I] in
theorem interiorSymbols_eq_of_point (classifiers : I → Set X)
    (i j : InteriorSymbol classifiers) (x : X)
    (left : x ∈ interiorRectangles classifiers i) (right : x ∈ interiorRectangles classifiers j) : i = j := by
  apply Subtype.ext
  by_contra different
  exact Set.disjoint_left.mp (atom_disjoint classifiers i.val j.val different) left right

end LeanShared.FiniteClosedRefinement
