module

public import LeanShared.Dynamics.ClosedClassifierInteriorPaths
public import LeanShared.Dynamics.HyperbolicBasicSet

/-! Literal base mixing produces eventual connections in the actual
graph on classifier atoms with nonempty relative interior.  The proof
uses dense whole-orbit interior itineraries, rather than attributing
mixing to an arbitrary symbolic extension.
-/

public noncomputable section
namespace LeanShared.FiniteClosedRefinement
open Set Function BilateralShadowingCoding MarkovFinitePathRealization
open scoped Topology
variable {X I : Type*} [MetricSpace X] [BaireSpace X] [Fintype I]

theorem mixing_interior_graph_connections (T : X ≃ₜ X) (classifiers : I → Set X)
    (closed : ∀ i, IsClosed (classifiers i))
    (mixing : HyperbolicBasicSet.MixingOn T univ)
    (i j : InteriorSymbol classifiers) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ a : Path (Transition T (interiorRectangles classifiers)),
      a.val 0 = i ∧ a.val (n : ℤ) = j := by
  obtain ⟨N, hits⟩ := mixing (interior (interiorRectangles classifiers i))
    (interior (interiorRectangles classifiers j)) isOpen_interior isOpen_interior
    (by simpa only [univ_inter, interiorRectangles] using i.property)
    (by simpa only [univ_inter, interiorRectangles] using j.property)
  refine ⟨N, fun n large => ?_⟩
  obtain ⟨x, inside, endpoint⟩ := hits n large
  let U := interior (interiorRectangles classifiers i) ∩
    (T : X → X)^[n] ⁻¹' interior (interiorRectangles classifiers j)
  have openU : IsOpen U := isOpen_interior.inter (isOpen_interior.preimage (T.continuous.iterate n))
  have nonemptyU : U.Nonempty := ⟨x, inside.2, endpoint⟩
  obtain ⟨y, good, endpoints⟩ := (fullOrbitInteriors_dense T classifiers closed).exists_mem_open openU nonemptyU
  obtain ⟨a, itinerary⟩ := fullOrbitInteriors_path T classifiers y good
  refine ⟨a, ?_, ?_⟩
  · apply interiorSymbols_eq_of_point classifiers _ _ y
    · simpa only [zpow_zero, Homeomorph.one_apply] using interior_subset (itinerary 0)
    · exact interior_subset endpoints.1
  · apply interiorSymbols_eq_of_point classifiers _ _ ((T : X → X)^[n] y)
    · simpa only [zpow_natCast, DiffeomorphismIterates.coe_pow] using interior_subset (itinerary (n : ℤ))
    · exact interior_subset endpoints.2

theorem mixing_interior_graph_common_connections (T : X ≃ₜ X) (classifiers : I → Set X)
    (closed : ∀ i, IsClosed (classifiers i))
    (mixing : HyperbolicBasicSet.MixingOn T univ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ i j : InteriorSymbol classifiers,
      ∃ a : Path (Transition T (interiorRectangles classifiers)), a.val 0 = i ∧ a.val (n : ℤ) = j := by
  classical
  choose waiting connections using mixing_interior_graph_connections T classifiers closed mixing
  let N := Finset.univ.sup (fun p : InteriorSymbol classifiers × InteriorSymbol classifiers => waiting p.1 p.2)
  refine ⟨N, fun n large i j => connections i j n ?_⟩
  exact (Finset.le_sup (s := Finset.univ) (f := fun p : InteriorSymbol classifiers × InteriorSymbol classifiers =>
    waiting p.1 p.2) (Finset.mem_univ (i, j))).trans large

end LeanShared.FiniteClosedRefinement
