module

public import LeanShared.Analysis.CylinderPrincipalCoefficient

/-! Literal finite-word cylinders and survivors on the actual state space.
The cover is generated from a single finite open state-space cover; it is
not an arbitrary family of word-dependent sets. -/

@[expose] public noncomputable section
open Set
open scoped Topology
namespace LeanShared.FiniteWordCylinders
open CylinderPrincipalCoefficient
variable {G X J : Type*} [TopologicalSpace G] [TopologicalSpace X]

/-- All chronological prefixes through the terminal time remain in K. -/
def survivors (F : G → X → X) (K : Set X) (N : ℕ) : Set ((Fin N → G) × X) :=
  {z | ∀ j : Fin (N + 1), prefixOrbit F z.1 j.val z.2 ∈ K}

/-- A label at each actual prefix chooses one member of the base cover. -/
def cylinder (F : G → X → X) (cover : J → Set X) (N : ℕ)
    (labels : Fin (N + 1) → J) : Set ((Fin N → G) × X) :=
  {z | ∀ j : Fin (N + 1), prefixOrbit F z.1 j.val z.2 ∈ cover (labels j)}

theorem survivors_closed (F : G → X → X)
    (hF : Continuous (fun z : G × X => F z.1 z.2))
    (K : Set X) (hK : IsClosed K) (N : ℕ) : IsClosed (survivors F K N) := by
  have heq : survivors F K N = ⋂ j : Fin (N + 1),
      (fun z : (Fin N → G) × X => prefixOrbit F z.1 j.val z.2) ⁻¹' K := by
    ext z
    simp only [survivors, mem_ofPred_eq, mem_iInter, mem_preimage]
  rw [heq]
  exact isClosed_iInter (fun j => hK.preimage (continuous_prefixOrbit F hF N j.val))

theorem cylinder_open (F : G → X → X)
    (hF : Continuous (fun z : G × X => F z.1 z.2))
    (cover : J → Set X) (hcover : ∀ i, IsOpen (cover i)) (N : ℕ)
    (labels : Fin (N + 1) → J) : IsOpen (cylinder F cover N labels) := by
  have heq : cylinder F cover N labels = ⋂ j : Fin (N + 1),
      (fun z : (Fin N → G) × X => prefixOrbit F z.1 j.val z.2) ⁻¹' cover (labels j) := by
    ext z
    simp only [cylinder, mem_ofPred_eq, mem_iInter, mem_preimage]
  rw [heq]
  exact isOpen_iInter_of_finite
    (fun j => (hcover (labels j)).preimage (continuous_prefixOrbit F hF N j.val))

omit [TopologicalSpace G] [TopologicalSpace X] in
theorem survivors_covered (F : G → X → X) (K : Set X) (cover : J → Set X)
    (hcover : K ⊆ ⋃ i, cover i) (N : ℕ) :
    survivors F K N ⊆ ⋃ labels, cylinder F cover N labels := by
  intro z hz
  have each : ∀ j : Fin (N + 1), ∃ i, prefixOrbit F z.1 j.val z.2 ∈ cover i :=
    fun j => mem_iUnion.mp (hcover (hz j))
  choose labels hlabels using each
  exact mem_iUnion.mpr ⟨labels, hlabels⟩

omit [TopologicalSpace G] [TopologicalSpace X] in
/-- The genuine finite alphabet gives a finite cylinder cover at every
horizon, including the actual terminal prefix. -/
theorem exists_finite_deterministic_cover [Fintype J]
    (F : G → X → X) (T : G) (K : Set X) (cover : J → Set X)
    (hcover : K ⊆ ⋃ i, cover i) (N : ℕ) :
    ∃ c : Finset (Fin (N + 1) → J),
      fiber K (survivors F K N) (fun _ => T) ⊆
        ⋃ labels ∈ c, (fun x => ((fun _ : Fin N => T), x)) ⁻¹' cylinder F cover N labels := by
  classical
  refine ⟨Finset.univ, ?_⟩
  intro x hx
  obtain ⟨labels, hlabels⟩ := mem_iUnion.mp (survivors_covered F K cover hcover N hx.2)
  exact mem_iUnion.mpr ⟨labels, mem_iUnion.mpr ⟨Finset.mem_univ _, hlabels⟩⟩

end LeanShared.FiniteWordCylinders
