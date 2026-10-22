module

public import LeanShared.Geometry.ConstructedManifoldLocalization
public import LeanShared.Dynamics.FiniteWordCylinders

/-! The constructed genuine chart partition supplies the finite alphabet
for literal pressure cylinders on the manifold. Neither a global frame nor
an independently supplied finite word-cover family is required. -/

@[expose] public noncomputable section
open Set
open scoped Manifold ContDiff BigOperators Topology
namespace LeanShared.ConstructedManifoldLocalization
variable {E M J G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  (e : J → OpenPartialHomeomorph M E) {S : Set M} (D : Data e S)

/-- The actual finite atlas selected by the partition covers its support. -/
theorem selected_charts_cover : S ⊆ ⋃ i : D.indices, (e i).source := by
  classical
  intro x hx
  have hsum : (∑ i : D.indices, D.cutoff i x) ≠ 0 := by
    rw [D.partition x hx]
    exact one_ne_zero
  obtain ⟨i, _, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact mem_iUnion.mpr ⟨i, D.support i (subset_tsupport (D.cutoff i) hne)⟩

/-- Literal chronological cylinders of the selected actual atlas. -/
def wordCylinder (F : G → M → M) (N : ℕ) (labels : Fin (N + 1) → D.indices) :=
  FiniteWordCylinders.cylinder F (fun i : D.indices => (e i).source) N labels

variable [TopologicalSpace G]

theorem wordCylinder_open (F : G → M → M)
    (hF : Continuous (fun z : G × M => F z.1 z.2)) (N : ℕ)
    (labels : Fin (N + 1) → D.indices) : IsOpen (wordCylinder e D F N labels) :=
  FiniteWordCylinders.cylinder_open F hF (fun i : D.indices => (e i).source)
    (fun i => (e i).open_source) N labels

omit [TopologicalSpace G] in
/-- Any retained region inside the constructed localization support has a
finite actual atlas-cylinder cover at every deterministic horizon. -/
theorem exists_finite_word_cover (F : G → M → M) (T : G) (K : Set M) (hKS : K ⊆ S)
    (N : ℕ) :
    ∃ c : Finset (Fin (N + 1) → D.indices),
      CylinderPrincipalCoefficient.fiber K (FiniteWordCylinders.survivors F K N) (fun _ => T) ⊆
        ⋃ labels ∈ c, (fun x => ((fun _ : Fin N => T), x)) ⁻¹' wordCylinder e D F N labels :=
  FiniteWordCylinders.exists_finite_deterministic_cover F T K
    (fun i : D.indices => (e i).source) (hKS.trans (selected_charts_cover e D)) N

end LeanShared.ConstructedManifoldLocalization
