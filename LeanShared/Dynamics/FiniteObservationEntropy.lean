module

public import LeanShared.Dynamics.FinitePartitionEntropy
public import LeanShared.Dynamics.FiniteConditionalEntropy
public import LeanShared.Dynamics.FiniteStrongSubadditivity

/-! Shannon entropy and conditional entropy of actual finite measurable
observations, with their fiber partitions constructed internally. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators
namespace LeanShared.FiniteObservationEntropy
variable {X I J : Type*} [MeasurableSpace X] [Fintype I] [Fintype J]

@[expose] def entropy (μ : Measure X) (f : X → I) : ℝ :=
  -∑ i, μ.real (f ⁻¹' {i})*Real.log (μ.real (f ⁻¹' {i}))

omit [MeasurableSpace X] [Fintype J] in
/-- Actual fibers of a finite observation partition the whole space. -/
theorem fibers_cover (g : X → J) : (⋃ j, g ⁻¹' {j})=univ := by
  ext x
  simp

omit [MeasurableSpace X] [Fintype J] in
private theorem fibers_disjoint (g : X → J) : Pairwise (fun i j => Disjoint (g ⁻¹' {i}) (g ⁻¹' {j})) := by
  intro i j different
  exact (disjoint_singleton.mpr different).preimage _

theorem marginal [MeasurableSpace J] [MeasurableSingletonClass J] (μ : Measure X)
    [IsFiniteMeasure μ] (A : Set X) (measurableA : MeasurableSet A)
    (g : X → J) (measurable : Measurable g) :
    ∑ j, μ.real (A ∩ g ⁻¹' {j})=μ.real A := by
  rw [←measureReal_iUnion_fintype]
  · rw [←inter_iUnion,fibers_cover,inter_univ]
  · intro i j different
    exact (fibers_disjoint g different).mono inter_subset_right inter_subset_right
  · exact fun j => measurableA.inter ((measurableSet_singleton j).preimage measurable)

theorem pair_entropy (μ : Measure X) (f : X → I) (g : X → J) :
    entropy μ (fun x => (f x,g x)) =
      -(∑ i, ∑ j, μ.real (f ⁻¹' {i} ∩ g ⁻¹' {j})*Real.log (μ.real (f ⁻¹' {i} ∩ g ⁻¹' {j}))) := by
  unfold entropy
  rw [Fintype.sum_prod_type]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have identity : (fun x => (f x,g x)) ⁻¹' {(i,j)}=f ⁻¹' {i} ∩ g ⁻¹' {j} := by ext x; simp
  rw [identity]

theorem pair_entropy_le [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace J] [MeasurableSingletonClass J] (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → I) (g : X → J) (measurableF : Measurable f) (measurableG : Measurable g) :
    entropy μ (fun x => (f x,g x)) ≤ entropy μ f + entropy μ g := by
  rw [pair_entropy]
  simpa only [entropy,sub_eq_add_neg] using FinitePartitionEntropy.refinement_le μ
    (fun i => f ⁻¹' {i}) (fun j => g ⁻¹' {j})
    (fun i => (measurableSet_singleton i).preimage measurableF)
    (fun j => (measurableSet_singleton j).preimage measurableG)
    (fibers_disjoint f) (fibers_disjoint g) (fibers_cover f) (fibers_cover g)

/-- The conditional entropy of the second observation given the first
is nonnegative, including conditioning on zero-mass atoms. -/
theorem conditional_nonnegative [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace J] [MeasurableSingletonClass J] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → I) (g : X → J) (measurableF : Measurable f) (measurableG : Measurable g) :
    0 ≤ entropy μ (fun x => (f x,g x)) - entropy μ f := by
  rw [pair_entropy]
  have bound := FiniteConditionalEntropy.refinement_nonnegative
    (fun i j => μ.real (f ⁻¹' {i} ∩ g ⁻¹' {j})) (fun _ _ => measureReal_nonneg)
  have sums (i : I) := marginal μ (f ⁻¹' {i})
    ((measurableSet_singleton i).preimage measurableF) g measurableG
  simpa only [sums,entropy,sub_neg_eq_add] using bound

/-- Injective relabelling preserves the entropy of the actual fibers. -/
theorem entropy_injective (μ : Measure X) (f : X → I) (g : I → J) (injective : Injective g) :
    entropy μ (g ∘ f)=entropy μ f := by
  classical
  let embedding : I ↪ J := ⟨g,injective⟩
  let image : Finset J := Finset.univ.map embedding
  have subset : image ⊆ Finset.univ := Finset.subset_univ _
  have outside (j : J) (_ : j ∈ Finset.univ) (notmem : j ∉ image) :
      μ.real ((g ∘ f) ⁻¹' {j})*Real.log (μ.real ((g ∘ f) ⁻¹' {j}))=0 := by
    have empty : (g ∘ f) ⁻¹' {j}=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      apply notmem
      exact Finset.mem_map.mpr ⟨f x,Finset.mem_univ _,hx⟩
    simp only [empty,measureReal_empty,zero_mul]
  have fiber (i : I) : (g ∘ f) ⁻¹' {g i}=f ⁻¹' {i} := by
    ext x
    exact injective.eq_iff
  unfold entropy
  rw [←Finset.sum_subset subset outside,Finset.sum_map]
  simp only [embedding,Function.Embedding.coeFn_mk,fiber]

/-- Applying any deterministic finite observation can only decrease entropy. -/
theorem entropy_comp_le [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace J] [MeasurableSingletonClass J] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → I) (g : I → J) (measurableF : Measurable f) :
    entropy μ (g ∘ f) ≤ entropy μ f := by
  have bound := conditional_nonnegative μ (g ∘ f) f
    ((measurable_of_countable g).comp measurableF) measurableF
  have pair : entropy μ (fun x => (g (f x),f x))=entropy μ f :=
    entropy_injective μ f (fun i => (g i,i)) (fun _ _ equal => congrArg Prod.snd equal)
  simp only [Function.comp_apply] at bound
  rw [pair] at bound
  linarith

end LeanShared.FiniteObservationEntropy
