module

public import LeanShared.Dynamics.ThermodynamicDefinitions
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Data.Finset.Preimage

/-! Literal separated pressure is preserved by isometric embeddings
intertwining the actual dynamics, with the exact image as invariant core. -/
public noncomputable section
open Set Function
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

omit [MetricSpace X] [MetricSpace Y] in
private theorem orbitSum_embedding (f : X → Y) (T : X → X) (S : Y → Y)
    (intertwine : Semiconj f T S) (φ : Y → ℝ) (n : ℕ) (x : X) :
    orbitSum T (φ ∘ f) n x=orbitSum S φ n (f x) := by
  apply Finset.sum_congr rfl
  intro j _
  change φ (f (T^[j] x))=φ (S^[j] (f x))
  rw [(intertwine.iterate_right j) x]

private theorem separated_embedding_iff (f : X → Y) (isometry : Isometry f)
    (T : X → X) (S : Y → Y) (intertwine : Semiconj f T S)
    (n : ℕ) (ε : ℝ) (s : Finset X) :
    Separated T univ n ε s ↔ Separated S (range f) n ε (s.map ⟨f,isometry.injective⟩) := by
  have distance (j : ℕ) (x y : X) : dist (S^[j] (f x)) (S^[j] (f y))=dist (T^[j] x) (T^[j] y) := by
    rw [←(intertwine.iterate_right j) x,←(intertwine.iterate_right j) y,isometry.dist_eq]
  constructor
  · intro hs
    refine ⟨?_,?_⟩
    · intro x hx
      obtain ⟨y,_,rfl⟩ := Finset.mem_map.mp hx
      exact mem_range_self y
    · intro x hx y hy different
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hy
      obtain ⟨j,hj,bound⟩ := hs.2 a ha b hb (fun h => different (congrArg f h))
      refine ⟨j,hj,?_⟩
      change ε ≤ dist (S^[j] (f a)) (S^[j] (f b))
      rwa [distance]
  · intro hs
    refine ⟨fun _ _ => mem_univ _,?_⟩
    intro x hx y hy different
    obtain ⟨j,hj,bound⟩ := hs.2 (f x) (Finset.mem_map.mpr ⟨x,hx,rfl⟩)
      (f y) (Finset.mem_map.mpr ⟨y,hy,rfl⟩) (fun h => different (isometry.injective h))
    exact ⟨j,hj,by rwa [distance] at bound⟩

theorem separatedPartitionSum_embedding (f : X → Y) (isometry : Isometry f)
    (T : X → X) (S : Y → Y) (intertwine : Semiconj f T S)
    (φ : Y → ℝ) (n : ℕ) (ε : ℝ) :
    separatedPartitionSum T (φ ∘ f) univ n ε=separatedPartitionSum S φ (range f) n ε := by
  classical
  have sums (s : Finset X) :
      (∑ x ∈ s, ENNReal.ofReal (Real.exp (orbitSum T (φ ∘ f) n x))) =
      ∑ x ∈ s.map ⟨f,isometry.injective⟩, ENNReal.ofReal (Real.exp (orbitSum S φ n x)) := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro x _
    rw [orbitSum_embedding f T S intertwine]
    rfl
  apply le_antisymm
  · refine iSup_le fun s => iSup_le fun hs => ?_
    rw [sums]
    exact le_iSup_of_le _ (le_iSup_of_le ((separated_embedding_iff f isometry T S intertwine n ε s).mp hs) le_rfl)
  · refine iSup_le fun s => iSup_le fun hs => ?_
    let t := s.preimage f isometry.injective.injOn
    have image : t.map ⟨f,isometry.injective⟩=s := by
      ext x
      constructor
      · intro hx
        obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
        exact Finset.mem_preimage.mp hy
      · intro hx
        obtain ⟨y,rfl⟩ := hs.1 x hx
        exact Finset.mem_map.mpr ⟨y,Finset.mem_preimage.mpr hx,rfl⟩
    have separated := (separated_embedding_iff f isometry T S intertwine n ε t).mpr (image ▸ hs)
    have sumEq := sums t
    rw [image] at sumEq
    rw [←sumEq]
    exact le_iSup_of_le t (le_iSup_of_le separated le_rfl)

theorem pressure_embedding (f : X → Y) (isometry : Isometry f)
    (T : X → X) (S : Y → Y) (intertwine : Semiconj f T S) (φ : Y → ℝ) :
    pressure T (φ ∘ f) univ=pressure S φ (range f) := by
  unfold pressure
  congr 1
  funext ε
  congr 1
  funext n
  rw [separatedPartitionSum_embedding f isometry T S intertwine]

end LeanShared.ThermodynamicDefinitions
