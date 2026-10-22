module

public import LeanShared.Dynamics.ThermodynamicDefinitions
public import Mathlib.Data.Finset.Preimage

/-! Literal separated pressure commutes with restriction to an invariant
subtype, using its induced metric and the exact original orbit sums. -/
public noncomputable section
open Set Function
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] {T : X → X} {K : Set X}

omit [MetricSpace X] in
theorem iterate_coe_restriction (S : K → K) (same : ∀ x, (S x).val=T x.val)
    (n : ℕ) (x : K) : (S^[n] x).val=T^[n] x.val := by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [iterate_succ_apply',same,hn,iterate_succ_apply']

omit [MetricSpace X] in
theorem orbitSum_restriction (S : K → K) (same : ∀ x, (S x).val=T x.val)
    (φ : X → ℝ) (n : ℕ) (x : K) :
    orbitSum S (fun x => φ x.val) n x=orbitSum T φ n x.val := by
  apply Finset.sum_congr rfl
  intro j _
  change φ ((S^[j] x).val)=φ (T^[j] x.val)
  rw [iterate_coe_restriction S same]

private theorem separated_map_iff (S : K → K) (same : ∀ x, (S x).val=T x.val)
    (n : ℕ) (ε : ℝ) (s : Finset K) :
    Separated S univ n ε s ↔
      Separated T K n ε (s.map ⟨Subtype.val,Subtype.val_injective⟩) := by
  constructor
  · intro hs
    constructor
    · intro x hx
      obtain ⟨x,_,rfl⟩ := Finset.mem_map.mp hx
      exact x.property
    · intro x hx y hy neq
      obtain ⟨a,ha,ea⟩ := Finset.mem_map.mp hx
      obtain ⟨b,hb,eb⟩ := Finset.mem_map.mp hy
      change a.val=x at ea
      change b.val=y at eb
      subst x
      subst y
      obtain ⟨j,hj,hd⟩ := hs.2 a ha b hb (fun h => neq (congrArg Subtype.val h))
      refine ⟨j,hj,?_⟩
      change ε ≤ dist ((S^[j] a).val) ((S^[j] b).val) at hd
      simpa only [iterate_coe_restriction S same] using hd
  · intro hs
    constructor
    · exact fun _ _ => mem_univ _
    · intro x hx y hy neq
      obtain ⟨j,hj,hd⟩ := hs.2 x.val (Finset.mem_map.mpr ⟨x,hx,rfl⟩)
        y.val (Finset.mem_map.mpr ⟨y,hy,rfl⟩) (fun h => neq (Subtype.ext h))
      refine ⟨j,hj,?_⟩
      change ε ≤ dist ((S^[j] x).val) ((S^[j] y).val)
      simpa only [iterate_coe_restriction S same] using hd

theorem separatedPartitionSum_restriction (S : K → K) (same : ∀ x, (S x).val=T x.val)
    (φ : X → ℝ) (n : ℕ) (ε : ℝ) :
    separatedPartitionSum S (fun x => φ x.val) univ n ε=separatedPartitionSum T φ K n ε := by
  classical
  have sums (s : Finset K) :
      (∑ x ∈ s, ENNReal.ofReal (Real.exp (orbitSum S (fun x => φ x.val) n x))) =
      ∑ x ∈ s.map ⟨Subtype.val,Subtype.val_injective⟩,
        ENNReal.ofReal (Real.exp (orbitSum T φ n x)) := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro x _
    exact congrArg (fun r : ℝ => ENNReal.ofReal (Real.exp r))
      (orbitSum_restriction S same φ n x)
  apply le_antisymm
  · refine iSup_le fun s => iSup_le fun hs => ?_
    rw [sums]
    exact le_iSup_of_le (s.map ⟨Subtype.val,Subtype.val_injective⟩)
      (by simp only [iSup_pos ((separated_map_iff S same n ε s).mp hs)]; exact le_rfl)
  · refine iSup_le fun s => iSup_le fun hs => ?_
    let t : Finset K := s.preimage Subtype.val Subtype.val_injective.injOn
    have image : t.map ⟨Subtype.val,Subtype.val_injective⟩=s := by
      ext x
      constructor
      · intro hx
        obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
        exact Finset.mem_preimage.mp hy
      · intro hx
        refine Finset.mem_map.mpr ⟨⟨x,hs.1 x hx⟩,?_,rfl⟩
        exact Finset.mem_preimage.mpr hx
    have hsub : Separated S univ n ε t := (separated_map_iff S same n ε t).mpr (image ▸ hs)
    have sumEq := sums t
    rw [image] at sumEq
    rw [←sumEq]
    exact le_iSup_of_le t (by simp only [iSup_pos hsub]; exact le_rfl)

theorem pressure_restriction (S : K → K) (same : ∀ x, (S x).val=T x.val) (φ : X → ℝ) :
    pressure S (fun x => φ x.val) univ=pressure T φ K := by
  unfold pressure
  congr 1
  funext ε
  congr 1
  funext n
  rw [separatedPartitionSum_restriction S same]

end LeanShared.ThermodynamicDefinitions
