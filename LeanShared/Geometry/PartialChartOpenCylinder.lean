module
public import LeanShared.Geometry.PartialChartWordAgreement

/-! Actual physical chart-cylinder validity and open coordinate tracking
produce an open equality window, hence eventual equality in the genuine
source coordinates for the ACTUAL whole word. -/
public noncomputable section
open Set Filter
open scoped Topology
namespace LeanShared.PartialChartWordAgreement
open CylinderPrincipalCoefficient
variable {M E : Type*} [TopologicalSpace M] [TopologicalSpace E]

theorem exists_open_window {N : ℕ} (F : Fin N → M → M) (continuousF : ∀ k, Continuous (F k))
    (G : Fin N → E → E) (κ : ℕ → OpenPartialHomeomorph M E)
    (B : ℕ → Set E) (openB : ∀ k, IsOpen (B k))
    (agreement : ∀ k : Fin N, ∀ z ∈ B k.val,
      G k z = κ (k.val+1) (F k ((κ k.val).symm z)))
    (m : M) (valid : ∀ k ≤ N, prefixOrbit F (fun j => j) k m ∈ (κ k).source)
    (tracking : ∀ k < N, κ k (prefixOrbit F (fun j => j) k m) ∈ B k) :
    ∃ O : Set M, IsOpen O ∧ m ∈ O ∧ ∀ p ∈ O, ∀ n ≤ N,
      prefixOrbit G (fun j => j) n (κ 0 p) = κ n (prefixOrbit F (fun j => j) n p) := by
  classical
  have continuousPrefix (k : ℕ) : Continuous (prefixOrbit F (fun j => j) k) := by
    induction k with
    | zero => exact continuous_id
    | succ k ih =>
      by_cases hk : k<N
      · simpa only [prefixOrbit,dite_eq_left hk,Function.comp_def] using (continuousF ⟨k,hk⟩).comp ih
      · simpa only [prefixOrbit,dite_eq_right hk] using ih
  let V (k : Fin (N+1)) := (prefixOrbit F (fun j => j) k.val) ⁻¹'
    ((κ k.val).source ∩ (κ k.val) ⁻¹' (if k.val<N then B k.val else univ))
  have openV (k : Fin (N+1)) : IsOpen (V k) := by
    have chartOpen : IsOpen ((κ k.val).source ∩ (κ k.val) ⁻¹'
        (if k.val<N then B k.val else univ)) := by
      apply (κ k.val).isOpen_inter_preimage
      split_ifs
      · exact openB k.val
      · exact isOpen_univ
    exact chartOpen.preimage (continuousPrefix k.val)
  have memberV (k : Fin (N+1)) : m ∈ V k := by
    refine ⟨valid k.val (Nat.le_of_lt_succ k.isLt),?_⟩
    by_cases hk : k.val<N
    · simpa only [mem_preimage,ite_eq_left hk] using tracking k.val hk
    · simp only [mem_preimage,ite_eq_right hk,mem_univ]
  refine ⟨⋂ k : Fin (N+1), V k,isOpen_iInter_of_finite openV,mem_iInter.mpr memberV,?_⟩
  intro p hp n hn
  apply prefix_eq F G κ B agreement p
  · intro k hk
    exact (mem_iInter.mp hp ⟨k,Nat.lt_succ_of_le hk⟩).1
  · intro k hk
    have item := (mem_iInter.mp hp ⟨k,Nat.lt_succ_of_le (Nat.le_of_lt hk)⟩).2
    simpa only [mem_preimage,ite_eq_left hk] using item
  · exact hn

theorem eventuallyEq_endpoint {N : ℕ} (F : Fin N → M → M) (continuousF : ∀ k, Continuous (F k))
    (G : Fin N → E → E) (κ : ℕ → OpenPartialHomeomorph M E)
    (B : ℕ → Set E) (openB : ∀ k, IsOpen (B k))
    (agreement : ∀ k : Fin N, ∀ z ∈ B k.val,
      G k z = κ (k.val+1) (F k ((κ k.val).symm z)))
    (m : M) (valid : ∀ k ≤ N, prefixOrbit F (fun j => j) k m ∈ (κ k).source)
    (tracking : ∀ k < N, κ k (prefixOrbit F (fun j => j) k m) ∈ B k) :
    prefixOrbit G (fun j => j) N =ᶠ[𝓝 (κ 0 m)]
      (κ N ∘ prefixOrbit F (fun j => j) N ∘ (κ 0).symm) := by
  obtain ⟨O,openO,member,equalities⟩ := exists_open_window F continuousF G κ B openB agreement m valid tracking
  have start : m ∈ (κ 0).source := valid 0 (Nat.zero_le N)
  have near : (κ 0).target ∩ (κ 0).symm ⁻¹' O ∈ 𝓝 (κ 0 m) :=
    ((κ 0).isOpen_inter_preimage_symm openO).mem_nhds
      ⟨(κ 0).map_source start,by
        change (κ 0).symm (κ 0 m) ∈ O
        rw [(κ 0).left_inv start]
        exact member⟩
  filter_upwards [near] with z hz
  have result := equalities ((κ 0).symm z) hz.2 N le_rfl
  rw [(κ 0).right_inv hz.1] at result
  exact result

end LeanShared.PartialChartWordAgreement
