module
public import LeanShared.Dynamics.ExpansiveSeparatedCardinality
public import LeanShared.Dynamics.SeparatedSpanningSet
public import LeanShared.Analysis.PressureCoverRefinement

/-! Actual maximal Bowen-separated centers give a finite open orbit cover
whose literal supremum costs are controlled by the separated partition sum.
Only the actual potential distortion on these orbit balls is used. -/
public noncomputable section
open Set
open scoped BigOperators ENNReal
namespace LeanShared.BowenOpenCoverCoefficient
open ThermodynamicDefinitions PressureCoverRefinement
variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]

@[expose] def orbitBall (T : X→X) (n : ℕ) (ε : ℝ) (y : X) : Set X :=
  {x | ∀ j<n,dist (T^[j] x) (T^[j] y)<ε}

theorem exists_cover (T : X ≃ₜ X) (c : ℝ) (positiveC : 0<c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T:X→X)^[j] x) ((T:X→X)^[j] y)≤c ∧
      dist ((T.symm:X→X)^[j] x) ((T.symm:X→X)^[j] y)≤c)→x=y)
    (φ : X→ℝ) (n : ℕ) (ε D : ℝ) (positiveε : 0<ε)
    (distortion : ∀ x y,x∈orbitBall T n ε y → orbitSum T φ n x≤orbitSum T φ n y+D) :
    ∃ s : Finset X, Separated T univ n ε s ∧
      univ⊆⋃ y∈s,orbitBall T n ε y ∧
      (∀ y,IsOpen (orbitBall T n ε y)) ∧
      ENNReal.ofReal (∑ y∈s,domainCoefficient univ (orbitBall T n ε y)
        (fun x=>Real.exp (orbitSum T φ n x)))≤
        ENNReal.ofReal (Real.exp D)*separatedPartitionSum T φ univ n ε := by
  classical
  obtain ⟨a,_,counts⟩ := FiniteExpansiveWords.exists_uniform_card_bound T c positiveC expansive
  obtain ⟨p,count⟩ := counts ε positiveε
  obtain ⟨s,_,separated,spans⟩ := exists_separated_spanning T n ε positiveε (a^(n+p)) (count n)
  have point (y : X) : domainCoefficient univ (orbitBall T n ε y)
      (fun x=>Real.exp (orbitSum T φ n x))≤Real.exp D*Real.exp (orbitSum T φ n y) := by
    unfold domainCoefficient
    apply csSup_le (s:=({0} ∪ (fun x=>Real.exp (orbitSum T φ n x)) '' (univ ∩ orbitBall T n ε y) : Set ℝ)) ⟨0,Or.inl (mem_singleton 0)⟩
    rintro v (hv|⟨x,hx,rfl⟩)
    · rcases mem_singleton_iff.mp hv with rfl
      positivity
    · rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      exact (distortion x y hx.2).trans_eq (add_comm _ _)
  refine ⟨s,separated,?_,?_,?_⟩
  · intro x _
    obtain ⟨y,hy,near⟩ := spans x
    exact mem_iUnion₂.mpr ⟨y,hy,near⟩
  · intro y
    have formula : orbitBall T n ε y=⋂ j : Fin n,{x | dist (T^[j.val] x) (T^[j.val] y)<ε} := by
      ext x
      simp only [orbitBall,mem_ofPred_eq,mem_iInter]
      exact ⟨fun h j=>h j.val j.isLt,fun h j hj=>h ⟨j,hj⟩⟩
    rw [formula]
    exact isOpen_iInter_of_finite (fun j=>isOpen_lt ((T.continuous.iterate j.val).dist continuous_const) continuous_const)
  · have sumBound := ENNReal.ofReal_le_ofReal (Finset.sum_le_sum (fun y (_:y∈s)=>point y))
    rw [←Finset.mul_sum,ENNReal.ofReal_mul (Real.exp_nonneg D),
      ENNReal.ofReal_sum_of_nonneg (fun _ _=>Real.exp_nonneg _)] at sumBound
    apply sumBound.trans
    exact mul_le_mul' le_rfl (le_iSup_of_le s (le_iSup_of_le separated le_rfl))
end LeanShared.BowenOpenCoverCoefficient
