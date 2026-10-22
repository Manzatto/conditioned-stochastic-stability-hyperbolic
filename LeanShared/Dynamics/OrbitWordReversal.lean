module
public import LeanShared.Dynamics.FiniteOrbitWordAssembly

/-! Exact reversal of finite orbit-segment schedules. No asymptotic or
unlabelled choice of segment times is used. -/
public section
namespace LeanShared.FiniteOrbitWordAssembly

@[expose] def reversed (length:ℕ→ℕ) (k:ℕ) (i:ℕ) : ℕ := length (k-i)

theorem offset_head (gap:ℕ) (length:ℕ→ℕ) (k:ℕ) :
    offset gap length (k+1)=length 0+gap+offset gap (fun i=>length (i+1)) k := by
  simp only [offset,Finset.sum_range_succ']
  omega

theorem reversed_offset_succ (gap:ℕ) (length:ℕ→ℕ) (k n:ℕ) :
    offset gap (reversed length (k+1)) (n+1)=
      length (k+1)+gap+offset gap (reversed length k) n := by
  rw [offset_head]
  have shift : (fun i=>reversed length (k+1) (i+1))=reversed length k := by
    funext i
    dsimp only [reversed]
    rw [Nat.add_sub_add_right]
  rw [shift]
  rfl

theorem offset_reversal (gap:ℕ) (length:ℕ→ℕ) {i k:ℕ} (hi:i≤k) :
    offset gap length i+offset gap (reversed length k) (k-i)+length i=ending gap length k := by
  induction k with
  | zero =>
    have same:i=0 := by omega
    subst i
    simp only [offset,reversed,ending,Finset.range_zero,Finset.sum_empty,Nat.zero_add,Nat.sub_self]
  | succ k ih =>
    by_cases lower:i≤k
    · have index:k+1-i=(k-i)+1 := by omega
      rw [index,reversed_offset_succ,ending_succ]
      have previous:=ih lower
      omega
    · have same:i=k+1 := by omega
      subst i
      simp only [Nat.sub_self,offset,Finset.range_zero,Finset.sum_empty,Nat.add_zero,ending]

theorem reversed_ending (gap:ℕ) (length:ℕ→ℕ) (k:ℕ) :
    ending gap (reversed length k) k=ending gap length k := by
  have sum:=offset_reversal gap length (i:=0) (k:=k) (Nat.zero_le k)
  simpa only [offset,ending,reversed,Nat.sub_zero,Nat.sub_self,Finset.range_zero,
    Finset.sum_empty,Nat.zero_add,Nat.sub_self] using sum

end LeanShared.FiniteOrbitWordAssembly
