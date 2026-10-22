module

public import LeanShared.Dynamics.OneSidedGraphSplicing

/-! A common graph connection length gives literal finite prehistories
of any prescribed future which converge to any other prescribed future.
Every prehistory retains its full chosen initial word.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function Filter Topology
variable {A : Type*} [TopologicalSpace A] {R : A → A → Prop}

theorem exists_future_preimage_with_prefix (N : ℕ)
    (connections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val N = j)
    (a b : FuturePath R) (m : ℕ) :
    ∃ c : FuturePath R, (∀ k : ℕ, k ≤ m → c.val k = a.val k) ∧
      (futureShift : FuturePath R → FuturePath R)^[m + N] c = b := by
  obtain ⟨p, initial, final⟩ := connections (a.val m) (b.val 0)
  let middle := translatePath p (-(m : ℤ))
  have leftSymbol : (futureExtension a).val m = middle.val m := by
    change (futureExtension a).val m = p.val ((m : ℤ) + -(m : ℤ))
    rw [add_neg_cancel, initial, futureExtension_future]
  let reference := pasteWindow (futureExtension a) middle middle m m le_rfl leftSymbol rfl
  have referencePrefix (k : ℕ) (bound : k ≤ m) : reference.val k = a.val k := by
    by_cases before : k < m
    · change (if (k : ℤ) < m then _ else _) = _
      rw [ite_eq_left (by omega : (k : ℤ) < m)]
      exact futureExtension_future a k
    · have equal : k = m := by omega
      subst k
      rw [pasteWindow_middle _ _ _ _ _ _ _ _ _ le_rfl le_rfl]
      change p.val ((m : ℤ) + -(m : ℤ)) = a.val m
      simpa only [add_neg_cancel] using initial
  have endpoint : reference.val (m + N) = b.val 0 := by
    change (if ((m + N : ℕ) : ℤ) < m then _ else
      if ((m + N : ℕ) : ℤ) ≤ m then middle.val (m + N) else middle.val (m + N)) = _
    rw [ite_eq_right (by omega : ¬ ((m + N : ℕ) : ℤ) < m), ite_self]
    change p.val (((m + N : ℕ) : ℤ) + -(m : ℤ)) = b.val 0
    have time : (((m + N : ℕ) : ℤ) + -(m : ℤ)) = (N : ℤ) := by omega
    rw [time]
    exact final
  refine ⟨futureSplice reference (m + N) b endpoint, ?_, futureShift_splice _ _ _ _⟩
  intro k bound
  rw [futureSplice_word _ _ _ _ k (by omega)]
  exact referencePrefix k bound

theorem exists_convergent_future_prehistories (N : ℕ)
    (connections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val N = j)
    (a b : FuturePath R) :
    ∃ c : ℕ → FuturePath R, Tendsto c atTop (𝓝 a) ∧
      ∀ m, (futureShift : FuturePath R → FuturePath R)^[m + N] (c m) = b := by
  choose c agreement preimage using exists_future_preimage_with_prefix N connections a b
  refine ⟨c, ?_, preimage⟩
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro k
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop k] with m bound
  exact (agreement m k bound).symm

end LeanShared.BilateralShadowingCoding
