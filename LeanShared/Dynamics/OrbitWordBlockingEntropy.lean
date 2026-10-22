module

public import LeanShared.Dynamics.FiniteObservationEntropy
public import Mathlib.Logic.Equiv.Fin.Basic

/-! Blocking an actual orbit word into equal consecutive segments preserves
its finite observation entropy exactly. The time-index bijection and the
iterate identities are proved, including empty words. -/
public noncomputable section
open Function MeasureTheory
namespace LeanShared.FiniteObservationEntropy
variable {X I : Type*} [MeasurableSpace X] [Fintype I]

theorem entropy_orbit_word_blocks (μ : Measure X) (T : X → X) (f : X → I)
    (k n : ℕ) :
    entropy μ (fun x (i : Fin k) (j : Fin n) => f (T^[j.val] ((T^[n])^[i.val] x))) =
      entropy μ (fun x (l : Fin (k * n)) => f (T^[l.val] x)) := by
  let block : (Fin (k * n) → I) → (Fin k → Fin n → I) :=
    fun w i j => w (finProdFinEquiv (i, j))
  have injective : Injective block := by
    intro u v equal
    funext l
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective l
    exact congrFun (congrFun equal i) j
  have same : (fun x (i : Fin k) (j : Fin n) => f (T^[j.val] ((T^[n])^[i.val] x))) =
      block ∘ (fun x (l : Fin (k * n)) => f (T^[l.val] x)) := by
    funext x i j
    dsimp [block]
    rw [← Function.iterate_mul, ← Function.iterate_add_apply]
    rfl
  rw [same]
  exact entropy_injective μ _ block injective

end LeanShared.FiniteObservationEntropy
