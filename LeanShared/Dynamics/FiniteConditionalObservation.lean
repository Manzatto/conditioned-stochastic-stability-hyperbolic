module

public import LeanShared.Dynamics.FiniteObservationPermutation
public import LeanShared.Dynamics.FiniteObservationStrongSubadditivity

/-! Conditioning and pair-chain inequalities for actual finite
observations. No entropy comparison is assumed. -/
public noncomputable section
open Function MeasureTheory
namespace LeanShared.FiniteObservationEntropy
variable {X I J K L : Type*} [MeasurableSpace X]
  [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
  [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]

@[expose] def conditional (μ : Measure X) (f : X → I) (g : X → J) : ℝ :=
  entropy μ (fun x => (f x,g x)) - entropy μ g

theorem conditioning_decreases (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → I) (g : X → J) (h : X → K)
    (mf : Measurable f) (mg : Measurable g) (mh : Measurable h) :
    conditional μ f (fun x => (g x,h x)) ≤ conditional μ f g := by
  have bound := strong_subadditivity μ g f h mg mf mh
  rw [triple_swap_first μ g f h,pair_swap μ g f] at bound
  dsimp only [conditional]
  linarith

theorem conditional_subadditive (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → I) (g : X → J) (h : X → K)
    (mf : Measurable f) (mg : Measurable g) (mh : Measurable h) :
    conditional μ (fun x => (f x,h x)) g ≤ conditional μ f g + conditional μ h g := by
  have bound := strong_subadditivity μ g f h mg mf mh
  rw [pair_swap μ g (fun x => (f x,h x)),pair_swap μ g f,pair_swap μ g h] at bound
  dsimp only [conditional]
  linarith

omit [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace K] [MeasurableSingletonClass K] in
private theorem triple_swap_last (μ : Measure X) (f : X → I) (g : X → J) (h : X → K) :
    entropy μ (fun x => (f x,(g x,h x)))=entropy μ (fun x => (f x,(h x,g x))) :=
  (entropy_injective μ (fun x => (f x,(g x,h x)))
    (Equiv.prodCongr (Equiv.refl I) (Equiv.prodComm J K))
    (Equiv.prodCongr (Equiv.refl I) (Equiv.prodComm J K)).injective).symm

/-- The conditional entropy of two paired observations is at most the
sum of their separately conditioned entropies. -/
theorem conditional_pair_le (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → I) (g : X → J) (h : X → K) (q : X → L)
    (mf : Measurable f) (mg : Measurable g) (mh : Measurable h) (mq : Measurable q) :
    conditional μ (fun x => (f x,h x)) (fun x => (g x,q x)) ≤
      conditional μ f g + conditional μ h q := by
  have first := conditional_subadditive μ f (fun x => (g x,q x)) h mf (mg.prodMk mq) mh
  have second := conditioning_decreases μ f g q mf mg mq
  have third := conditioning_decreases μ h q g mh mq mg
  have swap : conditional μ h (fun x => (q x,g x))=conditional μ h (fun x => (g x,q x)) := by
    unfold conditional
    rw [triple_swap_last μ h q g,pair_swap μ q g]
  rw [swap] at third
  exact first.trans (add_le_add second third)

end LeanShared.FiniteObservationEntropy
