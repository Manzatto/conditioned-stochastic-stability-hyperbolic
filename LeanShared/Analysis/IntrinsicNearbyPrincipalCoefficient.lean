module

public import LeanShared.Analysis.IntrinsicOrbitDistortion
public import LeanShared.Analysis.IntrinsicPrincipalSuprema

/-! The principal coefficient for actual nearby words is derived from
ordinary DETERMINISTIC full-cylinder orbit/Jacobian distortion. The loss
constant is independent of word length whenever the deterministic orbital
sum and log-Jacobian constants are. The nearby neighborhood may depend on
the selected word length, as required by the fixed-block argument. -/

public noncomputable section
open Set
open scoped BigOperators
namespace LeanShared.IntrinsicNearbyPrincipalCoefficient
open CylinderPrincipalCoefficient IntrinsicPrincipalDensity IntrinsicPrincipalSuprema
variable {G X : Type*} [TopologicalSpace G] [TopologicalSpace X] [T2Space X]
  (F : G → X → X) (E : X → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [∀ x, FiniteDimensional ℝ (E x)]
  (D : ∀ a x, E x ≃L[ℝ] E (F a x))
  (stable unstable : ∀ x, Submodule ℝ (E x))

/-- The microscopic product of separate suprema is bounded by the JOINT
positive-envelope coefficient, including on every selected outer cylinder
inside the actual full moving cylinder. No noisy distortion estimate or
noisy principal coefficient is assumed. -/
theorem exists_uniform_separate_bound (g : X → ℝ) (hg : ∀ x, 0 ≤ g x)
    (N : ℕ) (reference : G) (K : Set X) (hK : IsCompact K)
    (R : Set ((Fin N → G) × X)) (hR : IsClosed R)
    (U : Set (Fin N → G)) (hU : IsOpen U) (href : (fun _ => reference) ∈ U)
    (ε H B BJ : ℝ) (hε : 0 < ε) (hH : 0 ≤ H)
    (hf : ContinuousOn (IntrinsicDistortionRatio.ratio F E D unstable g (fun x => g x + ε) N)
      ((U ×ˢ univ) ∩ IntrinsicDistortionRatio.tripleRelation R))
    (error : X → X → Fin N → ℝ)
    (hdiff : ∀ x ∈ fiber K R (fun _ => reference), ∀ z ∈ fiber K R (fun _ => reference),
      ∀ j : Fin N, |g (prefixOrbit F (fun _ : Fin N => reference) j.val x) -
        g (prefixOrbit F (fun _ : Fin N => reference) j.val z)| ≤ H * error x z j)
    (hsum : ∀ x ∈ fiber K R (fun _ => reference), ∀ z ∈ fiber K R (fun _ => reference),
      (∑ j, error x z j) ≤ B)
    (hjac : ∀ y ∈ fiber K R (fun _ => reference), ∀ z ∈ fiber K R (fun _ => reference),
      |Real.log (unstableJacobian F E D (List.ofFn (fun _ : Fin N => reference)) z (unstable z)) -
        Real.log (unstableJacobian F E D (List.ofFn (fun _ : Fin N => reference)) y (unstable y))| ≤ BJ) :
    ∃ W : Set G, IsOpen W ∧ reference ∈ W ∧
      ∀ word : Fin N → G, (∀ i, word i ∈ W) →
        ∀ (S : Set ((Fin N → G) × X)), IsClosed S → fiber K S word ⊆ fiber K R word →
        ∀ (t s : ℝ),
        ContinuousOn (fun x => originalWeight F g N (word, x)) (fiber K S word) →
        ContinuousOn (fun x => originalWeight F (fun q => g q + ε) N (word, x)) (fiber K S word) →
        ContinuousOn (fun x => unstableJacobian F E D (List.ofFn word) x (unstable x)) (fiber K S word) →
        ContinuousOn (fun x => hyperbolicity F E D stable unstable N t s (word, x)) (fiber K S word) →
        coefficient K S (originalWeight F g N) word *
          coefficient K S (inverseJacobian F E D unstable N) word *
          coefficient K S (hyperbolicity F E D stable unstable N t s) word ≤
          (Real.exp ((H / ε) * B + BJ) + 1) *
            coefficient K S (density F E D (fun q => g q + ε) stable unstable N t s) word := by
  have hdet : ∀ x ∈ fiber K R (fun _ => reference), ∀ y ∈ fiber K R (fun _ => reference),
      ∀ z ∈ fiber K R (fun _ => reference),
      IntrinsicDistortionRatio.ratio F E D unstable g (fun q => g q + ε) N
        ((fun _ => reference), (x, y, z)) ≤ Real.exp ((H / ε) * B + BJ) := by
    intro x hx y hy z hz
    exact IntrinsicOrbitDistortion.ratio_bound F E D unstable g hg (fun _ => reference)
      x y z (error x z) H B BJ ε hH hε (hdiff x hx z hz) (hsum x hx z hz) (hjac y hy z hz)
  obtain ⟨W, hW, hrefW, hbound⟩ := IntrinsicDistortionRatio.exists_nearby_bound F E D unstable
    g (fun q => g q + ε) N reference K hK R hR U hU href hf
    (Real.exp ((H / ε) * B + BJ)) (Real.exp_pos _).le hdet
  refine ⟨W, hW, hrefW, ?_⟩
  intro word hw S hS hsub t s hweight henvelope hjacobian hhyperbolicity
  apply three_suprema_le F E D stable unstable g (fun q => g q + ε) hg
    (fun q => add_pos_of_nonneg_of_pos (hg q) hε) N t s word K hK S hS
    hweight henvelope hjacobian hhyperbolicity
    (Real.exp ((H / ε) * B + BJ) + 1) (by positivity)
  intro x hx y hy z hz
  exact (hbound word hw x (hsub hx) y (hsub hy) z (hsub hz)).le

end LeanShared.IntrinsicNearbyPrincipalCoefficient
