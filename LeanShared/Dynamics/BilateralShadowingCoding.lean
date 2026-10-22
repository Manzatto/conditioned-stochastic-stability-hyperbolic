module

public import LeanShared.Dynamics.EntireOrbitIdentity
public import Mathlib.Dynamics.SymbolicDynamics.Basic
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith

/-! Finite-graph symbolic paths and the unique continuous coding supplied
by expansive shadowing.  This constructs the shadowing coding used before
the Markov refinement.  It does not assert finite coding multiplicity.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function BilateralHomeomorphismOrbit
open scoped Topology
variable {A X : Type*} [TopologicalSpace A] [DiscreteTopology A] [MetricSpace X]

/-- The subshift with the prescribed one-step adjacency relation. -/
@[expose] def graphShift (R : A → A → Prop) : SymbolicDynamics.FullShift.Subshift A ℤ where
  carrier := {a | ∀ n : ℤ, R (a n) (a (n + 1))}
  isClosed := by
    have closedR : IsClosed {p : A × A | R p.1 p.2} := isClosed_discrete _
    have closed (n : ℤ) : IsClosed {a : ℤ → A | R (a n) (a (n + 1))} := by
      have pair : Continuous (fun a : ℤ → A => (a n, a (n + 1))) :=
        (continuous_apply n).prodMk (continuous_apply (n + 1))
      exact closedR.preimage pair
    convert isClosed_iInter closed using 1
    ext a
    simp only [mem_iInter, mem_ofPred_eq]
  mapsTo := by
    intro g a ha n
    simpa only [SymbolicDynamics.FullShift.shift_apply, add_assoc] using ha (g + n)

/-- A bilateral admissible path, with the inherited product topology. -/
@[expose] def Path (R : A → A → Prop) : Type _ :=
  {a : ℤ → A // ∀ n : ℤ, R (a n) (a (n + 1))}

instance (R : A → A → Prop) : TopologicalSpace (Path R) := inferInstanceAs
  (TopologicalSpace {a : ℤ → A // ∀ n : ℤ, R (a n) (a (n + 1))})

instance [CompactSpace A] (R : A → A → Prop) : CompactSpace (Path R) :=
  isCompact_iff_compactSpace.mp (graphShift R).isClosed.isCompact

/-- The usual left shift on admissible paths. -/
@[expose] def shift (R : A → A → Prop) : Path R ≃ₜ Path R where
  toFun a := ⟨fun n => a.val (n + 1), fun n => by
    simpa only [add_assoc] using a.property (n + 1)⟩
  invFun a := ⟨fun n => a.val (n - 1), fun n => by
    simpa using a.property (n - 1)⟩
  left_inv a := by apply Subtype.ext; funext n; simp
  right_inv a := by apply Subtype.ext; funext n; simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi (fun n => (continuous_apply (n + 1)).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi (fun n => (continuous_apply (n - 1)).comp continuous_subtype_val)

omit [DiscreteTopology A] in
@[simp] theorem shift_apply (R : A → A → Prop) (a : Path R) (n : ℤ) :
    (shift R a).val n = a.val (n + 1) := rfl

theorem orbit_apply_time (T : X ≃ₜ X) (x : X) (n : ℤ) :
    orbit T (T x) n = orbit T x (n - 1) := by
  have canonical := eq_canonical T (fun j => orbit T x (j - 1)) (by
    intro j
    simpa only [sub_add_cancel, add_sub_cancel_right] using step T x (j - 1))
  have initial : orbit T x (0 - 1) = T x := by simp [orbit]
  rw [initial] at canonical
  exact (congrFun canonical n).symm

/-- Two points shadowing the same reference within less than half an
expansivity radius coincide.  Closed shadowing bounds are allowed. -/
theorem shadow_unique (T : X ≃ₜ X) (c ε : ℝ)
    (expansive : ∀ x y : X, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (small : 2 * ε ≤ c) (reference : ℤ → X) (x y : X)
    (hx : ∀ n, dist (orbit T x n) (reference n) ≤ ε)
    (hy : ∀ n, dist (orbit T y n) (reference n) ≤ ε) : x = y := by
  have close (n : ℤ) : dist (orbit T x n) (orbit T y n) ≤ c := by
    have triangle := dist_triangle (orbit T x n) (reference n) (orbit T y n)
    have other := hy n
    rw [dist_comm] at other
    linarith [hx n]
  apply expansive x y
  intro j
  constructor
  · simpa only [neg_nat_time] using close (-(j : ℤ))
  · simpa only [nat_time] using close (j : ℤ)

/-- Every admissible path with a shadowing point has a unique continuous
coding, and that coding intertwines the usual left shift with the map. -/
theorem exists_continuous_coding [CompactSpace X]
    (T : X ≃ₜ X) (R : A → A → Prop) (center : A → X) (c ε : ℝ)
    (expansive : ∀ x y : X, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (small : 2 * ε ≤ c)
    (shadows : ∀ a : Path R, ∃ x : X,
      ∀ n : ℤ, dist (orbit T x n) (center (a.val (-n))) ≤ ε) :
    ∃ π : Path R → X, Continuous π ∧
      (∀ a n, dist (orbit T (π a) n) (center (a.val (-n))) ≤ ε) ∧
      ∀ a, π (shift R a) = T (π a) := by
  choose π near using shadows
  have unique (a : Path R) (x : X)
      (hx : ∀ n, dist (orbit T x n) (center (a.val (-n))) ≤ ε) : π a = x :=
    shadow_unique T c ε expansive small _ _ _ (near a) hx
  have graph : IsClosed π.graph := by
    have identity : π.graph = ⋂ n : ℤ,
        {p : Path R × X | dist (orbit T p.2 n) (center (p.1.val (-n))) ≤ ε} := by
      ext p
      constructor
      · intro hp
        have equal : π p.1 = p.2 := hp
        apply mem_iInter.mpr
        intro n
        change dist (orbit T p.2 n) (center (p.1.val (-n))) ≤ ε
        rw [← equal]
        exact near p.1 n
      · intro hp
        exact unique p.1 p.2 (fun n => mem_iInter.mp hp n)
    rw [identity]
    apply isClosed_iInter
    intro n
    apply isClosed_le _ continuous_const
    exact (((T ^ (-n)).continuous.comp continuous_snd).dist
      (continuous_of_discreteTopology.comp
        ((continuous_apply (-n)).comp (continuous_subtype_val.comp continuous_fst))))
  refine ⟨π, continuous_of_isClosed_graph graph, near, fun a => ?_⟩
  apply unique
  intro n
  rw [orbit_apply_time]
  have estimate := near a (n - 1)
  have index : -(n - 1) = -n + 1 := by omega
  simpa only [shift_apply, index] using estimate

/-- A compact expansive system with bilateral shadowing admits a continuous
surjective coding by a finite graph at every sufficiently small scale. -/
theorem exists_finite_coding [CompactSpace X] (T : X ≃ₜ X) (c ε : ℝ)
    (positiveε : 0 < ε)
    (expansive : ∀ x y : X, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (small : 2 * ε ≤ c)
    (shadowing : ∃ η > 0, ∀ reference : ℤ → X,
      (∀ n, dist (T (reference (n + 1))) (reference n) < η) →
      ∃ q : ℤ → X, (∀ n, T (q (n + 1)) = q n) ∧
        ∀ n, dist (q n) (reference n) < ε) :
    ∃ N : ℕ, ∃ R : Fin N → Fin N → Prop, ∃ center : Fin N → X,
      ∃ π : Path R → X, Continuous π ∧ Surjective π ∧
        (∀ a n, dist (orbit T (π a) n) (center (a.val (-n))) ≤ ε) ∧
        ∀ a, π (shift R a) = T (π a) := by
  classical
  obtain ⟨η, positiveη, shadows⟩ := shadowing
  obtain ⟨δ₀, positiveδ₀, uniform⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous T.continuous) (η / 3) (by positivity)
  let δ := min ε (min δ₀ (η / 3))
  have positiveδ : 0 < δ := lt_min positiveε (lt_min positiveδ₀ (by positivity))
  obtain ⟨s, _subset, finite, covers⟩ :=
    (isCompact_univ : IsCompact (univ : Set X)).finite_cover_balls positiveδ
  let : Fintype s := finite.fintype
  let N := Fintype.card s
  let e : Fin N ≃ s := (Fintype.equivFin s).symm
  let center : Fin N → X := fun i => (e i).val
  have net (x : X) : ∃ i : Fin N, dist x (center i) < δ := by
    obtain ⟨y, ys, close⟩ := mem_iUnion₂.mp (covers (mem_univ x))
    refine ⟨e.symm ⟨y, ys⟩, ?_⟩
    simpa only [center, Equiv.apply_symm_apply] using Metric.mem_ball.mp close
  choose label labelClose using net
  let R : Fin N → Fin N → Prop := fun i j => dist (T (center i)) (center j) < η
  have pathShadows (a : Path R) : ∃ x : X,
      ∀ n, dist (orbit T x n) (center (a.val (-n))) ≤ ε := by
    let reference : ℤ → X := fun n => center (a.val (-n))
    have pseudo (n : ℤ) : dist (T (reference (n + 1))) (reference n) < η := by
      have index : -(n + 1) + 1 = -n := by omega
      simpa only [R, reference, index] using a.property (-(n + 1))
    obtain ⟨q, qStep, qClose⟩ := shadows reference pseudo
    have canonical := eq_canonical T q qStep
    refine ⟨q 0, fun n => ?_⟩
    rw [← congrFun canonical n]
    exact (qClose n).le
  obtain ⟨π, continuous, near, intertwines⟩ :=
    exists_continuous_coding T R center c ε expansive small pathShadows
  refine ⟨N, R, center, π, continuous, ?_, near, intertwines⟩
  intro x
  let a : ℤ → Fin N := fun n => label (orbit T x (-n))
  have path (n : ℤ) : R (a n) (a (n + 1)) := by
    have first := labelClose (orbit T x (-n))
    have second := labelClose (orbit T x (-(n + 1)))
    have δsmall : δ ≤ δ₀ := (min_le_right _ _).trans (min_le_left _ _)
    have ηsmall : δ ≤ η / 3 := (min_le_right _ _).trans (min_le_right _ _)
    have firstUniform : dist (T (center (a n))) (T (orbit T x (-n))) < η / 3 := by
      apply uniform
      rw [dist_comm]
      exact first.trans_le δsmall
    have index : -(n + 1) + 1 = -n := by omega
    have time : T (orbit T x (-n)) = orbit T x (-(n + 1)) := by
      simpa only [index] using step T x (-(n + 1))
    rw [time] at firstUniform
    have triangle := dist_triangle (T (center (a n)))
      (orbit T x (-(n + 1))) (center (a (n + 1)))
    change dist (T (center (a n))) (center (a (n + 1))) < η
    linarith
  let admissible : Path R := ⟨a, path⟩
  refine ⟨admissible, ?_⟩
  apply shadow_unique T c ε expansive small
    (fun n => center (admissible.val (-n))) _ _ (near admissible)
  intro n
  have close := labelClose (orbit T x n)
  have δsmall : δ ≤ ε := min_le_left _ _
  simpa only [admissible, a, neg_neg] using close.le.trans δsmall

end LeanShared.BilateralShadowingCoding
