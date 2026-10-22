module

public import LeanShared.Dynamics.ControlledPlaqueClosure

/-! Positivity with departure weights positive only in a fixed core collar.
All geometric plaque controls used to propagate zeros stay in this collar.
Backward parents are taken in a compact localized support, rather than in
an unweighted left support which may contain zero-weight sources. -/

@[expose] public noncomputable section

open Set Function Filter
open scoped Topology

namespace LeanShared.ControlledPlaqueClosure

variable {X Ω : Type*} [MetricSpace X] [TopologicalSpace Ω]

omit [TopologicalSpace Ω] in
theorem zero_on_core_of_zero_on_collar (T : X ≃ₜ X) (F : X × Ω → X) (zero : Ω)
    (hFzero : ∀ x, F (x, zero) = T x) (V K G : Set X)
    (hcoreV : isolatedCore T K ⊆ V)
    (hcoreG : isolatedCore T K ⊆ G)
    (hcover : ∀ p ∈ isolatedCore T K, ∃ W : Set X, IsOpen W ∧ p ∈ W ∧ W ⊆ V ∧
      ∀ y ∈ W, ∃ ω : Ω, F (T.symm p, ω) = y)
    (htrans : forwardTransitiveOn T (isolatedCore T K))
    (g : X → ℝ) (hgc : ContinuousOn g K)
    (hzeroStep : ∀ x ∈ K, x ∈ G → ∀ ω : Ω, F (x, ω) ∈ V → g x = 0 → g (F (x, ω)) = 0)
    {x : X} (hx : x ∈ isolatedCore T K) (hgx : g x = 0) :
    EqOn g (fun _ => 0) (isolatedCore T K) := by
  have hcoreK : isolatedCore T K ⊆ K := fun _ hy => forwardTrapped_subset T K hy.1
  obtain ⟨W, hW, hpW, hWV, hnoise⟩ := hcover (T x) (mapsTo_isolatedCore T K hx)
  have hgW : ∀ y ∈ W, g y = 0 := by
    intro y hy
    obtain ⟨ω, hω⟩ := hnoise y hy
    rw [T.symm_apply_apply] at hω
    have hh := hzeroStep x (hcoreK hx) (hcoreG hx) ω (hω.symm ▸ hWV hy) hgx
    rwa [hω] at hh
  have hforward : ∀ a ∈ isolatedCore T K, g a = 0 → ∀ n : ℕ, g ((T : X → X)^[n] a) = 0 := by
    intro a ha hga n
    induction n with
    | zero => exact hga
    | succ n ih =>
        have hn := iterate_mem_isolatedCore T K ha n
        have hTn := mapsTo_isolatedCore T K hn
        have hh := hzeroStep _ (hcoreK hn) (hcoreG hn) zero (by rw [hFzero]; exact hcoreV hTn) ih
        simpa only [hFzero, iterate_succ_apply'] using hh
  let D : Set X := ⋃ n : ℕ, (T : X → X)^[n] '' (isolatedCore T K ∩ W)
  have hDcore : D ⊆ isolatedCore T K := by
    intro y hy
    obtain ⟨n, a, ha, rfl⟩ := mem_iUnion.mp hy
    exact iterate_mem_isolatedCore T K ha.1 n
  have hgD : EqOn g (fun _ => 0) D := by
    intro y hy
    obtain ⟨n, a, ha, rfl⟩ := mem_iUnion.mp hy
    exact hforward a ha.1 (hgW a ha.2) n
  exact hgD.of_subset_closure (hgc.mono hcoreK) continuousOn_const hDcore
    (htrans W hW ⟨T x, mapsTo_isolatedCore T K hx, hpW⟩)

/-- A localized compact-support parent construction plus genuine collar
plaques proves core positivity. Departure zero propagation is used only
where the weight is positive; no positivity on the whole isolating set is
required. The parent and seed hypotheses concern the localized product
support and can be supplied by its actual stationary Doob law. -/
theorem core_positive_of_collar_plaques
    (T : X ≃ₜ X) (F : X × Ω → X) (zero : Ω)
    (hFzero : ∀ x, F (x, zero) = T x) (V K G : Set X)
    (hVK : V ⊆ K) (hK : IsCompact K)
    (hcoreV : isolatedCore T K ⊆ V) (hcoreG : isolatedCore T K ⊆ G)
    (hcover : ∀ p ∈ isolatedCore T K, ∃ W : Set X, IsOpen W ∧ p ∈ W ∧
      W ⊆ V ∩ G ∧ ∀ y ∈ W, ∃ ω : Ω, F (T.symm p, ω) = y)
    (htrans : forwardTransitiveOn T (isolatedCore T K))
    (plaque : (ℤ → Ω) → Set X)
    (hlsc : ∀ ω : ℤ → Ω, ∀ ωn : ℕ → ℤ → Ω, Tendsto ωn atTop (𝓝 ω) →
      ∀ z ∈ plaque ω, ∃ zn : ℕ → X, Tendsto zn atTop (𝓝 z) ∧
        ∀ k, zn k ∈ plaque (ωn k))
    (hback : ∀ ω : ℤ → Ω, ∀ z ∈ plaque ω, ∃ b : ℕ → X, b 0 = z ∧
      (∀ n, b n ∈ V ∩ G) ∧ ∀ n, F (b (n + 1), backwardNoise ω n) = b n)
    (hcapture : ∀ ω : ℤ → Ω, ∀ b : ℕ → X, (∀ n, b n ∈ V) →
      (∀ n, F (b (n + 1), backwardNoise ω n) = b n) →
      (∀ᶠ n : ℕ in atTop, b n ∈ G) → ∃ j : ℕ, b j ∈ plaque (backwardShift ω j))
    (g : X → ℝ) (hgc : ContinuousOn g K) (hg0 : ∀ x ∈ K, 0 ≤ g x)
    (hzeroStep : ∀ x ∈ K, x ∈ G → ∀ ω : Ω, F (x, ω) ∈ V →
      g x = 0 → g (F (x, ω)) = 0)
    (S : Set X) (hSV : S ⊆ V ∩ G)
    (hparent : ∀ p ∈ S, ∃ x ∈ S, ∃ ω : Ω, F (x, ω) = p)
    (hseed : ∃ p ∈ S, 0 < g p) : ∀ x ∈ isolatedCore T K, 0 < g x := by
  let L := V ∩ G
  have hLK : L ⊆ K := fun _ hx => hVK hx.1
  have hcoreL : isolatedCore T K ⊆ L := fun _ hx => ⟨hcoreV hx, hcoreG hx⟩
  have hplaque := plaque_subset_closure_reachable T F zero hFzero L K
    hLK hK hcoreL hcover plaque hlsc hback
  obtain ⟨p, hp, hgp⟩ := hseed
  have hSkg : S ⊆ K ∩ G := fun _ hx => ⟨hVK (hSV hx).1, (hSV hx).2⟩
  have hstepkg : ∀ x ∈ K ∩ G, ∀ ω : Ω, F (x, ω) ∈ L →
      g x = 0 → g (F (x, ω)) = 0 :=
    fun x hx ω hy => hzeroStep x hx.1 hx.2 ω hy.1
  obtain ⟨z, noise, _, hz, hstep⟩ := exists_positive_backward_orbit F L (K ∩ G) S
    hSkg g (fun x hx => hg0 x hx.1) (fun x hx _ => hSV hx) hstepkg hparent p hp hgp
  let ω := completeBackwardNoise zero noise
  have hstep' : ∀ n, F (z (n + 1), backwardNoise ω n) = z n := by
    intro n
    simpa only [ω, backwardNoise_complete] using hstep n
  obtain ⟨j, hj⟩ := hcapture ω z (fun n => (hz n).2.1.1) hstep'
    (Eventually.of_forall fun n => (hz n).2.1.2)
  intro x hx
  by_contra hbad
  have hgx : g x = 0 := le_antisymm (le_of_not_gt hbad)
    (hg0 x (forwardTrapped_subset T K hx.1))
  have hcoreZero := zero_on_core_of_zero_on_collar T F zero hFzero L K G
    hcoreL hcoreG hcover htrans g hgc
    (fun y hy hyG ω hyL => hzeroStep y hy hyG ω hyL.1) hx hgx
  have hreachZero : EqOn g (fun _ => 0) (reachable F L (isolatedCore T K)) := by
    rintro y ⟨a, ha, _, hp⟩
    induction hp with
    | refl => exact hcoreZero ha
    | @tail b c hp hs ih =>
        obtain ⟨v, hv⟩ := hs.2.2
        have hh := hzeroStep b (hVK hs.1.1) hs.1.2 v
          (hv.symm ▸ hs.2.1.1) ih
        rwa [hv] at hh
  have hclosureK : closure (reachable F L (isolatedCore T K)) ⊆ K :=
    closure_minimal ((reachable_subset_live F L _).trans hLK) hK.isClosed
  have hclosedZero := hreachZero.of_subset_closure (hgc.mono hclosureK)
    continuousOn_const subset_closure (Subset.refl _)
  exact (ne_of_gt (hz j).2.2) (hclosedZero (hplaque (backwardShift ω j) hj))

end LeanShared.ControlledPlaqueClosure
