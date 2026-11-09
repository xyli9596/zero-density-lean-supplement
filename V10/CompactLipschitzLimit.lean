import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# Compact uniform convergence from eventual common Lipschitz bounds

The parameter filter can be real `atTop`, so the result applies directly to
continuous scaling parameters and also to arbitrary sampling subsequences.
The common Lipschitz bound need hold only eventually. Pointwise convergence
proves that the limit retains the same Lipschitz constant; Ascoli's theorem
then upgrades convergence to uniform convergence on the compact set.

This is the topology bridge in the vector-limit argument. The actual ODE
must still supply the common Lipschitz bound and pointwise limit; neither is
proved here, and no subharmonic L1-local compactness conclusion is asserted.
-/

noncomputable section
open Filter Set
open scoped Topology NNReal
namespace V10.CompactLipschitzLimit

variable {ι X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  {l : Filter ι} [NeBot l] {F : ι → X → Y} {f : X → Y}
  {K : Set X} {C : ℝ≥0}

/-- Eventual common Lipschitz estimates pass to the pointwise limit,
without compactness or continuity being an additional hypothesis. -/
theorem lipschitzOnWith_of_pointwise_limit
    (hLip : ∀ᶠ i in l, LipschitzOnWith C (F i) K)
    (hpoint : ∀ x ∈ K, Tendsto (fun i => F i x) l (𝓝 (f x))) :
    LipschitzOnWith C f K := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  exact le_of_tendsto ((hpoint x hx).dist (hpoint y hy))
    (hLip.mono fun i hi => hi.dist_le_mul x hx y hy)

/-- The limit is continuous on the set under the same eventual hypotheses. -/
theorem continuousOn_of_pointwise_limit
    (hLip : ∀ᶠ i in l, LipschitzOnWith C (F i) K)
    (hpoint : ∀ x ∈ K, Tendsto (fun i => F i x) l (𝓝 (f x))) :
    ContinuousOn f K :=
  (lipschitzOnWith_of_pointwise_limit hLip hpoint).continuousOn

/-- On a compact set, eventual common Lipschitz control and pointwise
convergence imply actual uniform convergence. There is no assumed uniform
convergence, precompact range, or chosen convergent subsequence. -/
theorem tendstoUniformlyOn_of_pointwise_limit (hK : IsCompact K)
    (hLip : ∀ᶠ i in l, LipschitzOnWith C (F i) K)
    (hpoint : ∀ x ∈ K, Tendsto (fun i => F i x) l (𝓝 (f x))) :
    TendstoUniformlyOn F f l K := by
  classical
  let G : ι → X → Y := fun i => if LipschitzOnWith C (F i) K then F i else f
  have hfLip := lipschitzOnWith_of_pointwise_limit hLip hpoint
  have hGLip : ∀ i, LipschitzOnWith C (G i) K := by
    intro i
    dsimp [G]
    split_ifs with h
    · exact h
    · exact hfLip
  have hGpoint : ∀ x ∈ K, Tendsto (fun i => G i x) l (𝓝 (f x)) := by
    intro x hx
    apply (hpoint x hx).congr'
    filter_upwards [hLip] with i hi
    simp [G, hi]
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hEq : Equicontinuous (fun i (x : K) => G i x) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => (C : ℝ) * r)
      (by simpa using ((tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 0) (𝓝 0)).const_mul (C : ℝ)))
    intro x y i
    exact (hGLip i).dist_le_mul x x.property y y.property
  have hPi : Tendsto (fun i (x : K) => G i x) l (𝓝 (fun x : K => f x)) :=
    tendsto_pi_nhds.mpr fun x => hGpoint x x.property
  have hUniform : TendstoUniformly (fun i (x : K) => G i x) (fun x : K => f x) l := by
    exact UniformFun.tendsto_iff_tendstoUniformly.mp
      ((hEq.tendsto_uniformFun_iff_pi l (fun x : K => f x)).mpr hPi)
  have hOn : TendstoUniformlyOn G f l K :=
    tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr hUniform
  apply hOn.congr
  filter_upwards [hLip] with i hi
  intro x hx
  simp [G, hi]

/-- A bundled interface giving both the actual uniform limit and its exact
inherited Lipschitz constant. -/
theorem compact_limit (hK : IsCompact K)
    (hLip : ∀ᶠ i in l, LipschitzOnWith C (F i) K)
    (hpoint : ∀ x ∈ K, Tendsto (fun i => F i x) l (𝓝 (f x))) :
    TendstoUniformlyOn F f l K ∧ LipschitzOnWith C f K ∧ ContinuousOn f K :=
  ⟨tendstoUniformlyOn_of_pointwise_limit hK hLip hpoint,
    lipschitzOnWith_of_pointwise_limit hLip hpoint,
    continuousOn_of_pointwise_limit hLip hpoint⟩

#print axioms lipschitzOnWith_of_pointwise_limit
#print axioms tendstoUniformlyOn_of_pointwise_limit
#print axioms compact_limit
end V10.CompactLipschitzLimit
