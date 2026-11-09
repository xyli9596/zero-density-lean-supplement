import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Genuine smooth approximation with one fixed compact carrier inside an open
domain. The approximants are constructed by Mathlib's convolution theorem;
their compact support is proved from its local averaging property. -/
noncomputable section
open Set Metric
open scoped Topology ContDiff
namespace V10.SmoothTestApproximation

/-- A continuous compactly supported test inside an open domain admits smooth
uniform approximants all supported in a single compact subset of that domain. -/
theorem exists_fixed_compact_smooth_approximation {f : ℂ → ℝ} {U : Set ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hU : IsOpen U)
    (hfs : tsupport f ⊆ U) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ U ∧ tsupport f ⊆ K ∧
      ∀ ε : ℝ, 0 < ε → ∃ g : ℂ → ℝ,
        ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ K ∧
          ∀ z, ‖g z - f z‖ < ε := by
  obtain ⟨δ₀, hδ₀, hδU⟩ := hfc.exists_cthickening_subset_open hU hfs
  let K := cthickening δ₀ (tsupport f)
  have hK : IsCompact K := hfc.cthickening
  have hfK : tsupport f ⊆ K := self_subset_cthickening _
  refine ⟨K, hK, hδU, hfK, ?_⟩
  intro ε hε
  obtain ⟨δ₁, hδ₁, hcont⟩ := Metric.uniformContinuous_iff.mp
    (hfc.uniformContinuous_of_continuous hf) (ε / 2) (half_pos hε)
  let δ := min δ₀ δ₁
  have hδ : 0 < δ := lt_min hδ₀ hδ₁
  obtain ⟨g, hg, havg⟩ := hf.exists_contDiff_dist_le_of_forall_mem_ball_dist_le hδ
  have hgs : Function.support g ⊆ K := by
    intro z hz
    by_contra hzK
    have hz0 : f z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hzK (hfK h))
    have hball : ∀ x ∈ ball z δ, dist (f x) (f z) ≤ 0 := by
      intro x hx
      have hx0 : f x = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hxs
        apply hzK
        exact mem_cthickening_of_dist_le z x δ₀ (tsupport f) hxs
          ((by simpa only [dist_comm] using mem_ball.mp hx : dist z x < δ).le.trans
            (min_le_left _ _))
      simp [hz0, hx0]
    have hg0 := havg z 0 hball
    have hz' : g z = 0 := by
      simpa only [hz0, dist_zero_right, norm_le_zero_iff] using hg0
    exact hz hz'
  have hgt : tsupport g ⊆ K := closure_minimal hgs hK.isClosed
  refine ⟨g, hg, HasCompactSupport.of_support_subset_isCompact hK hgs, hgt, ?_⟩
  intro z
  rw [← dist_eq_norm]
  apply (havg z (ε / 2) ?_).trans_lt (half_lt_self hε)
  intro x hx
  exact (hcont ((mem_ball.mp hx).trans_le (min_le_right _ _))).le

#print axioms exists_fixed_compact_smooth_approximation
end V10.SmoothTestApproximation
