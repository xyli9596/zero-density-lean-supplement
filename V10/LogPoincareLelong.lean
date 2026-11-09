import V10.LogLaplacianLocal
import V10.HarmonicWeakLaplacian

/-!
# Local Poincaré–Lelong for actual analytic functions

The finite divisor decomposition is extracted from the given analytic function.
The Dirac identity for its logarithmic factors and the vanishing weak Laplacian
of its nonvanishing analytic remainder are proved independently.
-/
noncomputable section
open Set Filter MeasureTheory Metric InnerProductSpace
open scoped Topology ContDiff

namespace V10.LogPoincareLelong
open LogLaplacian LogLaplacianLocal ScalarCompactnessJensen ScalarCompactnessDivisor

/-- The distributional Laplacian of the logarithm of a nonzero analytic
function is its actual analytic divisor, tested locally inside the disk. -/
theorem analytic_log_laplacian {f : ℂ → ℂ} {c w : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hw : w ∈ closedBall c R) (hfw : f w ≠ 0)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ closedBall c R) :
    (∫ z, Laplacian.laplacian φ z * Real.log ‖f z‖) =
      2 * Real.pi * ∑ u ∈ divisorSupport f c R,
        (MeromorphicOn.divisor f (closedBall c R) u : ℝ) * φ u := by
  classical
  obtain ⟨g, hg, hgn, he⟩ := analytic_log_divisor_decomposition_of_point hw hf hfw
  have hhg : HarmonicOnNhd (fun z => Real.log ‖g z‖) (closedBall c R) :=
    fun z hz => (hg z hz).harmonicAt_log_norm (hgn z hz)
  have hsup : Function.support (fun u => (fun z =>
      (MeromorphicOn.divisor f (closedBall c R) u : ℝ) * Real.log ‖z - u‖)) ⊆
      (divisorSupport f c R : Set ℂ) := by
    intro u hu
    apply mem_divisorSupport.mpr
    intro hzero
    apply hu
    ext z
    simp [hzero]
  rw [finsum_eq_sum_of_support_subset _ hsup] at he
  have he' : (fun z => Real.log ‖f z‖) =ᵐ[volume.restrict (closedBall c R)]
      (fun z => (∑ u ∈ divisorSupport f c R,
        (MeromorphicOn.divisor f (closedBall c R) u : ℝ) * Real.log ‖z - u‖) +
          Real.log ‖g z‖) := by
    filter_upwards [he] with z hz
    simpa only [Pi.add_apply, Finset.sum_apply] using hz
  rw [laplacian_pairing_congr_local measurableSet_closedBall hs he']
  simp_rw [mul_add]
  have hi1 : Integrable (fun z => Laplacian.laplacian φ z *
      ∑ u ∈ divisorSupport f c R,
        (MeromorphicOn.divisor f (closedBall c R) u : ℝ) * Real.log ‖z - u‖) := by
    simp_rw [Finset.mul_sum]
    apply integrable_finsetSum
    intro u hu
    simpa only [mul_left_comm] using
      (integrable_laplacian_mul_log u hφ hφc).const_mul
        (MeromorphicOn.divisor f (closedBall c R) u : ℝ)
  have hi2 : Integrable (fun z => Laplacian.laplacian φ z * Real.log ‖g z‖) := by
    have hi := HarmonicWeakLaplacian.integrable_mul_of_local
      (continuous_laplacian hφ hφc) (hasCompactSupport_laplacian hφc)
      (fun z hz => (hhg z (hs (tsupport_laplacian_subset φ hz))).1.continuousAt)
    simpa only [mul_comm] using hi
  have hpot := finite_log_potential_laplacian (divisorSupport f c R)
    (fun u : ℂ => u) (fun u => (MeromorphicOn.divisor f (closedBall c R) u : ℝ)) hφ hφc
  rw [integral_add hi1 hi2, hpot,
    HarmonicWeakLaplacian.harmonic_laplacian_test hhg hφ hφc hs, add_zero]

#print axioms analytic_log_laplacian
end V10.LogPoincareLelong
