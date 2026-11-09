import V10.AnalyticZeroMeasure
import V10.ScalarWeakLaplacian

/-!
# Scalar L¹ convergence implies convergence of the actual analytic zero measures

The measure on the left is constructed from actual analytic multiplicities.
Its Poincaré–Lelong identity is proved, not postulated. This module only supplies
the analytic-to-measure bridge; the scalar ODE L¹ theorem supplies its convergence
hypothesis in the application.
-/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace V10.ZeroMeasureTestConvergence
open AnalyticZeroMeasure LogLaplacianLocal

/-- Compact support localizes the genuine Laplacian pairing without any
assumption on the represented function away from the test domain. -/
theorem setIntegral_laplacian_mul {φ u : ℂ → ℝ} {D : Set ℂ}
    (hs : tsupport φ ⊆ D) :
    (∫ z in D, Laplacian.laplacian φ z * u z) =
      ∫ z, Laplacian.laplacian φ z * u z := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have hn : z ∉ tsupport φ := fun h => hz (hs h)
  simp [laplacian_eq_zero_of_notMem_tsupport hn]

/-- Smooth-test convergence of the actual positive normalized divisor measures.
Analyticity and nontriviality are only required eventually, as in exterior
sector rescaling. -/
theorem normalized_divisor_measure_tendsto_test
    {ι : Type*} {l : Filter ι} {f : ι → ℂ → ℂ} {q : ι → ℝ}
    {c : ℂ} {R : ℝ} {H φ : ℂ → ℝ}
    (hinputs : ∀ᶠ i in l, 0 < q i ∧
      AnalyticOnNhd ℂ (f i) (closedBall c R) ∧
      ∃ w ∈ closedBall c R, f i w ≠ 0)
    (hH : IntegrableOn H (closedBall c R))
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ closedBall c R)
    (hL1 : Tendsto (fun i => ∫ z in closedBall c R,
      ‖Real.log ‖f i z‖ / q i - H z‖) l (𝓝 0)) :
    Tendsto (fun i => ∫ z, φ z ∂normalizedDivisorMeasure (f i) c R (q i)) l
      (𝓝 ((∫ z, Laplacian.laplacian φ z * H z) / (2 * Real.pi))) := by
  have hu : ∀ᶠ i in l, IntegrableOn (fun z => Real.log ‖f i z‖ / q i)
      (closedBall c R) := by
    filter_upwards [hinputs] with i hi
    obtain ⟨w, hw, hfw⟩ := hi.2.2
    exact (ScalarCompactnessL1Bounds.log_inputs_on_disk_of_point hw hi.2.1 hfw).1.div_const _
  have ht := ScalarWeakLaplacian.weakLaplacianPairing_tendsto_on_compact_eventually
    (isCompact_closedBall c R) hu hH (continuous_laplacian hφ hφc) hL1
  have he (u : ℂ → ℝ) : ZeroDensity.L1TestPairing.weakLaplacianPairing
      (volume.restrict (closedBall c R)) u φ =
      ∫ z, Laplacian.laplacian φ z * u z := setIntegral_laplacian_mul hs
  simp_rw [he] at ht
  apply (ht.div_const (2 * Real.pi)).congr'
  filter_upwards [hinputs] with i hi
  obtain ⟨w, hw, hfw⟩ := hi.2.2
  rw [normalized_log_laplacian_measure hi.1 hi.2.1 hw hfw hφ hφc hs]
  field_simp

#print axioms normalized_divisor_measure_tendsto_test
end V10.ZeroMeasureTestConvergence
