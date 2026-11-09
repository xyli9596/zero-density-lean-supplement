import V10.LogLaplacian
import V10.ScalarCompactnessDivisor
import V10.ScalarCompactnessL1Bounds

/-! Finite logarithmic potentials and local test-function pairings. -/
noncomputable section
open Set Filter MeasureTheory Metric InnerProductSpace
open scoped Topology ContDiff

namespace V10.LogLaplacianLocal
open LogLaplacian ScalarCompactnessJensen ScalarCompactnessDivisor

/-- A test Laplacian vanishes off the topological support of its test function. -/
theorem laplacian_eq_zero_of_notMem_tsupport {φ : ℂ → ℝ} {z : ℂ}
    (hz : z ∉ tsupport φ) : Laplacian.laplacian φ z = 0 := by
  have h := (InnerProductSpace.laplacian_congr_nhds
    (notMem_tsupport_iff_eventuallyEq.mp hz)).self_of_nhds
  have hz0 : Laplacian.laplacian (0 : ℂ → ℝ) z = 0 := by
    change Laplacian.laplacian (fun _ : ℂ => (0 : ℝ)) z = 0
    simp
  exact h.trans hz0

theorem support_laplacian_subset (φ : ℂ → ℝ) :
    Function.support (Laplacian.laplacian φ) ⊆ tsupport φ := by
  intro z hz
  by_contra hn
  exact hz (laplacian_eq_zero_of_notMem_tsupport hn)

theorem tsupport_laplacian_subset (φ : ℂ → ℝ) :
    tsupport (Laplacian.laplacian φ) ⊆ tsupport φ :=
  closure_minimal (support_laplacian_subset φ) isClosed_closure

theorem hasCompactSupport_laplacian {φ : ℂ → ℝ} (hs : HasCompactSupport φ) :
    HasCompactSupport (Laplacian.laplacian φ) :=
  HasCompactSupport.of_support_subset_isCompact hs (support_laplacian_subset φ)

theorem continuous_laplacian {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hs : HasCompactSupport φ) : Continuous (Laplacian.laplacian φ) := by
  have he : (Laplacian.laplacian (hs.toSchwartzMap hφ) : ℂ → ℝ) =
      Laplacian.laplacian φ := funext (SchwartzMap.laplacian_apply _)
  rw [← he]
  exact (Laplacian.laplacian (hs.toSchwartzMap hφ)).continuous

theorem integrable_laplacian_mul_log (a : ℂ) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) :
    Integrable (fun z => Laplacian.laplacian φ z * Real.log ‖z - a‖) := by
  exact (ZeroDensity.PlanarLogIntegrability.locallyIntegrable_log_norm_sub a).integrable_smul_left_of_hasCompactSupport
      (continuous_laplacian hφ hs) (hasCompactSupport_laplacian hs)

/-- The logarithmic potential of a finite weighted divisor has exactly the
corresponding finite atomic test pairing. -/
theorem finite_log_potential_laplacian {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (w : ι → ℝ) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) :
    (∫ z, Laplacian.laplacian φ z * ∑ i ∈ s, w i * Real.log ‖z - a i‖) =
      2 * Real.pi * ∑ i ∈ s, w i * φ (a i) := by
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · simp_rw [show ∀ i z, Laplacian.laplacian φ z * (w i * Real.log ‖z - a i‖) =
        w i * (Laplacian.laplacian φ z * Real.log ‖z - a i‖) by intros; ring,
      integral_const_mul, log_laplacian_test_sub _ hφ hs]
    exact Finset.sum_congr rfl fun i _ => by ring
  · intro i hi
    simpa only [mul_left_comm] using (integrable_laplacian_mul_log (a i) hφ hs).const_mul (w i)

/-- Equality a.e. on the support domain suffices for global Laplacian pairings. -/
theorem laplacian_pairing_congr_local {φ f g : ℂ → ℝ} {D : Set ℂ}
    (hD : MeasurableSet D) (hs : tsupport φ ⊆ D)
    (he : f =ᵐ[volume.restrict D] g) :
    (∫ z, Laplacian.laplacian φ z * f z) = ∫ z, Laplacian.laplacian φ z * g z := by
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hD).mp he] with z hz
  by_cases hzd : z ∈ D
  · rw [hz hzd]
  · have hn : z ∉ tsupport φ := fun h => hzd (hs h)
    simp [laplacian_eq_zero_of_notMem_tsupport hn]

#print axioms finite_log_potential_laplacian
end V10.LogLaplacianLocal
