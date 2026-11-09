/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in V10/Physlib/LICENSE.

This bridge uses the genuine distributional logarithmic fundamental solution from
Physlib, commit 6fd6640d23ae4df6ba93ede701528f2f08718f95, adapted to Lean 4.33.
The upstream proof uses regularization, integration by parts, spherical coordinates,
and the radial fundamental theorem of calculus; the Dirac mass is not a hypothesis.
-/
import V10.Physlib.SpaceAndTime.Space.Norm.Basic
import ZeroDensity.LogKernelBoundary
import ZeroDensity.L1TestPairing

open MeasureTheory InnerProductSpace
open scoped Topology SchwartzMap ContDiff

noncomputable section
namespace V10.LogLaplacian

/-- Physlib's distributional Laplacian is the transpose of the actual Schwartz
Laplacian, and hence of Mathlib's classical Laplacian on test functions. -/
theorem distLaplacian_apply {d : ℕ} (u : Physlib.Distribution ℝ (Space d) ℝ)
    (φ : 𝓢(Space d, ℝ)) :
    Space.distLaplacian u φ = u (Laplacian.laplacian φ) := by
  rw [Space.distLaplacian, LinearMap.comp_apply,
    Space.distDiv_apply_eq_sum_distDeriv,
    SchwartzMap.laplacian_eq_sum Space.basis, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Space.distDeriv_apply, Physlib.Distribution.fderivD_apply,
    Space.distGrad_apply, PiLp.neg_apply]
  rw [neg_neg]
  rfl

/-- The distribution identity stated as an ordinary integral of a genuine
Mathlib Laplacian on a Schwartz test function. -/
theorem space_log_laplacian (φ : 𝓢(Space 2, ℝ)) :
    (∫ x : Space 2, Laplacian.laplacian (φ : Space 2 → ℝ) x * Real.log ‖x‖) =
      (2 * volume.real (Metric.ball (0 : Space 2) 1)) * φ 0 := by
  have h := congrArg (fun u => u φ) Space.distLaplacian_fundamentalSolution_log_norm
  rw [distLaplacian_apply, Space.distOfFunction_apply] at h
  simpa only [SchwartzMap.laplacian_apply, smul_eq_mul,
    _root_.smul_apply, Physlib.Distribution.diracDelta_apply] using h

/-- The canonical real-linear isometry from the imported Euclidean plane to ℂ. -/
def spaceComplex : Space 2 ≃ₗᵢ[ℝ] ℂ :=
  Space.basis.repr.trans Complex.orthonormalBasisOneI.repr.symm

/-- Laplacians of Schwartz functions commute with the isometric identification. -/
theorem laplacian_pullback (φ : 𝓢(ℂ, ℝ)) :
    Laplacian.laplacian (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      spaceComplex.toContinuousLinearEquiv φ) =
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ spaceComplex.toContinuousLinearEquiv
      (Laplacian.laplacian φ) := by
  rw [SchwartzMap.laplacian_eq_sum Space.basis,
    SchwartzMap.laplacian_eq_sum (Space.basis.map spaceComplex), map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv,
    SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv]
  rfl

theorem space_unit_ball_volume : volume.real (Metric.ball (0 : Space 2) 1) = Real.pi := by
  rw [Measure.real, InnerProductSpace.volume_ball_of_dim_even (k := 1) (by simp)]
  simp [Real.pi_pos.le]

/-- The planar logarithm has distributional Laplacian `2πδ₀`, stated using
Mathlib's actual Laplacian and the usual volume measure on ℂ. -/
theorem complex_log_laplacian (φ : 𝓢(ℂ, ℝ)) :
    (∫ z : ℂ, Laplacian.laplacian (φ : ℂ → ℝ) z * Real.log ‖z‖) =
      2 * Real.pi * φ 0 := by
  let ψ := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    spaceComplex.toContinuousLinearEquiv φ
  have h := space_log_laplacian ψ
  rw [space_unit_ball_volume] at h
  have hΔ (x : Space 2) : Laplacian.laplacian (ψ : Space 2 → ℝ) x =
      Laplacian.laplacian (φ : ℂ → ℝ) (spaceComplex x) := by
    rw [← SchwartzMap.laplacian_apply, laplacian_pullback]
    exact SchwartzMap.laplacian_apply φ (spaceComplex x)
  simp_rw [hΔ, ← spaceComplex.norm_map] at h
  have hchange := spaceComplex.measurePreserving.integral_comp
    spaceComplex.toHomeomorph.measurableEmbedding
    (fun z : ℂ => Laplacian.laplacian (φ : ℂ → ℝ) z * Real.log ‖z‖)
  rw [hchange] at h
  simpa [ψ] using h

/-- Compactly supported smooth test functions satisfy the same identity. -/
theorem log_laplacian_test {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hs : HasCompactSupport φ) :
    (∫ z : ℂ, Laplacian.laplacian φ z * Real.log ‖z‖) = 2 * Real.pi * φ 0 := by
  exact complex_log_laplacian (hs.toSchwartzMap hφ)

/-- Translation covariance of the actual planar Laplacian. -/
theorem laplacian_translate (φ : ℂ → ℝ) (a z : ℂ) :
    Laplacian.laplacian (fun w => φ (w + a)) z = Laplacian.laplacian φ (z + a) := by
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    iteratedFDeriv_comp_add_right]

/-- The singular logarithmic kernel at every point carries exactly `2π` mass. -/
theorem log_laplacian_test_sub (a : ℂ) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) :
    (∫ z : ℂ, Laplacian.laplacian φ z * Real.log ‖z - a‖) = 2 * Real.pi * φ a := by
  have h := log_laplacian_test (φ := fun z => φ (z + a))
    (hφ.comp (contDiff_id.add contDiff_const))
    (hs.comp_homeomorph (Homeomorph.addRight a))
  simp only [laplacian_translate, zero_add] at h
  have hchange := integral_add_right_eq_self (μ := (volume : Measure ℂ))
    (fun z : ℂ => Laplacian.laplacian φ z * Real.log ‖z - a‖) a
  simp only [add_sub_cancel_right] at hchange
  exact hchange.symm.trans h

/-- Direct compatibility with the existing weak Laplacian pairing used for
local L¹ convergence and zero counting. -/
theorem weakLaplacianPairing_log_kernel (a : ℂ) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) :
    ZeroDensity.L1TestPairing.weakLaplacianPairing volume
      (fun z => Real.log ‖z - a‖) φ = 2 * Real.pi * φ a :=
  log_laplacian_test_sub a hφ hs

#print axioms distLaplacian_apply
#print axioms space_log_laplacian
#print axioms complex_log_laplacian
#print axioms log_laplacian_test
#print axioms log_laplacian_test_sub
end V10.LogLaplacian
