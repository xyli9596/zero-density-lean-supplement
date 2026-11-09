import V10.HingeLaplacian
import V10.LocalSupportFace
import V10.RayMeasureGeometry
import Mathlib.Analysis.Complex.Isometry

/-! Rotation of the genuine Cartesian hinge identity to the geometric normal
and tangent of an actual polygon face. -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff SchwartzMap
namespace V10.RotatedHingeLaplacian
open ZeroDensity.PolygonFaces
set_option backward.isDefEq.respectTransparency false

def rotate (θ : ℝ) : ℂ ≃ₗᵢ[ℝ] ℂ := rotation (Circle.exp θ)

theorem rotate_apply (θ : ℝ) (z : ℂ) :
    rotate θ z = Complex.exp ((θ : ℂ) * Complex.I) * z := rfl

theorem tangent_rotate (θ : ℝ) (z : ℂ) : angularTangent θ (rotate θ z) = z.im := by
  rw [LocalSupportFace.tangent_coordinates, rotate_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  calc
    _ = (Real.sin θ ^ 2 + Real.cos θ ^ 2) * z.im := by ring
    _ = z.im := by rw [Real.sin_sq_add_cos_sq, one_mul]

theorem normal_rotate (θ : ℝ) (z : ℂ) : normalLinear θ (rotate θ z) = z.re := by
  rw [rotate_apply]
  change Real.cos θ * (Complex.exp ((θ : ℂ) * Complex.I) * z).re +
    Real.sin θ * (Complex.exp ((θ : ℂ) * Complex.I) * z).im = _
  simp only [Complex.mul_re, Complex.mul_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  calc
    _ = (Real.sin θ ^ 2 + Real.cos θ ^ 2) * z.re := by ring
    _ = z.re := by rw [Real.sin_sq_add_cos_sq, one_mul]

theorem laplacian_pullback (R : ℂ ≃ₗᵢ[ℝ] ℂ) (φ : 𝓢(ℂ, ℝ)) :
    Laplacian.laplacian (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      R.toContinuousLinearEquiv φ) =
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ R.toContinuousLinearEquiv
      (Laplacian.laplacian φ) := by
  rw [SchwartzMap.laplacian_eq_sum Complex.orthonormalBasisOneI,
    SchwartzMap.laplacian_eq_sum (Complex.orthonormalBasisOneI.map R), map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv,
    SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv]
  rfl

theorem laplacian_comp_isometry {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (R : ℂ ≃ₗᵢ[ℝ] ℂ) (z : ℂ) :
    Laplacian.laplacian (fun w => φ (R w)) z = Laplacian.laplacian φ (R z) := by
  have h := congrArg (fun ψ : 𝓢(ℂ, ℝ) => ψ z)
    (laplacian_pullback R (hφc.toSchwartzMap hφ))
  simp only [SchwartzMap.laplacian_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    Function.comp_def] at h
  exact h

/-- The angular hinge has the full line length measure as its actual weak
Laplacian. The tangent is the same geometric quantity as in the face jump. -/
theorem angular_hinge_laplacian_test (θ : ℝ) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ z, Laplacian.laplacian φ z * max 0 (angularTangent θ z)) =
      ∫ r : ℝ, φ (RadialCutoffGeometry.rayPoint r θ) := by
  have hs : HasCompactSupport (fun z => φ (rotate θ z)) :=
    hφc.comp_homeomorph (rotate θ).toHomeomorph
  have hc : ContDiff ℝ ∞ (fun z => φ (rotate θ z)) :=
    hφ.comp (rotate θ).toContinuousLinearEquiv.contDiff
  have h := HingeLaplacian.hinge_laplacian_test hc hs
  simp_rw [laplacian_comp_isometry hφ hφc] at h
  have he := (rotate θ).measurePreserving.integral_comp
    (rotate θ).toHomeomorph.measurableEmbedding
    (fun z => Laplacian.laplacian φ z * max 0 (angularTangent θ z))
  simp only [tangent_rotate] at he
  rw [he] at h
  convert h using 1
  congr 1
  funext r
  congr 1
  simp only [RadialCutoffGeometry.rayPoint, rotate_apply, mul_comm]

theorem normal_rayPoint (θ r : ℝ) :
    normalLinear θ (RadialCutoffGeometry.rayPoint r θ) = r := by
  simpa only [RadialCutoffGeometry.rayPoint, rotate_apply, mul_comm, Complex.ofReal_re] using
    normal_rotate θ (r : ℂ)

/-- On the positive normal half-plane only the positive half of the supporting
line meets the test support, yielding exactly the ray measure in the paper. -/
theorem angular_hinge_laplacian_ray (θ : ℝ) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ {z | 0 < normalLinear θ z}) :
    (∫ z, Laplacian.laplacian φ z * max 0 (angularTangent θ z)) =
      ∫ z, φ z ∂RayMeasureGeometry.rayLengthMeasure θ := by
  rw [angular_hinge_laplacian_test θ hφ hφc,
    RayMeasureGeometry.integral_rayLengthMeasure hφ.continuous θ]
  have he : (fun r : ℝ => φ (RadialCutoffGeometry.rayPoint r θ)) =
      (Ioi (0 : ℝ)).indicator (fun r => φ (RadialCutoffGeometry.rayPoint r θ)) := by
    funext r
    by_cases hr : 0 < r
    · simp [hr]
    · simp only [mem_Ioi, hr, not_false_eq_true, indicator_of_notMem]
      apply image_eq_zero_of_notMem_tsupport
      intro hz
      have hp := hs hz
      exact hr (by simpa only [mem_ofPred_eq, normal_rayPoint] using hp)
  calc
    _ = ∫ r, (Ioi (0 : ℝ)).indicator
        (fun u => φ (RadialCutoffGeometry.rayPoint u θ)) r := congrArg (fun f => ∫ r, f r) he
    _ = _ := integral_indicator measurableSet_Ioi

theorem projection_harmonic (p : ℂ) :
    InnerProductSpace.HarmonicOnNhd (LocalSupportFace.projection p) univ := by
  have he : LocalSupportFace.projection p = fun z => (star p * z).re := by
    funext z
    simp [LocalSupportFace.projection, Complex.mul_re]
  rw [he]
  intro z hz
  apply AnalyticAt.harmonicAt_re
  fun_prop

/-- A linear piece contributes no weak Laplacian; the actual nonnegative
face coefficient multiplies the unit angular hinge ray measure. -/
theorem linear_add_hinge_laplacian_ray (p : ℂ) (d θ : ℝ) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ {z | 0 < normalLinear θ z}) :
    (∫ z, Laplacian.laplacian φ z *
      (LocalSupportFace.projection p z + d * max 0 (angularTangent θ z))) =
      d * ∫ z, φ z ∂RayMeasureGeometry.rayLengthMeasure θ := by
  have hp : Integrable (fun z => Laplacian.laplacian φ z * LocalSupportFace.projection p z) :=
    ((LogLaplacianLocal.continuous_laplacian hφ hφc).mul
      (LocalSupportFace.projection_continuous p)).integrable_of_hasCompactSupport
        (LogLaplacianLocal.hasCompactSupport_laplacian hφc).mul_right
  have ht : Continuous (fun z => angularTangent θ z) := by
    simp only [LocalSupportFace.tangent_coordinates]
    fun_prop
  have hi : Integrable (fun z => Laplacian.laplacian φ z * max 0 (angularTangent θ z)) :=
    ((LogLaplacianLocal.continuous_laplacian hφ hφc).mul
      (continuous_const.max ht)).integrable_of_hasCompactSupport
        (LogLaplacianLocal.hasCompactSupport_laplacian hφc).mul_right
  have he : (fun z => Laplacian.laplacian φ z *
      (LocalSupportFace.projection p z + d * max 0 (angularTangent θ z))) =
      (fun z => Laplacian.laplacian φ z * LocalSupportFace.projection p z +
        d * (Laplacian.laplacian φ z * max 0 (angularTangent θ z))) := by
    funext z
    ring
  rw [he, integral_add hp (hi.const_mul d), integral_const_mul,
    HarmonicWeakLaplacian.harmonic_laplacian_test (projection_harmonic p) hφ hφc
      (subset_univ _), angular_hinge_laplacian_ray θ hφ hφc hs, zero_add]

#print axioms angular_hinge_laplacian_test
#print axioms angular_hinge_laplacian_ray
#print axioms linear_add_hinge_laplacian_ray
end V10.RotatedHingeLaplacian
