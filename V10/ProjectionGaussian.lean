import V10.ProjectionGaussianReal
import Mathlib.Tactic

/-! Actual complex Gaussian projections and logarithmic integrability.
The complex Gaussian is the standard real isotropic Gaussian scaled by
`sqrt (1/2)`, so each real coordinate has variance `1/2`. Projection laws
are proved through characteristic functions and exact dual norms.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace V10.ProjectionGaussian
open ProjectionGaussianReal
set_option backward.isDefEq.respectTransparency false

section Norms
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The norm of a real functional after a complex scalar projection is
exactly the product of the two norms, rather than only bounded by it. -/
theorem norm_real_comp_complex (F : E →L[ℂ] ℂ) (L : ℂ →L[ℝ] ℝ) :
    ‖L.comp (F.restrictScalars ℝ)‖ = ‖L‖ * ‖F‖ := by
  let G : ℂ →L[ℂ] ℂ := StrongDual.extendRCLike L
  have hG (z : ℂ) : G z = G 1 * z := by
    simpa only [smul_eq_mul, mul_one, mul_comm] using G.map_smul z 1
  have hGeq : G = G 1 • ContinuousLinearMap.id ℂ ℂ := by
    ext
    simp
  have hGn : ‖G 1‖ = ‖L‖ := by
    have hh : ‖G‖ = ‖G 1‖ := by rw [hGeq, norm_smul]; simp
    exact hh.symm.trans (StrongDual.norm_extendRCLike (𝕜 := ℂ) L)
  have he : L.comp (F.restrictScalars ℝ) =
      Complex.reCLM.comp ((G 1 • F).restrictScalars ℝ) := by
    ext x
    change L (F x) = (G 1 * F x).re
    rw [← hG]
    simp [G, StrongDual.extendRCLike_apply]
  rw [he, norm_realPart, norm_smul, hGn]

end Norms

/-- The probability law with independent real orthonormal coordinates of
variance 1/2; on a complex Euclidean space this is the standard complex
Gaussian normalization used in the manuscript. -/
def complexGaussian (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] : Measure F :=
  (stdGaussian F).map (fun x : F => Real.sqrt (1 / 2 : ℝ) • x)

section Measures
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Unit complex functionals send actual standard isotropic Gaussians to
the standard isotropic Gaussian on the complex plane. -/
theorem map_unit_stdGaussian (F : E →L[ℂ] ℂ) (hF : ‖F‖ = 1) :
    (stdGaussian E).map F = stdGaussian ℂ := by
  change (stdGaussian E).map (F.restrictScalars ℝ) = stdGaussian ℂ
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_map, charFunDual_stdGaussian, charFunDual_stdGaussian,
    norm_real_comp_complex, hF, mul_one]

instance complexGaussian_isProbability : IsProbabilityMeasure (complexGaussian E) := by
  unfold complexGaussian
  exact Measure.isProbabilityMeasure_map (by fun_prop)

instance complexGaussian_isGaussian : IsGaussian (complexGaussian E) := by
  change IsGaussian ((stdGaussian E).map
    (Real.sqrt (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ E))
  infer_instance

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
/-- The correct variance-1/2 real marginal, derived from the actual law. -/
theorem map_unit_real_complexGaussian (L : E →L[ℝ] ℝ) (hL : ‖L‖ = 1) :
    (complexGaussian E).map L = gaussianReal 0 (1 / 2) := by
  rw [complexGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  have he : L ∘ (fun x : E => Real.sqrt (1 / 2 : ℝ) • x) =
      (fun x : ℝ => Real.sqrt (1 / 2 : ℝ) * x) ∘ L := by
    ext x
    simp
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop), map_unit_real_stdGaussian L hL,
    gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    simp

/-- Unitary projection invariance, proved without an assumed change of
variables or an assumed Gaussian projection identity. -/
theorem map_unit_complexGaussian (F : E →L[ℂ] ℂ) (hF : ‖F‖ = 1) :
    (complexGaussian E).map F = complexGaussian ℂ := by
  rw [complexGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  have he : F ∘ (fun x : E => Real.sqrt (1 / 2 : ℝ) • x) =
      (fun z : ℂ => Real.sqrt (1 / 2 : ℝ) • z) ∘ F := by
    ext x
    exact F.map_smul_of_tower _ x
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop), map_unit_stdGaussian F hF]
  rfl

end Measures

/-- An elementary domination for the logarithmic singularity on the complex
plane. The real projection is nonzero almost everywhere under the Gaussian. -/
theorem abs_log_norm_le_real_log_add_norm {z : ℂ} (hz : z.re ≠ 0) :
    |Real.log ‖z‖| ≤ |Real.log (|z.re|)| + ‖z‖ := by
  have hrep : 0 < |z.re| := abs_pos.mpr hz
  have hnorm : 0 < ‖z‖ := hrep.trans_le (Complex.abs_re_le_norm z)
  by_cases hlarge : 1 ≤ ‖z‖
  · rw [abs_of_nonneg (Real.log_nonneg hlarge)]
    have hlog := Real.log_le_sub_one_of_pos hnorm
    linarith [abs_nonneg (Real.log (|z.re|))]
  · have hsmall : ‖z‖ ≤ 1 := (lt_of_not_ge hlarge).le
    rw [abs_of_nonpos (Real.log_nonpos hnorm.le hsmall)]
    have hlog := Real.log_le_log hrep (Complex.abs_re_le_norm z)
    linarith [neg_le_abs (Real.log (|z.re|)), norm_nonneg z]

/-- Actual absolute integrability on the one-dimensional complex Gaussian.
The proof uses the established real Gaussian logarithmic integral and the
Gaussian first moment. -/
theorem integrable_log_norm_complexGaussian :
    Integrable (fun z : ℂ => Real.log ‖z‖) (complexGaussian ℂ) := by
  have hrenorm : ‖Complex.reCLM‖ = 1 := by
    have h := norm_realPart (ContinuousLinearMap.id ℂ ℂ)
    change ‖Complex.reCLM‖ = ‖ContinuousLinearMap.id ℂ ℂ‖ at h
    simpa using h
  have hmap := map_unit_real_complexGaussian Complex.reCLM hrenorm
  have hreal : Integrable (fun z : ℂ => |Real.log (|z.re|)|) (complexGaussian ℂ) := by
    have hi := integrable_abs_log_gaussianReal 0 (by norm_num : (1 / 2 : ℝ≥0) ≠ 0)
    rw [← hmap] at hi
    exact hi.comp_measurable Complex.reCLM.measurable
  have hn : Integrable (fun z : ℂ => ‖z‖) (complexGaussian ℂ) :=
    IsGaussian.integrable_id.norm
  have hzero : ∀ᵐ z ∂complexGaussian ℂ, z.re ≠ 0 := by
    have hr : ∀ᵐ x ∂gaussianReal 0 (1 / 2), x ≠ (0 : ℝ) :=
      (gaussianReal_absolutelyContinuous 0 (v := 1 / 2) (by norm_num)).ae_le (volume.ae_ne 0)
    rw [← hmap] at hr
    exact (ae_map_iff Complex.reCLM.measurable.aemeasurable (by measurability)).mp hr
  apply (hreal.add hn).mono' measurable_norm.log.aestronglyMeasurable
  filter_upwards [hzero] with z hz
  simpa only [Real.norm_eq_abs, Pi.add_apply] using abs_log_norm_le_real_log_add_norm hz

#print axioms norm_real_comp_complex
#print axioms map_unit_stdGaussian
#print axioms map_unit_real_complexGaussian
#print axioms map_unit_complexGaussian
#print axioms integrable_log_norm_complexGaussian
end V10.ProjectionGaussian
