import V10.HarmonicWeakLaplacian
import V10.LogLaplacianLocal
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Genuine weak second derivatives of a hinge and its planar lift. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
namespace V10.HingeLaplacian
set_option backward.isDefEq.respectTransparency false

theorem integral_Ioi_mul_deriv_deriv {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    (∫ y in Ioi (0 : ℝ), y * deriv (deriv g) y) = g 0 := by
  have hd : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
  let q : ℝ → ℝ := fun y => y * deriv g y - g y
  have hq : ContDiff ℝ 1 q := (contDiff_id.mul hd |>.sub hg).of_le (by simp)
  have hqc : HasCompactSupport q := hgc.deriv.mul_left.sub hgc
  have he : deriv q = fun y => y * deriv (deriv g) y := by
    funext y
    have h := ((hasDerivAt_id y).mul
      (hd.differentiable (by simp) y).hasDerivAt).sub
        (hg.differentiable (by simp) y).hasDerivAt
    simpa only [q, id_eq, Pi.mul_def, Pi.sub_def, one_mul, add_sub_cancel_left] using h.deriv
  have h := hqc.integral_Ioi_deriv_eq hq 0
  rw [he] at h
  simpa [q] using h

/-- The positive-part function has a unit Dirac second derivative. This is
proved by the fundamental theorem of calculus, not taken as a weak identity. -/
theorem hinge_second_derivative {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    (∫ y, max 0 y * deriv (deriv g) y) = g 0 := by
  have he : (fun y => max 0 y * deriv (deriv g) y) =
      (Ioi (0 : ℝ)).indicator (fun y => y * deriv (deriv g) y) := by
    funext y
    by_cases hy : 0 < y
    · simp [hy, max_eq_right hy.le]
    · simp [hy, max_eq_left (not_lt.mp hy)]
  rw [he, integral_indicator measurableSet_Ioi]
  exact integral_Ioi_mul_deriv_deriv hg hgc

theorem integral_deriv_compact {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) : (∫ y, deriv g y) = 0 := by
  exact integral_eq_zero_of_hasDerivAt_of_integrable
    (fun y => (hg.differentiable (by simp) y).hasDerivAt)
    ((hg.continuous_deriv (by simp)).integrable_of_hasCompactSupport hgc.deriv)
    (hg.continuous.integrable_of_hasCompactSupport hgc)

def secondDirectional (φ : ℂ → ℝ) (v z : ℂ) : ℝ :=
  fderiv ℝ (fun w => fderiv ℝ φ w v) z v

theorem deriv_on_line {φ : ℂ → ℝ} (hφ : Differentiable ℝ φ) (a v : ℂ) (t : ℝ) :
    deriv (fun u : ℝ => φ (a + u • v)) t = fderiv ℝ φ (a + t • v) v := by
  have h := (hφ (a + t • v)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t a).add ((hasDerivAt_id t).smul_const v))
  simpa only [zero_add, one_smul, Function.comp_def, Pi.add_apply, id_eq] using h.deriv

theorem second_deriv_on_line {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (a v : ℂ) (t : ℝ) :
    deriv (deriv (fun u : ℝ => φ (a + u • v))) t =
      secondDirectional φ v (a + t • v) := by
  have he : deriv (fun u : ℝ => φ (a + u • v)) =
      fun u => fderiv ℝ φ (a + u • v) v := by
    funext u
    exact deriv_on_line (hφ.differentiable (by simp)) a v u
  rw [he]
  unfold secondDirectional
  apply deriv_on_line (φ := fun z => fderiv ℝ φ z v)
  have hd : ContDiff ℝ ∞ (fun z => fderiv ℝ φ z v) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  exact hd.differentiable (by simp)

theorem compactSupport_on_line {φ : ℂ → ℝ} (hφc : HasCompactSupport φ)
    (a v : ℂ) (hv : ‖v‖ = 1) : HasCompactSupport (fun t : ℝ => φ (a + t • v)) := by
  apply hφc.comp_isClosedEmbedding
  apply Isometry.isClosedEmbedding
  apply isometry_iff_dist_eq.mpr
  intro t u
  simp only [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hv, mul_one]

theorem secondDirectional_continuous {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (v : ℂ) :
    Continuous (secondDirectional φ v) := by
  have hd : ContDiff ℝ ∞ (fun z => fderiv ℝ φ z v) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have hdd : ContDiff ℝ ∞ (secondDirectional φ v) :=
    (hd.fderiv_right (by simp)).clm_apply contDiff_const
  exact hdd.continuous

theorem secondDirectional_compact {φ : ℂ → ℝ} (hφc : HasCompactSupport φ) (v : ℂ) :
    HasCompactSupport (secondDirectional φ v) :=
  (hφc.fderiv_apply ℝ v).fderiv_apply ℝ v

theorem complex_integral_eq_iterated {f : ℂ → ℝ} (hf : Integrable f) :
    (∫ z, f z) = ∫ x : ℝ, ∫ y : ℝ, f ((x : ℂ) + y • Complex.I) := by
  have hm := Complex.volume_preserving_equiv_real_prod.symm
  have he := hm.integral_comp Complex.measurableEquivRealProd.symm.measurableEmbedding f
  have hi : Integrable (fun p : ℝ × ℝ => f (Complex.measurableEquivRealProd.symm p))
      ((volume : Measure ℝ).prod volume) := hm.integrable_comp_of_integrable hf
  rw [← he, MeasureTheory.Measure.volume_eq_prod,
    integral_prod (fun p : ℝ × ℝ => f (Complex.measurableEquivRealProd.symm p)) hi]
  congr 1
  funext x
  congr 1
  funext y
  congr 1
  apply Complex.ext <;> simp [Complex.real_smul]

theorem complex_integral_eq_iterated_swap {f : ℂ → ℝ} (hf : Integrable f) :
    (∫ z, f z) = ∫ y : ℝ, ∫ x : ℝ, f ((x : ℂ) + y • Complex.I) := by
  rw [complex_integral_eq_iterated hf]
  apply integral_integral_swap
  have hi : Integrable (fun p : ℝ × ℝ => f (Complex.measurableEquivRealProd.symm p))
      ((volume : Measure ℝ).prod volume) :=
    Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_of_integrable hf
  exact hi.congr (ae_of_all _ fun p => by
    change f (Complex.measurableEquivRealProd.symm p) = f ((p.1 : ℂ) + p.2 • Complex.I)
    congr 1
    apply Complex.ext <;> simp [Complex.real_smul])

theorem weighted_second_integrable {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (v : ℂ) :
    Integrable (fun z => max 0 z.im * secondDirectional φ v z) := by
  have hc : Continuous (fun z : ℂ => max (0 : ℝ) z.im * secondDirectional φ v z) :=
    (continuous_const.max Complex.continuous_im).mul (secondDirectional_continuous hφ v)
  exact hc.integrable_of_hasCompactSupport (secondDirectional_compact hφc v).mul_left

theorem hinge_horizontal_term {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) :
    (∫ z, max 0 z.im * secondDirectional φ 1 z) = 0 := by
  rw [complex_integral_eq_iterated_swap (weighted_second_integrable hφ hφc 1)]
  apply integral_eq_zero_of_ae
  apply ae_of_all
  intro y
  simp only [Complex.add_im, Complex.ofReal_im, Complex.smul_im, Complex.I_im,
    smul_eq_mul, mul_one, zero_add, integral_const_mul]
  have hg : ContDiff ℝ ∞ (fun x : ℝ => φ (y • Complex.I + x • (1 : ℂ))) :=
    hφ.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hgc := compactSupport_on_line hφc (y • Complex.I) (1 : ℂ) (by simp)
  have hz := integral_deriv_compact (contDiff_infty_iff_deriv.mp hg).2 hgc.deriv
  have he : (fun x : ℝ => secondDirectional φ 1 ((x : ℂ) + y • Complex.I)) =
      deriv (deriv (fun x : ℝ => φ (y • Complex.I + x • (1 : ℂ)))) := by
    funext x
    rw [second_deriv_on_line hφ]
    simp [Complex.real_smul, add_comm]
  rw [he, hz, mul_zero]
  rfl

theorem hinge_vertical_term {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) :
    (∫ z, max 0 z.im * secondDirectional φ Complex.I z) = ∫ x : ℝ, φ x := by
  rw [complex_integral_eq_iterated (weighted_second_integrable hφ hφc Complex.I)]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  simp only [Complex.add_im, Complex.ofReal_im, Complex.smul_im, Complex.I_im,
    smul_eq_mul, mul_one, zero_add]
  have hg : ContDiff ℝ ∞ (fun y : ℝ => φ ((x : ℂ) + y • Complex.I)) :=
    hφ.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hgc := compactSupport_on_line hφc (x : ℂ) Complex.I (by simp)
  have h := hinge_second_derivative hg hgc
  simp only [second_deriv_on_line hφ, zero_smul, add_zero] at h
  exact h

/-- The actual planar Laplacian of the positive imaginary part is Euclidean
length measure on the real axis. Both directional terms are computed by
Fubini and genuine one-dimensional derivatives. -/
theorem hinge_laplacian_test {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) :
    (∫ z, Laplacian.laplacian φ z * max 0 z.im) = ∫ x : ℝ, φ x := by
  have he : (fun z => Laplacian.laplacian φ z * max 0 z.im) =
      (fun z => max 0 z.im * secondDirectional φ 1 z +
        max 0 z.im * secondDirectional φ Complex.I z) := by
    funext z
    rw [HarmonicWeakLaplacian.laplacian_eq_directional hφ.contDiffAt]
    dsimp only [secondDirectional]
    ring
  rw [he, integral_add (weighted_second_integrable hφ hφc 1)
    (weighted_second_integrable hφ hφc Complex.I), hinge_horizontal_term hφ hφc,
    hinge_vertical_term hφ hφc, zero_add]

#print axioms hinge_second_derivative
#print axioms hinge_laplacian_test
end V10.HingeLaplacian
