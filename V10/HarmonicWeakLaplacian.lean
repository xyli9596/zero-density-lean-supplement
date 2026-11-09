import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-!
# The weak Laplacian of a genuinely local harmonic function

The harmonic function need only be harmonic near the support of the test.
No global smoothness, cutoff extension, or distributional identity is assumed.
Two integrations by parts are justified using compact support of the test
and of its derivatives.
-/

noncomputable section
open MeasureTheory Set InnerProductSpace
open scoped Topology ContDiff Laplacian

namespace V10.HarmonicWeakLaplacian

theorem continuous_mul_of_local {f g : ℂ → ℝ} (hg : Continuous g)
    (hf : ∀ z ∈ tsupport g, ContinuousAt f z) :
    Continuous (fun z => f z * g z) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z ∈ tsupport g
  · exact (hf z hz).mul hg.continuousAt
  · have he : g =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp hz
    apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with w hw
    simp [hw]

theorem integrable_mul_of_local {f g : ℂ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hf : ∀ z ∈ tsupport g, ContinuousAt f z) :
    Integrable (fun z => f z * g z) :=
  (continuous_mul_of_local hg hf).integrable_of_hasCompactSupport hgc.mul_left

theorem directional_twice {h φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ)
    (hh : ∀ z ∈ tsupport φ, ContDiffAt ℝ ∞ h z) (v : ℂ) :
    (∫ z, h z * fderiv ℝ (fun w => fderiv ℝ φ w v) z v) =
      ∫ z, fderiv ℝ (fun w => fderiv ℝ h w v) z v * φ z := by
  let Dφ := fun z => fderiv ℝ φ z v
  let Dh := fun z => fderiv ℝ h z v
  have hcDφ : ContDiff ℝ ∞ Dφ := by
    dsimp [Dφ]
    exact hφ.fderiv_right (by simp) |>.clm_apply contDiff_const
  have hcDDφ : Continuous (fun z => fderiv ℝ Dφ z v) := by
    have hd : ContDiff ℝ ∞ (fun z => fderiv ℝ Dφ z v) :=
      (hcDφ.fderiv_right (by simp)).clm_apply contDiff_const
    exact hd.continuous
  have hcDh (z) (hz : z ∈ tsupport φ) : ContDiffAt ℝ ∞ Dh z := by
    dsimp [Dh]
    exact ((hh z hz).fderiv_right (by simp)).clm_apply contDiffAt_const
  have hcDDh (z) (hz : z ∈ tsupport φ) :
      ContinuousAt (fun w => fderiv ℝ Dh w v) z := by
    have hd : ContDiffAt ℝ ∞ (fun w => fderiv ℝ Dh w v) z :=
      ((hcDh z hz).fderiv_right (by simp)).clm_apply contDiffAt_const
    exact hd.continuousAt
  have hsDφ : tsupport Dφ ⊆ tsupport φ := tsupport_fderiv_apply_subset ℝ v
  have hsDDφ : tsupport (fun z => fderiv ℝ Dφ z v) ⊆ tsupport φ :=
    (tsupport_fderiv_apply_subset ℝ v).trans hsDφ
  have hDφc : HasCompactSupport Dφ := hφc.fderiv_apply ℝ v
  have hi1 : Integrable (fun z => Dh z * Dφ z) :=
    integrable_mul_of_local hcDφ.continuous hDφc
      (fun z hz => (hcDh z (hsDφ hz)).continuousAt)
  have hi2 : Integrable (fun z => h z * fderiv ℝ Dφ z v) :=
    integrable_mul_of_local hcDDφ (hDφc.fderiv_apply ℝ v)
      (fun z hz => (hh z (hsDDφ hz)).continuousAt)
  have hi3 : Integrable (fun z => h z * Dφ z) :=
    integrable_mul_of_local hcDφ.continuous hDφc
      (fun z hz => (hh z (hsDφ hz)).continuousAt)
  have hi4 : Integrable (fun z => fderiv ℝ Dh z v * φ z) :=
    integrable_mul_of_local hφ.continuous hφc hcDDh
  have hi5 : Integrable (fun z => Dh z * φ z) :=
    integrable_mul_of_local hφ.continuous hφc
      (fun z hz => (hcDh z hz).continuousAt)
  have hfirst := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := h) (g := Dφ) (v := v) hi1 hi2 hi3
    (fun z hz => (hh z (hsDφ hz)).differentiableAt (by simp))
    (fun z _ => hcDφ.differentiable (by simp) z)
  have hsecond := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := Dh) (g := φ) (v := v) hi4 hi1 hi5
    (fun z hz => (hcDh z hz).differentiableAt (by simp))
    (fun z _ => hφ.differentiable (by simp) z)
  rw [hfirst, hsecond, neg_neg]

theorem laplacian_eq_directional {h : ℂ → ℝ} {z : ℂ}
    (hh : ContDiffAt ℝ ∞ h z) :
    Δ h z = fderiv ℝ (fun w => fderiv ℝ h w 1) z 1 +
      fderiv ℝ (fun w => fderiv ℝ h w Complex.I) z Complex.I := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ h) z := hh.fderiv_right (by simp)
  simp only [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [fderiv_clm_apply (hd.differentiableAt (by simp)) (by fun_prop),
    fderiv_clm_apply (hd.differentiableAt (by simp)) (by fun_prop)]
  simp

/-- A harmonic function has zero weak Laplacian against a smooth compactly
supported test whose support lies in its domain. -/
theorem harmonic_laplacian_test {h φ : ℂ → ℝ} {U : Set ℂ}
    (hh : HarmonicOnNhd h U) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    (∫ z, Δ φ z * h z) = 0 := by
  have hh_smooth : ∀ z ∈ tsupport φ, ContDiffAt ℝ ∞ h z :=
    fun z hz => (_root_.HarmonicAt.analyticAt (hh z (hs hz))).contDiffAt
  let DD := fun (v z : ℂ) => fderiv ℝ (fun w => fderiv ℝ φ w v) z v
  have hDc (v : ℂ) : ContDiff ℝ ∞ (fun z => fderiv ℝ φ z v) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have hDDc (v : ℂ) : Continuous (DD v) := by
    have hd : ContDiff ℝ ∞ (DD v) :=
      ((hDc v).fderiv_right (by simp)).clm_apply contDiff_const
    exact hd.continuous
  have hDDs (v : ℂ) : tsupport (DD v) ⊆ tsupport φ :=
    (tsupport_fderiv_apply_subset ℝ v).trans (tsupport_fderiv_apply_subset ℝ v)
  have hDDi (v : ℂ) : Integrable (fun z => h z * DD v z) :=
    integrable_mul_of_local (hDDc v)
      ((hφc.fderiv_apply ℝ v).fderiv_apply ℝ v)
      (fun z hz => (hh_smooth z (hDDs v hz)).continuousAt)
  have hHi (v : ℂ) : Integrable
      (fun z => fderiv ℝ (fun w => fderiv ℝ h w v) z v * φ z) := by
    apply integrable_mul_of_local hφ.continuous hφc
    intro z hz
    have hd : ContDiffAt ℝ ∞ (fun w => fderiv ℝ h w v) z :=
      ((hh_smooth z hz).fderiv_right (by simp)).clm_apply contDiffAt_const
    have hdd : ContDiffAt ℝ ∞ (fun w => fderiv ℝ (fun u => fderiv ℝ h u v) w v) z :=
      (hd.fderiv_right (by simp)).clm_apply contDiffAt_const
    exact hdd.continuousAt
  calc
    (∫ z, Δ φ z * h z) = ∫ z, h z * DD 1 z + h z * DD Complex.I z := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        dsimp only
        rw [laplacian_eq_directional hφ.contDiffAt]
        dsimp [DD]
        ring
    _ = (∫ z, h z * DD 1 z) + ∫ z, h z * DD Complex.I z :=
      integral_add (hDDi 1) (hDDi Complex.I)
    _ = (∫ z, fderiv ℝ (fun w => fderiv ℝ h w 1) z 1 * φ z) +
        ∫ z, fderiv ℝ (fun w => fderiv ℝ h w Complex.I) z Complex.I * φ z := by
      rw [directional_twice hφ hφc hh_smooth, directional_twice hφ hφc hh_smooth]
    _ = ∫ z, fderiv ℝ (fun w => fderiv ℝ h w 1) z 1 * φ z +
        fderiv ℝ (fun w => fderiv ℝ h w Complex.I) z Complex.I * φ z :=
      (integral_add (hHi 1) (hHi Complex.I)).symm
    _ = 0 := by
      apply integral_eq_zero_of_ae
      apply ae_of_all
      intro z
      dsimp only
      by_cases hz : z ∈ tsupport φ
      · rw [← add_mul, ← laplacian_eq_directional (hh_smooth z hz), (hh z (hs hz)).2.eq_of_nhds]
        simp
      · simp [image_eq_zero_of_notMem_tsupport hz]

#print axioms harmonic_laplacian_test

end V10.HarmonicWeakLaplacian
