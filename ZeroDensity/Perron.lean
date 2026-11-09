import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-! Elementary, unconditional logarithmic-growth facts. The general Perron
classification for an asymptotically constant matrix ODE is not established here. -/
namespace ZeroDensity.Perron
open Filter

/-- The real radial logarithmic growth exponent. -/
def HasRadialRate {E : Type*} [NormedAddCommGroup E] (x : ℝ → E) (a : ℝ) : Prop :=
  Tendsto (fun r => Real.log ‖x r‖ / r) atTop (nhds a)

/-- Multiplying by a fixed nonzero scalar preserves a logarithmic growth exponent. -/
theorem hasRadialRate_const_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {x : ℝ → E} {a : ℝ} (hx : HasRadialRate x a)
    (hne : ∀ᶠ r in atTop, x r ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    HasRadialRate (fun r => c • x r) a := by
  have hconst : Tendsto (fun r : ℝ => Real.log ‖c‖ / r) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hsum := hconst.add hx
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [hne] with r hr
  rw [norm_smul, Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hr),
    add_div]

/-- A pure complex exponential has radial rate equal to the real part of its exponent. -/
theorem hasRadialRate_exp (z : ℂ) :
    HasRadialRate (fun r : ℝ => Complex.exp ((r : ℂ) * z)) z.re := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  simp only [Complex.norm_exp, Real.log_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  field_simp

/-- Every fixed nonzero exponential mode has the expected real growth exponent. -/
theorem hasRadialRate_exp_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (z : ℂ) {v : E} (hv : v ≠ 0) :
    HasRadialRate (fun r : ℝ => Complex.exp ((r : ℂ) * z) • v) z.re := by
  have hconst : Tendsto (fun r : ℝ => Real.log ‖v‖ / r) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hsum := (hasRadialRate_exp z).add hconst
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [] with r
  rw [norm_smul, Real.log_mul (norm_ne_zero_iff.mpr (Complex.exp_ne_zero _))
    (norm_ne_zero_iff.mpr hv), add_div]

/-- Polynomial prefactors have zero radial logarithmic growth. -/
theorem hasRadialRate_pow (k : ℕ) :
    HasRadialRate (fun r : ℝ => r ^ k) 0 := by
  have hlog : Tendsto (fun r : ℝ => Real.log r / r) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h := hlog.const_mul (k : ℝ)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [Real.norm_eq_abs, abs_of_pos (pow_pos hr k), Real.log_pow]
  ring

/-- Logarithmic growth is additive under products of eventually nonzero scalars. -/
theorem hasRadialRate_mul {x y : ℝ → ℂ} {a b : ℝ}
    (hx : HasRadialRate x a) (hy : HasRadialRate y b)
    (hxn : ∀ᶠ r in atTop, x r ≠ 0) (hyn : ∀ᶠ r in atTop, y r ≠ 0) :
    HasRadialRate (fun r => x r * y r) (a + b) := by
  apply (hx.add hy).congr'
  filter_upwards [hxn, hyn] with r hr hs
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hr) (norm_ne_zero_iff.mpr hs),
    add_div]

/-- The polynomial factors occurring in Jordan modes do not alter the real exponent. -/
theorem hasRadialRate_pow_exp (k : ℕ) (z : ℂ) :
    HasRadialRate (fun r : ℝ => ((r : ℂ) ^ k) * Complex.exp ((r : ℂ) * z)) z.re := by
  have hp : HasRadialRate (fun r : ℝ => (r : ℂ) ^ k) 0 := by
    simpa only [HasRadialRate, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      using hasRadialRate_pow k
  have hn : ∀ᶠ r : ℝ in atTop, (r : ℂ) ^ k ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hr))
  simpa using hasRadialRate_mul hp (hasRadialRate_exp z) hn
    (Filter.Eventually.of_forall fun r => Complex.exp_ne_zero _)

#print axioms hasRadialRate_const_smul
#print axioms hasRadialRate_exp
#print axioms hasRadialRate_exp_smul
#print axioms hasRadialRate_pow
#print axioms hasRadialRate_mul
#print axioms hasRadialRate_pow_exp

end ZeroDensity.Perron
