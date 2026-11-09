import ZeroDensity.PositiveBetaInverse
import ZeroDensity.ZeroBetaInverse

/-! Uniform inverse estimates for every real beta >= 0. This assembles the
actual zero- and positive-beta proofs and discharges the radius input used
in the existing counting-transfer modules. No inverse expansion is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace ZeroDensity.PhaseInverse
open ZeroDensity.MainTheorem ZeroDensity.CountGeometry
open ZeroDensity.PositiveBetaInverse

theorem inverse_uniform_closed {Φ : ℂ → ℂ} {β : ℝ} {C : ℂ} (hβ : 0 ≤ β)
    (hΦ : IsPhasePrimitive Φ β C) (B : InverseBranch Φ)
    {a b : ℝ} (hleft : B.left < a) (hab : a ≤ b) (hright : b < B.right) :
    ∃ k : ℤ, TendstoUniformlyOn (fun (R θ : ℝ) =>
      B.ψ ((R:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)) -
        (((Real.log R-β*Real.log (Real.log R):ℝ):ℂ)+
          ((θ+2*Real.pi*k:ℝ):ℂ)*Complex.I)) (fun _ => 0) atTop (Icc a b) := by
  rcases eq_or_lt_of_le hβ with he | hp
  · subst β
    obtain ⟨k,hk⟩ := ZeroDensity.ZeroBetaInverse.inverse_uniform_closed hΦ B hleft hab hright
    refine ⟨k, ?_⟩
    convert hk using 1 <;> first | rfl | (funext R θ; push_cast; ring)
  · exact PositiveBetaInverse.inverse_uniform_closed hp hΦ B hleft hab hright

lemma angular_bound (a b : ℝ) (k : ℤ) {θ : ℝ} (hθ : θ ∈ Icc a b) :
    |θ+2*Real.pi*k| ≤ max |a| |b|+|2*Real.pi*k| := by
  have ht : |θ| ≤ max |a| |b| := by
    apply abs_le.mpr
    constructor
    · have := le_max_left |a| |b|
      have := neg_abs_le a
      linarith [hθ.1]
    · have := le_max_right |a| |b|
      have := le_abs_self b
      linarith [hθ.2]
  exact (abs_add_le _ _).trans (add_le_add_left ht _)

/-- Actual admissible-radius asymptotic used by Theorem 3.1. -/
theorem inverse_radius_uniform_closed {Φ : ℂ → ℂ} {β : ℝ} {C : ℂ} (hβ : 0 ≤ β)
    (hΦ : IsPhasePrimitive Φ β C) (B : InverseBranch Φ)
    {a b : ℝ} (hleft : B.left < a) (hab : a ≤ b) (hright : b < B.right)
    (ω : ℂ) (hω : ω ≠ 0) :
    TendstoUniformlyOn (fun (R θ : ℝ) =>
      ‖ω⁻¹*B.ψ ((R:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖-
        ZeroDensity.RadiusComparison.L ‖ω‖ β R) (fun _ => 0) atTop (Icc a b) := by
  obtain ⟨k,hk⟩ := inverse_uniform_closed hβ hΦ B hleft hab hright
  exact ZeroDensity.InverseGeometry.admissible_radius (Icc a b) β
    (fun θ => θ+2*Real.pi*k) (fun θ hθ => angular_bound a b k hθ)
    (fun R θ => B.ψ ((R:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))) ω hω
    (by simpa only [Complex.ofReal_sub,Complex.ofReal_mul] using hk)

/-- A fixed inverse branch eventually lies in a horizontal strip, uniformly
on every closed subinterval of its angular sector. -/
theorem inverse_imaginary_bounded {Φ : ℂ → ℂ} {β : ℝ} {C : ℂ} (hβ : 0 ≤ β)
    (hΦ : IsPhasePrimitive Φ β C) (B : InverseBranch Φ)
    {a b : ℝ} (hleft : B.left < a) (hab : a ≤ b) (hright : b < B.right) :
    ∃ M : ℝ, ∀ᶠ R : ℝ in atTop, ∀ θ ∈ Icc a b,
      |(B.ψ ((R:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))).im| ≤ M := by
  obtain ⟨k,hk⟩ := inverse_uniform_closed hβ hΦ B hleft hab hright
  refine ⟨max |a| |b|+|2*Real.pi*k|+1, ?_⟩
  have he := (Metric.tendstoUniformlyOn_iff.mp hk) 1 (by norm_num)
  filter_upwards [he] with R hR
  intro θ hθ
  have hh := hR θ hθ
  rw [dist_zero_left] at hh
  have him := Complex.abs_im_le_norm
    (B.ψ ((R:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))-
      (((Real.log R-β*Real.log (Real.log R):ℝ):ℂ)+((θ+2*Real.pi*k:ℝ):ℂ)*Complex.I))
  simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add] at him
  have ht := angular_bound a b k hθ
  have htri := abs_add_le
    ((B.ψ ((R:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))).im-(θ+2*Real.pi*k)) (θ+2*Real.pi*k)
  simp only [sub_add_cancel] at htri
  linarith

/-- Real-part escape is now proved from the actual inverse, discharging the
horizontal-strip regime needed by coefficient-limit lemmas. -/
theorem inverse_real_escape {Φ : ℂ → ℂ} {β : ℝ} {C : ℂ} (hβ : 0 ≤ β)
    (hΦ : IsPhasePrimitive Φ β C) (B : InverseBranch Φ)
    {a b : ℝ} (hleft : B.left < a) (hab : a ≤ b) (hright : b < B.right) :
    Tendsto (fun x : ℝ × ℝ =>
      (B.ψ ((x.1:ℂ)*Complex.exp ((x.2:ℂ)*Complex.I))).re)
      (atTop ×ˢ 𝓟 (Icc a b)) atTop := by
  obtain ⟨k,hk⟩ := inverse_uniform_closed hβ hΦ B hleft hab hright
  have he := (Metric.tendstoUniformlyOn_iff.mp hk) 1 (by norm_num)
  have hx := ZeroDensity.InverseGeometry.log_radius_tendsto β
  apply tendsto_atTop.2
  intro M
  rw [eventually_prod_principal_iff]
  filter_upwards [he,hx.eventually_ge_atTop (M+1)] with R hR hx
  intro θ hθ
  have hh := hR θ hθ
  rw [dist_zero_left] at hh
  have hre := Complex.abs_re_le_norm
    (B.ψ ((R:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))-
      (((Real.log R-β*Real.log (Real.log R):ℝ):ℂ)+((θ+2*Real.pi*k:ℝ):ℂ)*Complex.I))
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] at hre
  have hbound := abs_le.mp (hre.trans hh.le)
  linarith

#print axioms inverse_uniform_closed
#print axioms inverse_radius_uniform_closed
#print axioms inverse_real_escape
end ZeroDensity.PhaseInverse
