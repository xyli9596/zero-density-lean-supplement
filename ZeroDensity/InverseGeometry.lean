import ZeroDensity.RadiusComparison
import ZeroDensity.CountGeometry
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! Exact norm geometry of the inverse asymptotic in Theorem 3.1.
The inverse formula is a conditional input here; its construction from the
phase map is not asserted. Radius convergence is proved from that formula. -/
noncomputable section
set_option autoImplicit false
open Filter Set
open scoped Topology
namespace ZeroDensity.InverseGeometry

/-- Bounded imaginary parts change a large positive real radius by O(1/x). -/
theorem norm_sub_real_bound {x y B : ℝ} (hx : 0 < x) (hy : |y| ≤ B) :
    0 ≤ ‖(x:ℂ) + (y:ℂ)*Complex.I‖-x ∧
    ‖(x:ℂ) + (y:ℂ)*Complex.I‖-x ≤ B^2/x := by
  let z : ℂ := (x:ℂ)+(y:ℂ)*Complex.I
  have hre : z.re = x := by simp [z]
  have him : z.im = y := by simp [z]
  have hn : x ≤ ‖z‖ := by simpa [hre] using Complex.re_le_norm z
  have hs : ‖z‖^2-x^2 = y^2 := by simpa [hre,him] using Complex.sq_norm_sub_sq_re z
  have hy2 : y^2 ≤ B^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg y) hy 2
  refine ⟨sub_nonneg.mpr hn, ?_⟩
  apply (le_div_iff₀ hx).mpr
  change (‖z‖-x)*x ≤ B^2
  nlinarith [norm_nonneg z]

/-- Uniformity over an arbitrary index set needs only a bound on imaginary
parts; neither compactness nor continuity of the angular parametrization. -/
theorem bounded_imaginary_radius {ι : Type*} (D : Set ι)
    {x : ℝ → ℝ} (hx : Tendsto x atTop atTop) (y : ι → ℝ)
    {B : ℝ} (hy : ∀ θ ∈ D, |y θ| ≤ B) :
    TendstoUniformlyOn (fun r θ => ‖(x r:ℂ)+(y θ:ℂ)*Complex.I‖-x r)
      (fun _ => 0) atTop D := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have ht : Tendsto (fun r => B^2/x r) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hx
  filter_upwards [hx.eventually_gt_atTop 0, ht.eventually (gt_mem_nhds hε)] with r hr he
  intro θ hθ
  obtain ⟨hlo,hhi⟩ := norm_sub_real_bound hr (hy θ hθ)
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hlo]
  exact hhi.trans_lt he

/-- Small complex errors in the inverse formula give uniformly small radius
errors after dividing by any nonzero complex phase coefficient. -/
theorem inverse_radius_uniform {ι : Type*} (D : Set ι)
    {x : ℝ → ℝ} (hx : Tendsto x atTop atTop) (y : ι → ℝ)
    {B : ℝ} (hy : ∀ θ ∈ D, |y θ| ≤ B)
    (ψ : ℝ → ι → ℂ) (ω : ℂ) (hω : ω ≠ 0)
    (herr : TendstoUniformlyOn
      (fun r θ => ψ r θ-((x r:ℂ)+(y θ:ℂ)*Complex.I)) (fun _ => 0) atTop D) :
    TendstoUniformlyOn (fun r θ => ‖ω⁻¹*ψ r θ‖-x r/‖ω‖)
      (fun _ => 0) atTop D := by
  have hωn : 0 < ‖ω‖ := norm_pos_iff.mpr hω
  have hg := bounded_imaginary_radius D hx y hy
  rw [Metric.tendstoUniformlyOn_iff] at herr hg ⊢
  intro ε hε
  have he : 0 < ε*‖ω‖/2 := by positivity
  filter_upwards [herr _ he, hg _ he] with r hr hg'
  intro θ hθ
  have h1 := hr θ hθ
  have h2 := hg' θ hθ
  rw [dist_zero_left] at h1
  rw [Real.dist_eq, zero_sub, abs_neg] at h2
  have hnorm := abs_norm_sub_norm_le (ψ r θ) ((x r:ℂ)+(y θ:ℂ)*Complex.I)
  have hsum : |‖ψ r θ‖-x r| < ε*‖ω‖ := by
    have hh := abs_add_le (‖ψ r θ‖-‖(x r:ℂ)+(y θ:ℂ)*Complex.I‖)
      (‖(x r:ℂ)+(y θ:ℂ)*Complex.I‖-x r)
    have htri : |‖ψ r θ‖-x r| ≤ |‖ψ r θ‖-‖(x r:ℂ)+(y θ:ℂ)*Complex.I‖|+
      |‖(x r:ℂ)+(y θ:ℂ)*Complex.I‖-x r| := by simpa using hh
    linarith
  rw [Real.dist_eq, zero_sub, abs_neg, norm_mul, norm_inv]
  have hid : ‖ω‖⁻¹*‖ψ r θ‖-x r/‖ω‖ = (‖ψ r θ‖-x r)/‖ω‖ := by ring
  rw [hid, abs_div, abs_of_pos hωn]
  exact (div_lt_iff₀ hωn).mpr hsum

/-- The real part occurring in the inverse asymptotic tends to infinity. -/
theorem log_radius_tendsto (β : ℝ) :
    Tendsto (fun R : ℝ => Real.log R-β*Real.log (Real.log R)) atTop atTop := by
  have hl := Real.tendsto_log_atTop
  have hsmall : Tendsto (fun R : ℝ => β*(Real.log (Real.log R)/Real.log R)) atTop (𝓝 0) :=
    by simpa using ((Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hl).const_mul β)
  refine tendsto_atTop_mono' _ ?_ (hl.const_mul_atTop (by norm_num : (0:ℝ)<1/2))
  filter_upwards [hl.eventually_gt_atTop 0, hsmall.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))] with R hR hh
  have hh' : β*Real.log (Real.log R) < (1/2)*Real.log R := by
    apply (div_lt_iff₀ hR).mp
    simpa [mul_div_assoc] using hh
  linarith

/-- Admissible radius formula, using the same L as RadiusComparison. -/
theorem admissible_radius {ι : Type*} (D : Set ι) (β : ℝ)
    (y : ι → ℝ) {B : ℝ} (hy : ∀ θ ∈ D, |y θ| ≤ B)
    (ψ : ℝ → ι → ℂ) (ω : ℂ) (hω : ω ≠ 0)
    (herr : TendstoUniformlyOn (fun R θ => ψ R θ-
      (((Real.log R-β*Real.log (Real.log R)):ℂ)+(y θ:ℂ)*Complex.I))
      (fun _ => 0) atTop D) :
    TendstoUniformlyOn (fun R θ => ‖ω⁻¹*ψ R θ‖-
      ZeroDensity.RadiusComparison.L ‖ω‖ β R) (fun _ => 0) atTop D := by
  apply inverse_radius_uniform D (log_radius_tendsto β) y hy ψ ω hω
  simpa only [Complex.ofReal_sub, Complex.ofReal_mul] using herr

/-- A differentiable local inverse has nonzero derivative, derived from the
actual local composition identity, rather than postulated separately. -/
theorem inverse_derivative_nonzero {F ψ : ℂ → ℂ} {z A B : ℂ}
    (hF : HasDerivAt F A (ψ z)) (hψ : HasDerivAt ψ B z)
    (hcomp : (fun w => F (ψ w)) =ᶠ[𝓝 z] (fun w => w)) :
    A ≠ 0 ∧ B ≠ 0 := by
  have hc : HasDerivAt (fun w => F (ψ w)) (A*B) z := hF.comp z hψ
  have hi : HasDerivAt (fun w => F (ψ w)) 1 z :=
    (hasDerivAt_id z).congr_of_eventuallyEq hcomp
  have he : A*B = 1 := hc.unique hi
  constructor
  · intro h; simp [h] at he
  · intro h; simp [h] at he

/-- Analyticity on a wider sector includes both angular boundary sides of
a narrower sector, with the same strict inner radial cutoff. -/
theorem analytic_on_closed_inner_sector {F : ℂ → ℂ}
    {S₀ S₁ a b c d : ℝ} (hS : S₀ ≤ S₁) (hca : c < a) (hbd : b < d)
    (hF : AnalyticOnNhd ℂ F (ZeroDensity.CountGeometry.angularSector S₀ c d)) :
    AnalyticOnNhd ℂ F (ZeroDensity.CountGeometry.closedAngularSector S₁ a b) := by
  apply hF.mono
  rintro s ⟨R,hR,θ,hθ,hs⟩
  exact ⟨R,lt_of_le_of_lt hS hR,θ,
    ⟨lt_of_lt_of_le hca hθ.1,lt_of_le_of_lt hθ.2 hbd⟩,hs⟩

#print axioms inverse_derivative_nonzero
#print axioms analytic_on_closed_inner_sector
#print axioms inverse_radius_uniform
#print axioms admissible_radius
end ZeroDensity.InverseGeometry
