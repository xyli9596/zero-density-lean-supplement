import ZeroDensity.PlanarLogIntegrability
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-! Actual boundary charge and classical Laplacian of the planar logarithmic
kernel. These are not the distributional Poincare--Lelong theorem: its missing
step is integration by parts through a shrinking puncture. -/
namespace ZeroDensity.LogKernelBoundary
open MeasureTheory Filter InnerProductSpace Laplacian
open scoped Topology
noncomputable section

/-- The complex gradient kernel has the exact boundary charge at every radius. -/
theorem inverse_circle_charge (a : ℂ) {R : ℝ} (hR : R ≠ 0) :
    (∮ z in C(a, R), (z - a)⁻¹) = 2 * Real.pi * Complex.I :=
  circleIntegral.integral_sub_center_inv a hR

/-- The logarithmic kernel is genuinely harmonic at every nonsingular point. -/
theorem harmonicAt_log_norm_sub {a z : ℂ} (hz : z ≠ a) :
    HarmonicAt (fun w : ℂ => Real.log ‖w - a‖) z := by
  exact (show AnalyticAt ℂ (fun w : ℂ => w - a) z by fun_prop).harmonicAt_log_norm
    (sub_ne_zero.mpr hz)

/-- Its classical Laplacian vanishes almost everywhere, despite the nonzero
boundary charge. The Dirac mass must therefore use the weak Laplacian. -/
theorem laplacian_log_norm_sub_ae (a : ℂ) :
    (Δ (fun w : ℂ => Real.log ‖w - a‖)) =ᵐ[volume] 0 := by
  filter_upwards [volume.ae_ne a] with z hz
  exact (harmonicAt_log_norm_sub hz).2.self_of_nhds

#print axioms inverse_circle_charge
#print axioms harmonicAt_log_norm_sub
#print axioms laplacian_log_norm_sub_ae
end
end ZeroDensity.LogKernelBoundary
