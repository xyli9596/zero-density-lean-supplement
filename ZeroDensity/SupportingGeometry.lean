import ZeroDensity.LocalRootSelection
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv

/-! Exact trigonometric geometry for the polygon coefficient in Theorem 3.1.
The equality of an actual polygon face with the two adjacent selected roots,
and its identification with the zero-measure mass, remain separate steps.
-/
noncomputable section
set_option autoImplicit false
open scoped Topology
namespace ZeroDensity.SupportingGeometry
open LocalRootSelection

def tangent (μ : ℂ) (θ : ℝ) : ℝ :=
      (Complex.I * (μ * Complex.exp ((θ : ℂ) * Complex.I))).re

theorem projection_hasDeriv (μ : ℂ) (θ : ℝ) :
    HasDerivAt (projection μ) (tangent μ θ) θ := by
  have hd := ((((hasDerivAt_id (θ : ℂ)).mul_const Complex.I).cexp).const_mul μ)
  convert hd.real_of_complex using 1
  · funext x
    exact projection_eq μ x
  · dsimp [tangent]
    congr 1
    ring

theorem normal_projection (μ : ℂ) (θ : ℝ) :
    (star μ * Complex.exp (-((θ : ℂ) * Complex.I))).re = projection μ θ := by
  rw [projection_eq]
  simp [Complex.mul_re, Complex.exp_re, Complex.exp_im]

theorem norm_unit_exponential (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem norm_of_real_part_zero (z : ℂ) (hz : z.re = 0) : ‖z‖ = |z.im| := by
  have hs := Complex.sq_norm z
  simp only [Complex.normSq_apply, hz, zero_mul, zero_add] at hs
  nlinarith [norm_nonneg z, abs_nonneg z.im, sq_abs z.im]

/-- At a collision direction, the absolute difference of the angular
derivatives is the Euclidean distance between the two roots. -/
theorem tangent_difference_length (μ ν : ℂ) (θ : ℝ)
    (he : projection μ θ = projection ν θ) :
    |tangent ν θ - tangent μ θ| = ‖ν - μ‖ := by
  let z := (ν - μ) * Complex.exp ((θ : ℂ) * Complex.I)
  have hr : z.re = 0 := by
    dsimp [z]
    rw [sub_mul, Complex.sub_re]
    simp only [projection_eq] at he
    exact sub_eq_zero.mpr he.symm
  have hj : tangent ν θ - tangent μ θ = -z.im := by
    simp [tangent, z, Complex.mul_re, Complex.mul_im]
    ring
  rw [hj, abs_neg, ← norm_of_real_part_zero z hr]
  dsimp [z]
  rw [norm_mul, norm_unit_exponential, mul_one]

/-- A nonnegative jump has the actual root-distance coefficient, without
requiring either root to be simple. -/
theorem nonnegative_jump_length (μ ν : ℂ) (θ : ℝ)
    (he : projection μ θ = projection ν θ)
    (hjump : 0 ≤ tangent ν θ - tangent μ θ) :
    tangent ν θ - tangent μ θ = ‖ν - μ‖ := by
  simpa only [abs_of_nonneg hjump] using tangent_difference_length μ ν θ he

#print axioms normal_projection
#print axioms projection_hasDeriv
#print axioms tangent_difference_length
#print axioms nonnegative_jump_length
end ZeroDensity.SupportingGeometry
