import ZeroDensity.SectorGeometry
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! A chosen analytic logarithm on every actual sector of opening less than
2π, including angular intervals outside the principal argument range. -/
noncomputable section
set_option autoImplicit false
open Set
open scoped Topology
namespace ZeroDensity.SectorLogarithm
open ZeroDensity.CountGeometry

def chosenLog (φ : ℝ) (s : ℂ) : ℂ :=
  Complex.log (s*Complex.exp (-(φ:ℂ)*Complex.I))+(φ:ℂ)*Complex.I

theorem rotated_ray {R θ φ : ℝ} (hR : 0 < R) :
    ((R:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))*Complex.exp (-(φ:ℂ)*Complex.I) =
      Complex.exp ((Real.log R:ℂ)+((θ-φ:ℝ):ℂ)*Complex.I) := by
  calc
    _ = (R:ℂ)*(Complex.exp ((θ:ℂ)*Complex.I)*Complex.exp (-(φ:ℂ)*Complex.I)) := by ring
    _ = (R:ℂ)*Complex.exp (((θ-φ:ℝ):ℂ)*Complex.I) := by
      rw [←Complex.exp_add]; congr 1; push_cast; ring
    _ = _ := by rw [Complex.exp_add,←Complex.ofReal_exp,Real.exp_log hR]

theorem chosenLog_ray {R θ φ : ℝ} (hR : 0 < R)
    (hlo : -Real.pi < θ-φ) (hhi : θ-φ < Real.pi) :
    chosenLog φ ((R:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)) =
      (Real.log R:ℂ)+(θ:ℂ)*Complex.I := by
  rw [chosenLog,rotated_ray hR,Complex.log_exp (by simpa using hlo) (by simpa using hhi.le)]
  push_cast; ring

theorem exp_chosenLog (φ : ℝ) {s : ℂ} (hs : s ≠ 0) :
    Complex.exp (chosenLog φ s) = s := by
  rw [chosenLog,Complex.exp_add,Complex.exp_log (mul_ne_zero hs (Complex.exp_ne_zero _))]
  calc
    _ = s*(Complex.exp (-(φ:ℂ)*Complex.I)*Complex.exp ((φ:ℂ)*Complex.I)) := by ring
    _ = s := by rw [←Complex.exp_add]; simp

theorem sector_rotation_slit {S a b : ℝ} (hS : 0 < S)
    (hab : b-a < 2*Real.pi) :
    ∀ s ∈ angularSector S a b,
      s*Complex.exp (-(((a+b)/2:ℝ):ℂ)*Complex.I) ∈ Complex.slitPlane := by
  rintro s ⟨R,hR,θ,hθ,rfl⟩
  have hRp : 0 < R := hS.trans hR
  rw [rotated_ray hRp]
  have hlo : -Real.pi < θ-(a+b)/2 := by linarith [hθ.1]
  have hhi : θ-(a+b)/2 < Real.pi := by linarith [hθ.2]
  apply Complex.expOpenPartialHomeomorph.map_source'
  change ((Real.log R:ℂ)+((θ-(a+b)/2:ℝ):ℂ)*Complex.I).im ∈ Ioo (-Real.pi) Real.pi
  simpa only [Set.mem_Ioo,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,mul_one,zero_mul,mul_zero,add_zero,zero_add]
    using And.intro hlo hhi

theorem chosenLog_analytic {S a b : ℝ} (hS : 0 < S)
    (hab : b-a < 2*Real.pi) :
    AnalyticOnNhd ℂ (chosenLog ((a+b)/2)) (angularSector S a b) := by
  intro s hs
  change AnalyticAt ℂ (fun z : ℂ => Complex.log
    (z*Complex.exp (-(((a+b)/2:ℝ):ℂ)*Complex.I))+(((a+b)/2:ℝ):ℂ)*Complex.I) s
  apply AnalyticAt.add
  · apply AnalyticAt.clog
    · exact analyticAt_id.mul analyticAt_const
    · exact sector_rotation_slit hS hab s hs
  · exact analyticAt_const

#print axioms chosenLog_ray
#print axioms chosenLog_analytic
end ZeroDensity.SectorLogarithm
