import V10.PerronConclusion
import V10.PerronGeneral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Restricting a complex linear differential equation to a ray

The real derivative and the rotation of actual eigenvalues are derived here.
They are not imposed as extra assumptions on the radial solution.
-/

noncomputable section
open Filter Set Module
open scoped Topology
namespace V10.PerronRadial

section Algebra
variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Scaling a genuine eigenvector scales its eigenvalue. -/
theorem hasEigenvalue_smul {A : End ℂ E} {μ : ℂ}
    (hμ : A.HasEigenvalue μ) (c : ℂ) : (c • A).HasEigenvalue (c * μ) := by
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := x)
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hx.2⟩
  simp only [LinearMap.smul_apply, hx.apply_eq_smul, smul_smul]

/-- Every eigenvalue of a nonzero scalar multiple comes from an actual
eigenvalue of the original operator, with no diagonalizability hypothesis. -/
theorem exists_eigenvalue_of_smul {A : End ℂ E} {c ν : ℂ}
    (hc : c ≠ 0) (hν : (c • A).HasEigenvalue ν) :
    ∃ μ : ℂ, A.HasEigenvalue μ ∧ ν = c * μ := by
  refine ⟨c⁻¹ * ν, ?_, by field_simp⟩
  have hh := hasEigenvalue_smul hν c⁻¹
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hh

end Algebra

section Analysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The actual chain rule along a ray. -/
theorem ray_hasDerivAt {Y : ℂ → E} {A : ℂ → E →L[ℂ] E} {c : ℂ} {r : ℝ}
    (hY : HasDerivAt Y (A ((r : ℂ) * c) (Y ((r : ℂ) * c))) ((r : ℂ) * c)) :
    HasDerivAt (fun t : ℝ => Y ((t : ℂ) * c))
      ((c • A ((r : ℂ) * c)) (Y ((r : ℂ) * c))) r := by
  have hr : HasDerivAt (fun t : ℝ => (t : ℂ) * c) c r := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := r)).mul_const c
  simpa only [Function.comp_def, smul_apply] using hY.scomp r hr

/-- Continuity of the rotated coefficient matrix follows from continuity on
the complex domain and the inclusion of the ray. -/
theorem ray_coefficient_continuousOn {A : ℂ → E →L[ℂ] E} {D : Set ℂ}
    {c : ℂ} {T : ℝ} (hA : ContinuousOn A D)
    (hray : ∀ r ≥ T, (r : ℂ) * c ∈ D) :
    ContinuousOn (fun r : ℝ => c • A ((r : ℂ) * c)) (Ici T) := by
  exact (continuous_const : Continuous (fun _ : ℝ => c)).continuousOn.smul
    (hA.comp (Complex.continuous_ofReal.mul_const c).continuousOn hray)

/-- The limiting real-parameter coefficient is the rotated limiting complex
coefficient. -/
theorem ray_coefficient_tendsto {A : ℂ → E →L[ℂ] E} {A₀ : E →L[ℂ] E} (c : ℂ)
    (hA : Tendsto (fun r : ℝ => A ((r : ℂ) * c)) atTop (𝓝 A₀)) :
    Tendsto (fun r : ℝ => c • A ((r : ℂ) * c)) atTop (𝓝 (c • A₀)) :=
  hA.const_smul c

/-- Perron's spectral classification on any ray contained in the coefficient
domain. The coefficient convergence alone is sufficient; no integrable error
or simplicity of eigenvalues is required. -/
theorem ray_growth_exponent [FiniteDimensional ℂ E]
    {Y : ℂ → E} {A : ℂ → E →L[ℂ] E} {A₀ : E →L[ℂ] E}
    {D : Set ℂ} {c : ℂ} {T : ℝ} (hc : c ≠ 0)
    (hA : ContinuousOn A D) (hray : ∀ r ≥ T, (r : ℂ) * c ∈ D)
    (hlim : Tendsto (fun r : ℝ => A ((r : ℂ) * c)) atTop (𝓝 A₀))
    (hode : ∀ z ∈ D, HasDerivAt Y (A z (Y z)) z)
    (hx : Y ((T : ℂ) * c) ≠ 0) :
    ∃ μ : Module.End.Eigenvalues (A₀.toLinearMap : Module.End ℂ E),
      Tendsto (fun r : ℝ => Real.log ‖Y ((r : ℂ) * c)‖ / r)
        atTop (𝓝 (μ.val * c).re) := by
  obtain ⟨ν, hν⟩ := V10.PerronGeneral.perron_growth_exponent
    (ray_coefficient_continuousOn hA hray) (ray_coefficient_tendsto c hlim)
    (fun r hr => ray_hasDerivAt (hode _ (hray r hr))) hx
  have heig : Module.End.HasEigenvalue (c • A₀.toLinearMap) ν.val := ν.property
  obtain ⟨μ, hμ, hrot⟩ := exists_eigenvalue_of_smul hc heig
  refine ⟨⟨μ, hμ⟩, ?_⟩
  change Tendsto (fun r : ℝ => Real.log ‖Y ((r : ℂ) * c)‖ / r)
    atTop (𝓝 (μ * c).re)
  rw [mul_comm μ c, ← hrot]
  exact hν

end Analysis
end V10.PerronRadial
