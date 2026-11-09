import V10.PerronDichotomyCoordinates
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Actual change to finite basis coordinates for the Perron cone argument. -/

set_option backward.isDefEq.respectTransparency false

namespace V10.PerronDichotomyBasis
open Set Filter Module
open scoped Topology Matrix
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual continuous linear coordinate isomorphism of a finite basis. -/
def basisCoordinates (b : Basis ι ℂ E) : E ≃L[ℂ] (ι → ℂ) :=
  b.equivFun.toContinuousLinearEquiv

/-- The conjugated operator acts by its actual matrix in this basis. -/
theorem conjugate_apply_eq_toMatrix (b : Basis ι ℂ E) (A : E →L[ℂ] E) (y : ι → ℂ) :
    ((basisCoordinates b).arrowCongr (basisCoordinates b) A) y =
      LinearMap.toMatrix b b A.toLinearMap *ᵥ y := by
  let e := basisCoordinates b
  have h := LinearMap.toMatrix_mulVec_repr b b A.toLinearMap (e.symm y)
  change LinearMap.toMatrix b b A.toLinearMap *ᵥ e (e.symm y) = e (A (e.symm y)) at h
  change e (A (e.symm y)) = _
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h.symm

omit [FiniteDimensional ℂ E] [Fintype ι] [DecidableEq ι] in
/-- A fixed actual coordinate isomorphism transports the differential equation. -/
theorem conjugated_hasDerivAt (e : E ≃L[ℂ] (ι → ℂ))
    {A : E →L[ℂ] E} {B : ℝ → E →L[ℂ] E} {x : ℝ → E} {t : ℝ}
    (hx : HasDerivAt x (A (x t) + B t (x t)) t) :
    HasDerivAt (fun u => e (x u))
      ((e.arrowCongr e A) (e (x t)) + (e.arrowCongr e (B t)) (e (x t))) t := by
  apply hasDerivAt_pi.mpr
  intro i
  have h := (((ContinuousLinearMap.proj i).comp e.toContinuousLinearMap).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hx
  change HasDerivAt (fun u => e (x u) i) (e (A (x t) + B t (x t)) i) t at h
  simpa only [ContinuousLinearEquiv.arrowCongr_apply,
    ContinuousLinearEquiv.symm_apply_apply, map_add, Pi.add_apply] using h

omit [FiniteDimensional ℂ E] [Fintype ι] [DecidableEq ι] in
/-- Perturbation convergence survives the fixed basis transformation. -/
theorem conjugated_perturbation_tendsto (e : E ≃L[ℂ] (ι → ℂ))
    {B : ℝ → E →L[ℂ] E} (hB : Tendsto B atTop (𝓝 0)) :
    Tendsto (fun t => e.arrowCongr e (B t)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, map_zero] using ((e.arrowCongr e).continuous.tendsto 0).comp hB

/-- The energy dichotomy is transported from actual basis coordinates.
The only unresolved input here is the matrix spectral energy gap, supplied
by the independent Jordan/spectral construction. -/
theorem basis_ode_dichotomy
    (b : Basis ι ℂ E) (s : Finset ι) {A : E →L[ℂ] E}
    {B : ℝ → E →L[ℂ] E} {x : ℝ → E} {T₀ γ δ : ℝ} (hδ : 0 < δ)
    (hode : ∀ t ≥ T₀, HasDerivAt x (A (x t) + B t (x t)) t)
    (hx : x T₀ ≠ 0) (hBcont : ContinuousOn B (Ici T₀))
    (hstable : ∀ y, V10.PerronDichotomyCoordinates.pairing s y
      (LinearMap.toMatrix b b A.toLinearMap *ᵥ y) ≤
        (γ - 2 * δ) * V10.PerronDichotomyCoordinates.energy s y)
    (hunstable : ∀ y, (γ + 2 * δ) * V10.PerronDichotomyCoordinates.energy sᶜ y ≤
      V10.PerronDichotomyCoordinates.pairing sᶜ y
        (LinearMap.toMatrix b b A.toLinearMap *ᵥ y))
    (hBlim : Tendsto B atTop (𝓝 0)) :
    ∃ T ≥ T₀,
      (∃ C : ℝ, 0 < C ∧ ∀ t ≥ T,
        V10.PerronDichotomyCoordinates.energy Finset.univ (basisCoordinates b (x t)) ≤
          C * Real.exp (2 * (γ - δ) * (t - T))) ∨
      (∃ T₁ ≥ T, ∃ C : ℝ, 0 < C ∧ ∀ t ≥ T₁,
        C * Real.exp (2 * (γ + δ) * (t - T₁)) ≤
          V10.PerronDichotomyCoordinates.energy Finset.univ (basisCoordinates b (x t))) := by
  let e := basisCoordinates b
  apply V10.PerronDichotomyCoordinates.actual_asymptotic_coordinate_dichotomy s hδ
    (fun t ht => conjugated_hasDerivAt e (hode t ht))
  · intro hz
    apply hx
    apply e.injective
    simpa using hz
  · exact (e.arrowCongr e).continuous.comp_continuousOn hBcont
  · intro y
    rw [conjugate_apply_eq_toMatrix]
    exact hstable y
  · intro y
    rw [conjugate_apply_eq_toMatrix]
    exact hunstable y
  · exact conjugated_perturbation_tendsto e hBlim

#print axioms conjugate_apply_eq_toMatrix
#print axioms conjugated_hasDerivAt
#print axioms basis_ode_dichotomy
end
end V10.PerronDichotomyBasis
