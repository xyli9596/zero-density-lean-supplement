import V10.PerronSpectral
import Mathlib.LinearAlgebra.Eigenspace.Zero

/-! The unperturbed stable spectral space has dimension n minus the actual
algebraic multiplicity of the unique eigenvalue above the spectral cut. -/
noncomputable section
open Module
namespace V10.PerronStableSubspace
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
theorem unstableSpace_eq_maxGenEigenspace (A : End ℂ V) (γ : ℝ) (μ : ℂ)
    (hμ : A.HasEigenvalue μ) (hμre : γ < μ.re)
    (hrest : ∀ a : A.Eigenvalues, a.val ≠ μ → a.val.re < γ) :
    V10.PerronSpectral.unstableSpace A γ = A.maxGenEigenspace μ := by
  unfold V10.PerronSpectral.unstableSpace V10.PerronSpectral.spectralSpace
  apply le_antisymm
  · refine iSup_le fun a => iSup_le fun ha => ?_
    have he : a.val = μ := by
      by_contra hh
      have hh' := hrest a hh
      exact (not_lt_of_ge ha.le) hh'
    rw [he]
  · exact le_iSup_of_le ⟨μ, hμ⟩ (le_iSup_of_le hμre le_rfl)

/-- Algebraic multiplicity, not the number of distinct eigenvalues or geometric
multiplicity, controls the codimension. -/
theorem stableSpace_finrank (A : End ℂ V) (γ : ℝ) (μ : ℂ)
    (hμ : A.HasEigenvalue μ) (hμre : γ < μ.re)
    (hrest : ∀ a : A.Eigenvalues, a.val ≠ μ → a.val.re < γ) :
    finrank ℂ (V10.PerronSpectral.stableSpace A γ) =
      finrank ℂ V - A.charpoly.rootMultiplicity μ := by
  have hcut : ∀ a : A.Eigenvalues, a.val.re ≠ γ := by
    intro a
    by_cases ha : a.val = μ
    · simpa [ha] using hμre.ne'
    · exact (hrest a ha).ne
  have hh := Submodule.finrank_add_eq_of_isCompl
    (V10.PerronSpectral.stable_unstable_isCompl A γ hcut)
  rw [unstableSpace_eq_maxGenEigenspace A γ μ hμ hμre hrest,
    LinearMap.finrank_maxGenEigenspace_eq] at hh
  omega

end V10.PerronStableSubspace
