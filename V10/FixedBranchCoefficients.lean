import ZeroDensity.BranchCoefficientLimits

/-!
# v10 Lemma 2.1: fixed-branch coefficient limits

This is an explicitly named v10 interface to the already proved legacy
result. It introduces no new analytic assumptions and no new proof of
the underlying analysis. In particular, inverse escape, strip bounds,
and coefficient convergence are derived by the imported proof, not
supplied as hypotheses. The inverse branch itself is part of the
setting of Lemma 2.1; its existence and uniform moving-branch estimates
belong to the separate, stronger v10 Lemma 2.3.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace V10.FixedBranchCoefficients
open ZeroDensity.Statement ZeroDensity.MaximalCoefficientData
open ZeroDensity.MainTheorem ZeroDensity.BranchCoefficientLimits

/-- v10 Lemma 2.1, uniformly on every compact angular subinterval of an
    actual analytic inverse branch of the phase primitive. -/
theorem lemma_2_1 {n : ℕ} (E : EquationData n) (S : Selection E)
    {Φ : ℂ → ℂ} {C : ℂ}
    (hΦ : IsPhasePrimitive Φ (beta E S : ℝ) C)
    (B : InverseBranch Φ) :
    ∀ (k : Fin n) (α₁ α₂ : ℝ), B.left < α₁ → α₁ ≤ α₂ → α₂ < B.right →
      TendstoUniformlyOn
        (fun (R θ : ℝ) => branchCoefficient E S Φ B k
          ((R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
        (fun _ => characteristicCoefficient E S k) atTop (Icc α₁ α₂) := by
  intro k α₁ α₂ hleft horder hright
  exact branch_coefficient_actual_uniform E S hΦ B k hleft horder hright

theorem analytic_coefficients {n : ℕ} (E : EquationData n) (S : Selection E)
    {Φ : ℂ → ℂ} {C : ℂ}
    (hΦ : IsPhasePrimitive Φ (beta E S : ℝ) C)
    (B : InverseBranch Φ) (k : Fin n) :
    AnalyticOnNhd ℂ (branchCoefficient E S Φ B k)
      (ZeroDensity.CountGeometry.angularSector B.S₀ B.left B.right) :=
  branch_coefficient_analytic E S hΦ B k

end V10.FixedBranchCoefficients
