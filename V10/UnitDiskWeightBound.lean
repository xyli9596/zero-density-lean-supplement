import V10.CoefficientWeight
import V10.AffineScalarZeroCount
import ZeroDensity.BranchCoefficientLimits

/-! The manuscript's actual equation and its explicit weight imply the
solution-independent unit-disk bound in Lemma 4.1. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace V10.UnitDiskWeightBound
open ZeroDensity.Statement ZeroDensity.CoefficientData
open CoefficientWeight BoundedCoefficientZeroCount AffineScalarZeroCount

variable {n : ℕ}

def boundConstant (E : EquationData n) : ℝ :=
  diskCountConstant n (1 + (n : ℝ) * localConstant E)

theorem boundConstant_pos (E : EquationData n) : 0 < boundConstant E := by
  apply diskCountConstant_pos
  have hh := (localConstant_pos E).le
  positivity

/-- Actual multiplicity count in the physical closed unit disk. -/
def unitDiskCount (f : ℂ → ℂ) (c : ℂ) : ℝ :=
  ((∑ᶠ z, MeromorphicOn.divisor f (closedBall c 1) z : ℤ) : ℝ)

/-- The initial jet cannot vanish for a nonzero solution of the actual
polynomial-exponential-coefficient equation. -/
theorem solution_jet_ne_zero (E : EquationData n) {f : ℂ → ℂ}
    (hf : IsSolution E f) (hn : ∃ z, f z ≠ 0) (c : ℂ) :
    ZeroDensity.ScalarLimit.jet n f c ≠ 0 := by
  cases n with
  | zero => have h := E.order_ge_two; omega
  | succ n =>
    have ha := Complex.analyticOnNhd_univ_iff_differentiable.mpr hf.1
    have hc : Continuous (fun z => fun j : Fin (n + 1) => E.coefficient j z) :=
      continuous_pi fun j => continuous_iff_continuousAt.mpr fun z =>
        (ZeroDensity.BranchCoefficientLimits.equation_coefficient_analytic E j z).continuousAt
    obtain ⟨z, hz⟩ := hn
    exact ScalarCompanionODE.jet_nowhere_zero_of_scalar_nontrivial isOpen_univ
      isPreconnected_univ ha hc.continuousOn (fun z _ => hf.2 z)
      ⟨z, mem_univ _, hz⟩ c (mem_univ _)

/-- First conclusion of Lemma 4.1, with a constant constructed only from n
and the actual coefficient data. The estimate is uniform in the solution
and in the center. -/
theorem unit_disk_zero_bound (E : EquationData n) {f : ℂ → ℂ}
    (hf : IsSolution E f) (hn : ∃ z, f z ≠ 0) (c : ℂ) :
    unitDiskCount f c ≤ boundConstant E * weight E c := by
  have hjet := solution_jet_ne_zero E hf hn c
  have ha := Complex.analyticOnNhd_univ_iff_differentiable.mpr hf.1
  cases n with
  | zero => have h := E.order_ge_two; omega
  | succ n =>
    unfold unitDiskCount boundConstant
    simp only [Nat.cast_add, Nat.cast_one]
    apply unit_disk_divisor_le ha hf.2 (weight_ge_one E c) (localConstant_pos E).le
      (b := fun z j => E.coefficient j z) _ hjet
    intro w hw j
    exact coefficient_local_bound E j (by simpa only [dist_eq_norm] using mem_closedBall.mp hw)

/-- Uniform quantification over all nonzero solutions. -/
theorem exists_uniform_unit_disk_zero_bound (E : EquationData n) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℂ → ℂ, IsSolution E f → (∃ z, f z ≠ 0) →
      ∀ c : ℂ, unitDiskCount f c ≤ C * weight E c :=
  ⟨boundConstant E, boundConstant_pos E, fun _ hf hn c => unit_disk_zero_bound E hf hn c⟩

#print axioms unit_disk_zero_bound
#print axioms exists_uniform_unit_disk_zero_bound
end V10.UnitDiskWeightBound
