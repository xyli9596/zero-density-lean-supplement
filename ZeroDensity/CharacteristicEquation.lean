import ZeroDensity.MaximalCoefficientData
import ZeroDensity.LocalRootSelection
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! The roots in Theorem 3.1 are the actual distinct roots of the polynomial
computed from the equation. The exponential substitution below is an exact
calculation for the limiting equation, not a solution formula for the
variable-coefficient equation.
-/
noncomputable section
set_option autoImplicit false
open Polynomial
open scoped BigOperators
namespace ZeroDensity.CharacteristicEquation
open MaximalCoefficientData Statement
variable {n : ℕ}
attribute [local instance] Classical.propDecidable Classical.decEq

def roots (E : EquationData n) (S : Selection E) : Finset ℂ :=
  (characteristicPolynomial E S).roots.toFinset

theorem characteristic_ne_zero (E : EquationData n) (S : Selection E) :
    characteristicPolynomial E S ≠ 0 :=
  (characteristicPolynomial_monic E S).ne_zero

theorem mem_roots (E : EquationData n) (S : Selection E) (μ : ℂ) :
    μ ∈ roots E S ↔ (characteristicPolynomial E S).eval μ = 0 := by
  simp only [roots, Multiset.mem_toFinset, Polynomial.mem_roots (characteristic_ne_zero E S),
    Polynomial.IsRoot.def]

theorem roots_nonempty (E : EquationData n) (S : Selection E) : (roots E S).Nonempty := by
  have hn := E.order_ge_two
  have hd : 0 < (characteristicPolynomial E S).degree := by
    rw [Polynomial.degree_eq_natDegree (characteristic_ne_zero E S),
      characteristicPolynomial_natDegree]
    exact_mod_cast (show 0 < n by omega)
  obtain ⟨μ, hm⟩ := Complex.exists_root hd
  exact ⟨μ, (mem_roots E S μ).mpr hm⟩

theorem polynomial_eval (E : EquationData n) (S : Selection E) (μ : ℂ) :
    (characteristicPolynomial E S).eval μ =
      μ ^ n + ∑ j : Fin n, characteristicCoefficient E S j * μ ^ j.val := by
  simp [characteristicPolynomial, Polynomial.eval_finsetSum]

def limitingOperator (E : EquationData n) (S : Selection E) (v : ℂ → ℂ) (s : ℂ) : ℂ :=
  iteratedDeriv n v s +
    ∑ j : Fin n, characteristicCoefficient E S j * iteratedDeriv j.val v s

/-- Every derivative contributes the ordinary power μ^j in the limiting
constant-coefficient equation. No falling factorial is involved. -/
theorem exponential_substitution (E : EquationData n) (S : Selection E) (μ s : ℂ) :
    limitingOperator E S (fun z => Complex.exp (μ * z)) s =
      (characteristicPolynomial E S).eval μ * Complex.exp (μ * s) := by
  unfold limitingOperator
  simp only [iteratedDeriv_cexp_const_mul]
  rw [polynomial_eval, add_mul, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem exponential_solves_iff (E : EquationData n) (S : Selection E) (μ s : ℂ) :
    limitingOperator E S (fun z => Complex.exp (μ * z)) s = 0 ↔ μ ∈ roots E S := by
  rw [exponential_substitution, mul_eq_zero]
  simp only [Complex.exp_ne_zero, or_false, mem_roots]

/-- The local root selection is explicitly linked to the polynomial roots.
Its continuous-indicator hypotheses still have to be supplied by the
asymptotic analysis of the actual solution. -/
theorem selected_roots_nonempty (E : EquationData n) (S : Selection E) {h : ℝ → ℝ} {l u : ℝ}
    (hlu : l < u) (hh : ContinuousOn h (Set.Ioo l u))
    (halt : ∀ θ ∈ Set.Ioo l u, ∃ μ ∈ roots E S,
      h θ = LocalRootSelection.projection μ θ) :
    (LocalRootSelection.selected (roots E S) h l u).Nonempty :=
  LocalRootSelection.selected_nonempty (roots E S) hlu hh halt

#print axioms roots_nonempty
#print axioms exponential_substitution
#print axioms exponential_solves_iff
#print axioms selected_roots_nonempty
end ZeroDensity.CharacteristicEquation
