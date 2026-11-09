import V10.ProjectionExceptionalCone
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Literal finite holomorphic rows, with the Euclidean row norm. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ComplexConjugate
namespace V10.ProjectionRowFamily
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι]

def rowVector (f : ι → ℂ → ℂ) (z : ℂ) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun j => f j z)

def rowFunctional (f : ι → ℂ → ℂ) (z : ℂ) : EuclideanSpace ℂ ι →L[ℂ] ℂ :=
  ∑ j, f j z • EuclideanSpace.proj j

theorem rowFunctional_apply (f : ι → ℂ → ℂ) (z : ℂ) (c : EuclideanSpace ℂ ι) :
    rowFunctional f z c = ∑ j, f j z * c j := by
  simp [rowFunctional]

/-- The norm used in the abstract projection construction is exactly the
Euclidean norm of the finite row in the manuscript. -/
theorem rowFunctional_norm (f : ι → ℂ → ℂ) (z : ℂ) :
    ‖rowFunctional f z‖ = ‖rowVector f z‖ := by
  have he : rowFunctional f z =
      innerSL ℂ (WithLp.toLp 2 (fun j => conj (f j z)) : EuclideanSpace ℂ ι) := by
    ext c
    simp [rowFunctional_apply, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  rw [he, innerSL_apply_norm]
  simp [EuclideanSpace.norm_eq, rowVector]

theorem rowFunctional_continuous {f : ι → ℂ → ℂ}
    (hf : ∀ j, Continuous (f j)) : Continuous (rowFunctional f) := by
  unfold rowFunctional
  fun_prop

theorem rowFunctional_ne_zero {f : ι → ℂ → ℂ}
    (hn : ∀ z, ∃ j, f j z ≠ 0) (z : ℂ) : rowFunctional f z ≠ 0 := by
  classical
  obtain ⟨j, hj⟩ := hn z
  intro he
  have h := congrArg (fun T : EuclideanSpace ℂ ι →L[ℂ] ℂ =>
    T (EuclideanSpace.single j 1)) he
  simp [rowFunctional_apply, PiLp.single_apply] at h
  exact hj h

theorem rowFunctional_analytic {f : ι → ℂ → ℂ}
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) univ) (c : EuclideanSpace ℂ ι) :
    AnalyticOnNhd ℂ (fun z => rowFunctional f z c) univ := by
  simp only [rowFunctional_apply]
  exact Finset.analyticOnNhd_fun_sum Finset.univ
    (fun j _ => (hf j).mul analyticOnNhd_const)

theorem rowFunctional_nontrivial {f : ι → ℂ → ℂ}
    (hi : LinearIndependent ℂ f) {c : EuclideanSpace ℂ ι} (hc : c ≠ 0) :
    ∃ z, rowFunctional f z c ≠ 0 := by
  by_contra! he
  have hsum : ∑ j, c j • f j = 0 := by
    ext z
    simpa [rowFunctional_apply, mul_comm] using he z
  have hz := Fintype.linearIndependent_iff.mp hi (fun j => c j) hsum
  exact hc (by ext j; simpa using hz j)

#print axioms rowFunctional_norm
#print axioms rowFunctional_continuous
#print axioms rowFunctional_ne_zero
#print axioms rowFunctional_analytic
#print axioms rowFunctional_nontrivial
end V10.ProjectionRowFamily
