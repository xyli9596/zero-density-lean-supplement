import V10.CompanionObservation
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! The actual companion eigenvalues satisfy the scalar characteristic equation.
The proof uses the shift rows and final coefficient row, without assuming a
characteristic-polynomial identification. -/

noncomputable section
open Set
namespace V10.CompanionRoots
open V10.CompanionObservation
set_option backward.isDefEq.respectTransparency false

/-- Every eigenvector of the actual companion is its initial component times
the power vector. This includes repeated characteristic roots. -/
theorem eigenvector_coordinates {n : ℕ} (b : Fin (n + 1) → ℂ) {μ : ℂ} {w : State n}
    (hw : Module.End.HasEigenvector (companion b).toLinearMap μ w) :
    ∀ j : Fin (n + 1), w j = μ ^ j.val * w 0 := by
  intro j
  induction j using Fin.induction with
  | zero => simp
  | succ i ih =>
    have h := congrFun hw.apply_eq_smul i.castSucc
    have hs : companion b w i.castSucc = w i.succ := by simp [companion]
    change companion b w i.castSucc = μ * w i.castSucc at h
    rw [hs] at h
    calc
      w i.succ = μ * w i.castSucc := h
      _ = μ * (μ ^ i.val * w 0) := by rw [ih]; simp only [Fin.val_castSucc]
      _ = μ ^ i.succ.val * w 0 := by rw [Fin.val_succ, pow_succ]; ring

theorem eigenvector_first_ne_zero {n : ℕ} (b : Fin (n + 1) → ℂ) {μ : ℂ} {w : State n}
    (hw : Module.End.HasEigenvector (companion b).toLinearMap μ w) : w 0 ≠ 0 := by
  intro hz
  apply hw.2
  funext j
  simp only [eigenvector_coordinates b hw j, hz, mul_zero, Pi.zero_apply]

/-- The root equation for the actual eigenvalue of the companion. -/
theorem eigenvalue_root_equation {n : ℕ} (b : Fin (n + 1) → ℂ) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (companion b).toLinearMap μ) :
    μ ^ (n + 1) + ∑ j : Fin (n + 1), b j * μ ^ j.val = 0 := by
  classical
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have hw0 := eigenvector_first_ne_zero b hw
  have hs : ∑ j : Fin (n + 1), b j * w j =
      (∑ j : Fin (n + 1), b j * μ ^ j.val) * w 0 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [eigenvector_coordinates b hw j]
    ring
  have he := congrFun hw.apply_eq_smul (Fin.last n)
  change companion b w (Fin.last n) = μ * w (Fin.last n) at he
  rw [companion_last, hs, eigenvector_coordinates b hw (Fin.last n), Fin.val_last] at he
  have hp : (μ ^ (n + 1) + ∑ j : Fin (n + 1), b j * μ ^ j.val) * w 0 = 0 := by
    rw [pow_succ]
    linear_combination -he
  exact (mul_eq_zero.mp hp).resolve_right hw0

#print axioms eigenvalue_root_equation

end V10.CompanionRoots
