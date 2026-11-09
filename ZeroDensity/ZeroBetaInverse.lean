import ZeroDensity.InverseBranchFoundations
import ZeroDensity.SectorLogarithm

/-! Complete uniform β=0 inverse asymptotic from the actual primitive and
actual InverseBranch, on every closed angular interval strictly inside its
sector. Neither the inverse expansion nor its integer index is an input. -/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace ZeroDensity.ZeroBetaInverse
open ZeroDensity.MainTheorem ZeroDensity.CountGeometry
open ZeroDensity.InverseBranchFoundations ZeroDensity.SectorGeometry
open ZeroDensity.SectorLogarithm

theorem inverse_uniform_closed {Φ : ℂ → ℂ} {C : ℂ}
    (hΦ : IsPhasePrimitive Φ 0 C) (B : InverseBranch Φ)
    {a b : ℝ} (hleft : B.left < a) (hab : a ≤ b) (hright : b < B.right) :
    ∃ k : ℤ, TendstoUniformlyOn (fun (R : ℝ) (θ : ℝ) =>
      B.ψ ((R:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)) -
      ((Real.log R:ℂ)+(θ:ℂ)*Complex.I+(k:ℂ)*(2*Real.pi*Complex.I)))
      (fun _ => 0) atTop (Icc a b) := by
  let S := max B.S₀ ‖C-Complex.exp 1‖+1
  have hS : 0 < S := by
    have hh := le_max_left B.S₀ ‖C-Complex.exp 1‖
    dsimp [S]; linarith [B.radius_pos]
  have hSB : B.S₀ < S := by
    dsimp [S]; linarith [le_max_left B.S₀ ‖C-Complex.exp 1‖]
  have hSK : ‖C-Complex.exp 1‖ < S := by
    dsimp [S]; linarith [le_max_right B.S₀ ‖C-Complex.exp 1‖]
  let U := angularSector S B.left B.right
  have hsub : U ⊆ angularSector B.S₀ B.left B.right := by
    rintro s ⟨R,hR,θ,hθ,hs⟩
    exact ⟨R,hSB.trans hR,θ,hθ,hs⟩
  have hlarge : ∀ s ∈ U, ‖C-Complex.exp 1‖ < ‖s‖ := by
    rintro s ⟨R,hR,θ,hθ,rfl⟩
    have hRp : 0 < R := hS.trans hR
    simpa [Complex.norm_exp,abs_of_pos hRp] using hSK.trans hR
  let φ := (B.left+B.right)/2
  let s₀ : ℂ := ((S+1:ℝ):ℂ)*Complex.exp ((φ:ℂ)*Complex.I)
  have hs₀ : s₀ ∈ U := by
    refine ⟨S+1,by linarith,φ,?_,rfl⟩
    dsimp [φ]; constructor <;> linarith [B.left_lt_right]
  have hexp : ∀ s ∈ U, Complex.exp (chosenLog φ s) = s := by
    intro s hs
    have hsn : s ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt (hlarge s hs))
    exact exp_chosenLog φ hsn
  apply zero_beta_inverse_uniform hΦ B (sector_open hS) (sector_preconnected hS)
    hsub hlarge (chosenLog φ) (chosenLog_analytic hS B.opening_lt_two_pi)
    hexp hs₀ (Icc a b) id (S+1)
  · intro R hR θ hθ
    refine ⟨R,by linarith,θ,?_,rfl⟩
    exact ⟨hleft.trans_le hθ.1,lt_of_le_of_lt hθ.2 hright⟩
  · intro R hR θ hθ
    have hRp : 0 < R := by linarith
    apply chosenLog_ray hRp
    · dsimp [φ]; linarith [hθ.1,B.opening_lt_two_pi]
    · dsimp [φ]; linarith [hθ.2,B.opening_lt_two_pi]

#print axioms inverse_uniform_closed
end ZeroDensity.ZeroBetaInverse
