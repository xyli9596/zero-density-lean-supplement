import V10.PerronStableSubspaceJordan
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The actual coordinates for the half-line contraction: prescribed arbitrarily
small operator remainder, spectral gap, and the exact n-minus-m stable dimension. -/
noncomputable section
open Module
open scoped BigOperators Matrix
namespace V10.PerronStableSubspace

lemma matrix_opNorm_le_card_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : Matrix ι ι ℂ) {ε : ℝ} (hε : 0 ≤ ε) (hN : ∀ i j, ‖N i j‖ ≤ ε) :
    ‖(Matrix.toLin' N).toContinuousLinearMap‖ ≤ Fintype.card ι * ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hε)
  intro x
  change ‖N *ᵥ x‖ ≤ (Fintype.card ι * ε) * ‖x‖
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change ‖∑ j, N i j * x j‖ ≤ _
  calc
    _ ≤ ∑ j, ‖N i j * x j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : ι, ε * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul (hN i j) (norm_le_pi_norm x j) (norm_nonneg _) hε
    _ = _ := by simp; ring

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- A true spectral cut supplies a fixed positive gap. For every desired positive
remainder norm, actual coordinates realize that bound and retain the exact
algebraic-multiplicity count. This is suitable for absorbing Jordan terms into
a uniformly small perturbation. -/
theorem exists_stable_coordinates (A : End ℂ V) (γ : ℝ) (μ : ℂ)
    (hμ : A.HasEigenvalue μ) (hμre : γ < μ.re)
    (hrest : ∀ a : A.Eigenvalues, a.val ≠ μ → a.val.re < γ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ η : ℝ, 0 < η →
      ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
        (b : Basis ι ℂ V) (mode : ι → Bool) (lam : ι → ℂ) (N : Matrix ι ι ℂ),
        LinearMap.toMatrix b b (A - (γ : ℂ) • 1) = Matrix.diagonal lam + N ∧
        (∀ i, if mode i then (lam i).re ≤ -δ else δ ≤ (lam i).re) ∧
        ‖(Matrix.toLin' N).toContinuousLinearMap‖ ≤ η ∧
        Fintype.card {i : ι // mode i = true} =
          finrank ℂ V - A.charpoly.rootMultiplicity μ := by
  classical
  have hcut : ∀ a : A.Eigenvalues, a.val.re ≠ γ := by
    intro a
    by_cases ha : a.val = μ
    · simpa [ha] using hμre.ne'
    · exact (hrest a ha).ne
  obtain ⟨δ, hδ, hgap⟩ := V10.PerronSpectral.exists_spectral_gap A γ hcut
  refine ⟨δ, hδ, ?_⟩
  intro η hη
  let n : ℝ := finrank ℂ V
  let ε : ℝ := η / (n + 1)
  have hn : 0 < n + 1 := by dsimp [n]; positivity
  have hε : 0 < ε := div_pos hη hn
  obtain ⟨ι, fι, dι, b, oldlam, N, heigen, hA, hN, _hblocks, hcount⟩ :=
    exists_small_remainder_basis_multiplicity A ε hε
  let _ := fι
  let _ := dι
  let mode : ι → Bool := fun i => decide ((oldlam i).re < γ)
  let lam : ι → ℂ := fun i => oldlam i - γ
  refine ⟨ι, fι, dι, b, mode, lam, N, ?_, ?_, ?_, ?_⟩
  · rw [map_sub, map_smul, LinearMap.toMatrix_one, hA]
    have hd : Matrix.diagonal lam = Matrix.diagonal oldlam - (γ : ℂ) • 1 := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [lam, Matrix.diagonal]
      · simp [lam, Matrix.diagonal, hij]
    rw [hd]
    abel
  · intro i
    have hg := hgap ⟨oldlam i, heigen i⟩
    dsimp at hg
    simp only [mode, decide_eq_true_eq, lam, Complex.sub_re, Complex.ofReal_re]
    split_ifs with hi
    · rcases hg with hg | hg <;> linarith
    · rcases hg with hg | hg <;> linarith
  · have hc : (Fintype.card ι : ℝ) = n := by
      dsimp [n]
      exact_mod_cast (Module.finrank_eq_card_basis b).symm
    apply (matrix_opNorm_le_card_mul N hε.le hN).trans
    rw [hc]
    calc
      n * ε ≤ (n + 1) * ε := by gcongr; linarith
      _ = η := by dsimp [ε]; field_simp
  · have hp : ∀ i : ι, mode i = true ↔ ¬oldlam i = μ := by
      intro i
      simp only [mode, decide_eq_true_eq]
      constructor
      · intro hi he
        rw [he] at hi
        exact (not_lt_of_ge hμre.le) hi
      · intro hi
        exact hrest ⟨oldlam i, heigen i⟩ hi
    have hc := Fintype.card_congr (Equiv.subtypeEquivRight hp)
    have hμcount : Fintype.card {i : ι // oldlam i = μ} =
        A.charpoly.rootMultiplicity μ := hcount ⟨μ, hμ⟩
    rw [Fintype.card_subtype_compl, hμcount, ← Module.finrank_eq_card_basis b] at hc
    exact hc

end V10.PerronStableSubspace
