import V10.PerronSpectral

/-! Arbitrarily small genuine Jordan off-diagonal entries by rescaling the
constructed basis. This is an exact similarity, not an assumed normal form. -/
noncomputable section
open Module
namespace V10.PerronSpectral
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

lemma toMatrix_unitsSMul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℂ V) (w : ι → ℂˣ) (A : End ℂ V) (i j : ι) :
    LinearMap.toMatrix (b.unitsSMul w) (b.unitsSMul w) A i j =
      ((w i : ℂ)⁻¹ * (w j : ℂ)) * LinearMap.toMatrix b b A i j := by
  simp only [LinearMap.toMatrix_apply, Basis.unitsSMul_apply, Units.smul_def,
    map_smul, Basis.repr_unitsSMul, Finsupp.smul_apply, smul_eq_mul,
    Units.val_inv_eq_inv_val]
  ring

/-- Rescale each Jordan chain by powers of any nonzero `ε`. -/
theorem exists_scaled_jordan_basis [FiniteDimensional ℂ V] (A : End ℂ V)
    (ε : ℂ) (hε : ε ≠ 0) :
    ∃ (τ : A.Eigenvalues → Type) (_ : ∀ a, Fintype (τ a))
      (_ : ∀ a, DecidableEq (τ a)) (h : ∀ a, τ a → ℕ)
      (b : Basis (Σ a, WasowMultiShiftReduction.Index (h a)) ℂ V),
      LinearMap.toMatrix b b A = Matrix.blockDiagonal'
        (fun a => a.val • 1 + ε • WasowMultiShiftReduction.jordanShift (h a)) := by
  classical
  obtain ⟨τ, fτ, dτ, h, b, hb⟩ := WasowJordanBasis.exists_generalized_jordan_basis A
  let _ (a) := fτ a
  let _ (a) := dτ a
  let w : (Σ a, WasowMultiShiftReduction.Index (h a)) → ℂˣ :=
    fun i => (Units.mk0 ε hε) ^ i.2.2.val
  refine ⟨τ, fτ, dτ, h, b.unitsSMul w, ?_⟩
  ext ⟨a, c, i⟩ ⟨a', c', j⟩
  rw [toMatrix_unitsSMul, hb]
  by_cases haa : a = a'
  · subst a'
    rw [Matrix.blockDiagonal'_apply_eq, Matrix.blockDiagonal'_apply_eq]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases hcc : c = c'
    · subst c'
      simp only [WasowMultiShiftReduction.jordanShift, Matrix.blockDiagonal'_apply_eq]
      simp only [WasowShiftReduction.shift]
      by_cases hij : i = j
      · subst j
        simp [w, pow_ne_zero _ hε]
      · have hiij : (⟨c, i⟩ : WasowMultiShiftReduction.Index (h a)) ≠ ⟨c, j⟩ := by
          simpa using hij
        simp only [Matrix.one_apply, hiij, if_false, mul_zero, zero_add]
        by_cases hnext : j.val = i.val + 1
        · simp only [hnext, if_true, mul_one]
          simp only [w, Units.val_pow_eq_pow_val, Units.val_mk0]
          field_simp
          rw [hnext, pow_succ]
        · simp [hnext]
    · have hij : (⟨c, i⟩ : WasowMultiShiftReduction.Index (h a)) ≠ ⟨c', j⟩ := by
        intro hh
        exact hcc (congrArg Sigma.fst hh)
      simp [hij, WasowMultiShiftReduction.jordanShift,
        Matrix.blockDiagonal'_apply_ne _ _ _ hcc]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ haa,
      Matrix.blockDiagonal'_apply_ne _ _ _ haa, mul_zero]

/-- Every finite-dimensional complex operator admits coordinates with arbitrarily
small off-diagonal entries, preserving the full eigenvalue blocks. -/
theorem exists_small_remainder_basis [FiniteDimensional ℂ V] (A : End ℂ V)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Basis ι ℂ V)
      (lam : ι → ℂ) (N : Matrix ι ι ℂ),
      (∀ i, A.HasEigenvalue (lam i)) ∧
      LinearMap.toMatrix b b A = Matrix.diagonal lam + N ∧
      (∀ i j, ‖N i j‖ ≤ ε) ∧ (∀ i j, lam i ≠ lam j → N i j = 0) := by
  classical
  obtain ⟨τ, fτ, dτ, h, b, hb⟩ := exists_scaled_jordan_basis A (ε : ℂ)
    (by exact_mod_cast hε.ne')
  let _ (a) := fτ a
  let _ (a) := dτ a
  let ι := Σ a, WasowMultiShiftReduction.Index (h a)
  let N : Matrix ι ι ℂ := Matrix.blockDiagonal'
    (fun a => (ε : ℂ) • WasowMultiShiftReduction.jordanShift (h a))
  refine ⟨ι, inferInstance, inferInstance, b, (fun i => i.1.val), N,
    (fun i => i.1.property), ?_, ?_, ?_⟩
  · rw [hb]
    ext ⟨a,c,i⟩ ⟨a',c',j⟩
    by_cases haa : a = a'
    · subst a'
      simp [N, Matrix.diagonal, Matrix.one_apply, Matrix.blockDiagonal'_apply_eq, ι]
    · have hij : (⟨a, c, i⟩ : ι) ≠ ⟨a', c', j⟩ := by
        intro hh
        exact haa (congrArg Sigma.fst hh)
      simp [N, Matrix.diagonal, hij, Matrix.blockDiagonal'_apply_ne _ _ _ haa]
  · intro ⟨a,c,i⟩ ⟨a',c',j⟩
    by_cases haa : a = a'
    · subst a'
      simp only [N, Matrix.blockDiagonal'_apply_eq, Matrix.smul_apply, smul_eq_mul,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
      by_cases hcc : c = c'
      · subst c'
        simp only [WasowMultiShiftReduction.jordanShift, Matrix.blockDiagonal'_apply_eq,
          WasowShiftReduction.shift]
        split_ifs <;> simp [hε.le]
      · simp [WasowMultiShiftReduction.jordanShift,
          Matrix.blockDiagonal'_apply_ne _ _ _ hcc, hε.le]
    · simp [N, Matrix.blockDiagonal'_apply_ne _ _ _ haa, hε.le]
  · intro i j hij
    have haa : i.1 ≠ j.1 := fun hh => hij (congrArg Subtype.val hh)
    exact Matrix.blockDiagonal'_apply_ne _ _ _ haa

end V10.PerronSpectral
