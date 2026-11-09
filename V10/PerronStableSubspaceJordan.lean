import V10.PerronStableSubspaceMultiplicity
import V10.PerronSpectralJordan

/-! Jordan coordinates with certified algebraic multiplicities. The dimension
information is retained through the actual basis construction and rescaling. -/
noncomputable section
open Module
namespace V10.PerronStableSubspace
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Genuine Jordan coordinates with each primary block's algebraic multiplicity. -/
theorem exists_jordan_basis_multiplicity (A : End ℂ V) :
    ∃ (τ : A.Eigenvalues → Type) (_ : ∀ a, Fintype (τ a))
      (_ : ∀ a, DecidableEq (τ a)) (h : ∀ a, τ a → ℕ)
      (b : Basis (Σ a, WasowMultiShiftReduction.Index (h a)) ℂ V),
      LinearMap.toMatrix b b A = Matrix.blockDiagonal'
        (fun a => a.val • 1 + WasowMultiShiftReduction.jordanShift (h a)) ∧
      ∀ a, Fintype.card (WasowMultiShiftReduction.Index (h a)) =
        A.charpoly.rootMultiplicity a.val := by
  classical
  let g (a : A.Eigenvalues) : End ℂ (WasowLeadingBlocks.blockSpace A a) :=
    WasowLeadingBlocks.restriction A a -
      algebraMap ℂ (End ℂ (WasowLeadingBlocks.blockSpace A a)) a.val
  have hn (a : A.Eigenvalues) : IsNilpotent (g a) :=
    WasowLeadingBlocks.restriction_sub_nilpotent A a
  choose τ fτ dτ h b hb using fun a => WasowJordanBasis.exists_jordan_basis (g a) (hn a)
  let _ (a) := fτ a
  let _ (a) := dτ a
  refine ⟨τ, fτ, dτ, h, (WasowLeadingBlocks.internal_blocks A).collectedBasis b, ?_, ?_⟩
  · rw [LinearMap.toMatrix_directSum_collectedBasis_eq_blockDiagonal'
      (WasowLeadingBlocks.internal_blocks A) (WasowLeadingBlocks.internal_blocks A) b b
      (WasowLeadingBlocks.block_invariant A)]
    congr 1
    funext a
    have hrel : WasowLeadingBlocks.restriction A a = g a +
        algebraMap ℂ (End ℂ (WasowLeadingBlocks.blockSpace A a)) a.val := by
      dsimp [g]
      abel
    change LinearMap.toMatrix (b a) (b a) (WasowLeadingBlocks.restriction A a) = _
    rw [hrel, map_add, hb a]
    simp [Algebra.algebraMap_eq_smul_one, add_comm]
  · intro a
    rw [← Module.finrank_eq_card_basis (b a)]
    exact LinearMap.finrank_maxGenEigenspace_eq A a.val

theorem exists_scaled_jordan_basis_multiplicity (A : End ℂ V)
    (ε : ℂ) (hε : ε ≠ 0) :
    ∃ (τ : A.Eigenvalues → Type) (_ : ∀ a, Fintype (τ a))
      (_ : ∀ a, DecidableEq (τ a)) (h : ∀ a, τ a → ℕ)
      (b : Basis (Σ a, WasowMultiShiftReduction.Index (h a)) ℂ V),
      LinearMap.toMatrix b b A = Matrix.blockDiagonal'
        (fun a => a.val • 1 + ε • WasowMultiShiftReduction.jordanShift (h a)) ∧
      ∀ a, Fintype.card (WasowMultiShiftReduction.Index (h a)) =
        A.charpoly.rootMultiplicity a.val := by
  classical
  obtain ⟨τ, fτ, dτ, h, b, hb, hcard⟩ := exists_jordan_basis_multiplicity A
  let _ (a) := fτ a
  let _ (a) := dτ a
  let w : (Σ a, WasowMultiShiftReduction.Index (h a)) → ℂˣ :=
    fun i => (Units.mk0 ε hε) ^ i.2.2.val
  refine ⟨τ, fτ, dτ, h, b.unitsSMul w, ?_, hcard⟩
  ext ⟨a, c, i⟩ ⟨a', c', j⟩
  rw [V10.PerronSpectral.toMatrix_unitsSMul, hb]
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


theorem exists_small_remainder_basis_multiplicity (A : End ℂ V)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Basis ι ℂ V)
      (lam : ι → ℂ) (N : Matrix ι ι ℂ),
      (∀ i, A.HasEigenvalue (lam i)) ∧
      LinearMap.toMatrix b b A = Matrix.diagonal lam + N ∧
      (∀ i j, ‖N i j‖ ≤ ε) ∧ (∀ i j, lam i ≠ lam j → N i j = 0) ∧
      ∀ a : A.Eigenvalues, Fintype.card {i : ι // lam i = a.val} =
        A.charpoly.rootMultiplicity a.val := by
  classical
  obtain ⟨τ, fτ, dτ, h, b, hb, hcard⟩ := exists_scaled_jordan_basis_multiplicity A (ε : ℂ)
    (by exact_mod_cast hε.ne')
  let _ (a) := fτ a
  let _ (a) := dτ a
  let ι := Σ a, WasowMultiShiftReduction.Index (h a)
  let N : Matrix ι ι ℂ := Matrix.blockDiagonal'
    (fun a => (ε : ℂ) • WasowMultiShiftReduction.jordanShift (h a))
  refine ⟨ι, inferInstance, inferInstance, b, (fun i => i.1.val), N,
    (fun i => i.1.property), ?_, ?_, ?_, ?_⟩
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

  · intro a
    let e : {i : ι // i.1.val = a.val} ≃ WasowMultiShiftReduction.Index (h a) :=
      (Equiv.subtypeEquivRight (fun i => (Subtype.ext_iff).symm)).trans (Equiv.sigmaSubtype a)
    exact (Fintype.card_congr e).trans (hcard a)

end V10.PerronStableSubspace
