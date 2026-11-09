import WasowJordanBasis
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! Actual spectral subspaces for Perron theory, including generalized eigenvectors.
No spectral decomposition or semigroup estimate is assumed. -/
noncomputable section
open Module Set
namespace V10.PerronSpectral
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

def spectralSpace (A : End ℂ V) (s : Set A.Eigenvalues) : Submodule ℂ V :=
  ⨆ a ∈ s, A.maxGenEigenspace a.val

def stableSpace (A : End ℂ V) (γ : ℝ) : Submodule ℂ V :=
  spectralSpace A {a | a.val.re < γ}

def unstableSpace (A : End ℂ V) (γ : ℝ) : Submodule ℂ V :=
  spectralSpace A {a | γ < a.val.re}

/-- Any partition of the actual spectrum gives complementary invariant spaces. -/
theorem spectralSpace_isCompl (A : End ℂ V) (s : Set A.Eigenvalues) :
    IsCompl (spectralSpace A s) (spectralSpace A sᶜ) := by
  classical
  have hind : iSupIndep (fun a : A.Eigenvalues => A.maxGenEigenspace a.val) :=
    A.independent_maxGenEigenspace.comp Subtype.val_injective
  refine ⟨hind.disjoint_biSup_biSup' disjoint_compl_right (Set.toFinite s), ?_⟩
  rw [codisjoint_iff, spectralSpace, spectralSpace, ← iSup_union, Set.union_compl_self,
    iSup_univ]
  exact (WasowLeadingBlocks.internal_blocks A).submodule_iSup_eq_top

omit [FiniteDimensional ℂ V] in
theorem spectralSpace_invariant (A : End ℂ V) (s : Set A.Eigenvalues) :
    Set.MapsTo A (spectralSpace A s) (spectralSpace A s) := by
  have hm : (spectralSpace A s).map A ≤ spectralSpace A s := by
    unfold spectralSpace
    rw [Submodule.map_iSup]
    refine iSup_le fun a => ?_
    rw [Submodule.map_iSup]
    refine iSup_le fun ha => ?_
    rintro _ ⟨x, hx, rfl⟩
    have hi : A.maxGenEigenspace a.val ≤ ⨆ b ∈ s, A.maxGenEigenspace b.val :=
      le_iSup_of_le a (le_iSup_of_le ha le_rfl)
    exact hi (A.mapsTo_maxGenEigenspace_of_comm (Commute.refl A) a.val hx)
  exact fun x hx => hm (Submodule.mem_map_of_mem hx)

/-- The only spectral hypothesis is absence of eigenvalues on the separating line. -/
theorem stable_unstable_isCompl (A : End ℂ V) (γ : ℝ)
    (hγ : ∀ a : A.Eigenvalues, a.val.re ≠ γ) :
    IsCompl (stableSpace A γ) (unstableSpace A γ) := by
  have hs : {a : A.Eigenvalues | a.val.re < γ}ᶜ = {a | γ < a.val.re} := by
    ext a
    simp only [mem_compl_iff, mem_ofPred_eq, not_lt]
    constructor
    · intro h
      exact lt_of_le_of_ne h (Ne.symm (hγ a))
    · exact le_of_lt
  simpa only [stableSpace, unstableSpace, hs] using
    spectralSpace_isCompl A {a | a.val.re < γ}

/-- Genuine product coordinates, including an empty stable or unstable block. -/
def spectralCoordinates (A : End ℂ V) (γ : ℝ)
    (hγ : ∀ a : A.Eigenvalues, a.val.re ≠ γ) :
    V ≃ₗ[ℂ] stableSpace A γ × unstableSpace A γ :=
  ((stableSpace A γ).prodEquivOfIsCompl (unstableSpace A γ)
    (stable_unstable_isCompl A γ hγ)).symm

/-- Finiteness supplies a uniform positive distance from the separating line. -/
theorem exists_spectral_gap (A : End ℂ V) (γ : ℝ)
    (hγ : ∀ a : A.Eigenvalues, a.val.re ≠ γ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : A.Eigenvalues,
      a.val.re ≤ γ - δ ∨ γ + δ ≤ a.val.re := by
  classical
  have hfin : ∀ s : Finset A.Eigenvalues, ∃ δ : ℝ, 0 < δ ∧
      ∀ a ∈ s, δ ≤ |a.val.re - γ| := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨δ, hδ, hs⟩ := ih
      refine ⟨min δ |a.val.re - γ|, lt_min hδ (abs_pos.mpr (sub_ne_zero.mpr (hγ a))), ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hs b hb)
  obtain ⟨δ, hδ, hs⟩ := hfin Finset.univ
  refine ⟨δ, hδ, fun a => ?_⟩
  have ha := hs a (Finset.mem_univ a)
  rcases le_total a.val.re γ with h | h
  · left
    rw [abs_of_nonpos (sub_nonpos.mpr h)] at ha
    linarith
  · right
    rw [abs_of_nonneg (sub_nonneg.mpr h)] at ha
    linarith

end V10.PerronSpectral
