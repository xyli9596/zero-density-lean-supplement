import ZeroDensity.CountGeometry
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Maps.Proper.Basic

/-! Actual angular sectors, including the inner circular boundary of their
closures. No closure inclusion is an input hypothesis. -/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace ZeroDensity.SectorGeometry
open ZeroDensity.CountGeometry

def logStrip (S a b : ℝ) : Set ℂ :=
  {t | Real.log S < t.re ∧ a < t.im ∧ t.im < b}

theorem sector_eq_exp_strip {S a b : ℝ} (hS : 0 < S) :
    angularSector S a b = Complex.exp '' logStrip S a b := by
  ext z
  constructor
  · rintro ⟨R,hR,θ,hθ,rfl⟩
    have hRp : 0 < R := hS.trans hR
    refine ⟨(Real.log R:ℂ)+(θ:ℂ)*Complex.I, ?_, ?_⟩
    · simpa [logStrip] using And.intro (Real.strictMonoOn_log hS hRp hR) hθ
    · rw [Complex.exp_add]
      simp [← Complex.ofReal_exp,Real.exp_log hRp]
  · rintro ⟨t,ht,rfl⟩
    refine ⟨Real.exp t.re, ?_, t.im, ⟨ht.2.1,ht.2.2⟩, ?_⟩
    · have hh := Real.exp_lt_exp.mpr ht.1
      simpa [Real.exp_log hS] using hh
    · nth_rw 1 [←Complex.re_add_im t]
      rw [Complex.exp_add]
      simp [← Complex.ofReal_exp]

theorem logStrip_open (S a b : ℝ) : IsOpen (logStrip S a b) := by
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const))

theorem logStrip_convex (S a b : ℝ) : Convex ℝ (logStrip S a b) := by
  exact ((convex_Ioi (Real.log S)).linear_preimage Complex.reLm).inter
    ((convex_Ioo a b).linear_preimage Complex.imLm)

theorem sector_open {S a b : ℝ} (hS : 0 < S) : IsOpen (angularSector S a b) := by
  rw [sector_eq_exp_strip hS]
  exact Complex.isOpenMap_exp _ (logStrip_open S a b)

theorem sector_preconnected {S a b : ℝ} (hS : 0 < S) :
    IsPreconnected (angularSector S a b) := by
  rw [sector_eq_exp_strip hS]
  exact (logStrip_convex S a b).isPreconnected.image Complex.exp Complex.continuous_exp.continuousOn

/-- Closed envelope with radius ≥ S, including the entire inner arc. The
angular parameter lives in a compact interval. -/
def envelope (S a b : ℝ) : Set ℂ :=
  Prod.fst '' {p : ℂ × ↥(Icc a b) |
    S ≤ ‖p.1‖ ∧ p.1 = (‖p.1‖:ℂ)*Complex.exp ((p.2:ℝ)*Complex.I)}

theorem envelope_closed (S a b : ℝ) : IsClosed (envelope S a b) := by
  letI : CompactSpace ↥(Icc a b) := isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact (Icc a b))
  apply isClosedMap_fst_of_compactSpace
  apply (isClosed_le continuous_const (continuous_norm.comp continuous_fst)).inter
  apply isClosed_eq continuous_fst
  fun_prop

theorem sector_subset_envelope {S a b : ℝ} (hS : 0 < S) :
    angularSector S a b ⊆ envelope S a b := by
  rintro z ⟨R,hR,θ,hθ,rfl⟩
  have hRp : 0 < R := hS.trans hR
  have hn : ‖(R:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)‖ = R := by
    simp [norm_mul,Complex.norm_exp,abs_of_pos hRp]
  refine ⟨((R:ℂ)*Complex.exp ((θ:ℂ)*Complex.I),⟨θ,hθ.1.le,hθ.2.le⟩), ?_,rfl⟩
  change S ≤ ‖(R:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)‖ ∧
    (R:ℂ)*Complex.exp ((θ:ℂ)*Complex.I) =
      (‖(R:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)‖:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)
  rw [hn]
  exact ⟨hR.le,rfl⟩

/-- Closure of the smaller sector lies inside the wider sector. In
particular, the inner circular boundary R=S₁ is genuinely included. -/
theorem closure_sector_subset {S₀ S₁ a b c d : ℝ}
    (hS₀ : 0 < S₀) (hS : S₀ < S₁) (hca : c < a) (hbd : b < d) :
    closure (angularSector S₁ a b) ⊆ angularSector S₀ c d := by
  have hS₁ : 0 < S₁ := hS₀.trans hS
  have hc := closure_minimal (sector_subset_envelope hS₁) (envelope_closed S₁ a b)
  intro z hz
  obtain ⟨⟨w,θ⟩,hw,he⟩ := hc hz
  dsimp at he
  subst z
  refine ⟨‖w‖,hS.trans_le hw.1,(θ:ℝ),?_,hw.2⟩
  exact ⟨hca.trans_le θ.property.1,lt_of_le_of_lt θ.property.2 hbd⟩

/-- Analyticity on the wider actual sector extends to the complete closure
of the smaller actual sector, including its inner circular boundary. -/
theorem analytic_on_sector_closure {F : ℂ → ℂ} {S₀ S₁ a b c d : ℝ}
    (hS₀ : 0 < S₀) (hS : S₀ < S₁) (hca : c < a) (hbd : b < d)
    (hF : AnalyticOnNhd ℂ F (angularSector S₀ c d)) :
    AnalyticOnNhd ℂ F (closure (angularSector S₁ a b)) :=
  hF.mono (closure_sector_subset hS₀ hS hca hbd)

#print axioms sector_open
#print axioms sector_preconnected
#print axioms closure_sector_subset
#print axioms analytic_on_sector_closure
end ZeroDensity.SectorGeometry
