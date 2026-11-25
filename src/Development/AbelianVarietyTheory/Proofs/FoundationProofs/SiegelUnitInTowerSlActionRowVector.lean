module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
public import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionTransformation
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplex
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

namespace GlobalTheory.KZ.SiegelSL

theorem neBot_Hs : (Filter.codiscreteWithin Hs).NeBot := by
  rw [Filter.neBot_iff]
  intro h
  have hmem : (∅ : Set ℂ) ∈ Filter.codiscreteWithin Hs := h ▸ Filter.mem_bot
  rw [mem_codiscreteWithin] at hmem
  have hI : Complex.I ∈ Hs := by
    show (0 : ℝ) < Complex.I.im
    simp
  have h1 := hmem Complex.I hI
  rw [Set.sdiff_empty, Filter.disjoint_principal_right] at h1
  have h2 : Hs ∈ nhdsWithin Complex.I {Complex.I}ᶜ :=
    mem_nhdsWithin_of_mem_nhds (GlobalTheory.KZ.SiegelModel.isOpen_Hs.mem_nhds hI)
  have h3 := Filter.inter_mem h1 h2
  rw [Set.compl_inter_self] at h3
  simpa using Filter.nonempty_of_mem h3

theorem an_injective {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Tower Ω ε) :
    Function.Injective T.an := by
  have := neBot_Hs
  exact T.an.injective

theorem siegel_eq {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Tower Ω ε) {c : ℕ} {x : Fin 2 → ℚ} {f : T.K}
    (hf : T.an f = ((sgC c x : ℂ → ℂ) : Mero)) : siegel T c x = f := by
  have hex : ∃ g : T.K, T.an g = ((sgC c x : ℂ → ℂ) : Mero) := ⟨f, hf⟩
  apply an_injective T
  rw [siegel, dite_eq_left hex, hex.choose_spec, hf]

theorem sl_siegel : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ)
    (x : Fin 2 → ℚ) (γ : SL(2, ℤ)), admitted c x → T.sl (ofSL γ) (siegel T c x) = siegel T c (act x γ) := by
  intro Ω _ _ _ ε T c x γ hx
  symm
  apply siegel_eq
  rw [T.an_sl _ _ _ (_root_.GlobalTheory.KZ.SiegelMem.an_siegel_eq Ω ε T c x hx)]
  apply GlobalTheory.KZ.SiegelModel.germ_eq_of_eqOn
  intro z hz
  have hτ : ((⟨z, hz⟩ : ℍ) : ℂ) = z := rfl
  rw [← hτ, _root_.GlobalTheory.KZ.SiegelModel.mob_ofSL, _root_.GlobalTheory.KZ.SiegelModel.sgC_coe, _root_.GlobalTheory.KZ.SiegelModel.sgC_coe, _root_.GlobalTheory.Sieg.sg_smul c x γ _ hx]

end GlobalTheory.KZ.SiegelSL
