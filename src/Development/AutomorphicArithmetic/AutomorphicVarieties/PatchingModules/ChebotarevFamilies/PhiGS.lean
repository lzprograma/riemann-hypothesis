module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PhiCondOfFiniteH1

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

namespace UpperTheory.V.Pa

end UpperTheory.V.Pa

theorem UpperTheory.V.Pa.phiGS :
    GlobalFiniteness → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V : s.Lev), PhiCond V.frame.Γ l := by
  intro hGF l _ L Ω _ _ _ _ _ _ s V
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset (Plc (Lp L)), (S : Set (Plc (Lp L))) = V.S' :=
    ⟨V.fin.toFinset, V.fin.coe_toFinset⟩
  show PhiCond (ReciprocityTheory.Gal.GS Ω V.S') l
  rw [← hS]
  have key : PhiCond (ReciprocityTheory.Gal.GS Ω (S : Set (Plc (Lp L)))) (l ^ 1) := by
    apply UpperTheory.V.Alg.phiCond_of_finite_H1
    intro M _ _ _ _ _ ρ hρ
    have habove : ReciprocityTheory.Gal.ContainsAbove S l := by
      intro v hv
      have hv' : v ∈ V.S' := V.sub (Or.inl hv)
      rw [← hS] at hv'
      exact_mod_cast hv'
    exact (hGF (Lp L) Ω l 1 M S ρ one_pos habove hρ).2.1
  rw [pow_one] at key
  exact key
