module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKilledEqOfEqualMultiplicities

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
open GlobalTheory.CuspMult

theorem _root_.GlobalTheory.T.finrank_killed_eq_of_equal_multiplicities : ∀ (H : Type) [Group H] [TopologicalSpace H] (X Y : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (ρ : Representation ℂ H X) (ρ' : Representation ℂ H Y) (C : Submodule ℂ X) (C' : Submodule ℂ Y) (I : Set (MonoidAlgebra ℂ H)), IsDecomp ρ C → IsDecomp ρ' C' → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H W), σ.IsIrreducible → GlobalTheory.PRep.IsAdmissible σ → killed σ I ≠ ⊥ → Module.rank ℂ (homInto σ ρ C) = Module.rank ℂ (homInto σ ρ' C')) → (∀ x ∈ killed ρ I, IsOpen {g : H | ρ g x = x}) → (∀ y ∈ killed ρ' I, IsOpen {g : H | ρ' g y = y}) → FiniteDimensional ℂ (C ⊓ killed ρ I : Submodule ℂ X) → FiniteDimensional ℂ (C' ⊓ killed ρ' I : Submodule ℂ Y) → Module.finrank ℂ (C ⊓ killed ρ I : Submodule ℂ X) = Module.finrank ℂ (C' ⊓ killed ρ' I : Submodule ℂ Y) := by
  first | exact @GlobalTheory.RepCount.finrank_inf_killed_eq
