module

import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelLin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section
variable {l : ℕ} [Fact l.Prime] (F : GFrame l) {n : ℕ} {A R : Type} [CommRing A] [CommRing R] [Algebra A R]

end

theorem UpperTheory.V.Pa.Det.selSub :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) {n : ℕ} {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (t : A) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R) (V : Submodule A (Matrix (Fin n) (Fin n) R)), (∃ S : Submodule A (F.G₀ → Matrix (Fin n) (Fin n) R), (S : Set _) = SelZ F t ρ w wi V) ∧ ∃ S : Submodule A (F.G₀ → Matrix (Fin n) (Fin n) R), (S : Set _) = Bd F ρ V := by
  apply UpperTheory.V.Pa.sel_lin
