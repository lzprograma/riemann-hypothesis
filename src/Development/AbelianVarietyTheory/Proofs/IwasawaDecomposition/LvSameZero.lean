module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.HermitianForms.TiedTwSame
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsForgetsFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalDilatedClass
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesBijectiveSameDeco
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.TC.StepZero

open GlobalTheory.LvT.StartTie

section Deco

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

end Deco

section Pts2

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n}

end Pts2

attribute [local instance] starE

section Top

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

end Top

section Lv
variable {B : Base} {X : PreX B.toPre} (I : TC B X)

end Lv

section Fields
variable {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)

include hOk in
theorem rep_eCls0 (c : (I.stp u I.mu0 0).Cl) :
    (show PtAt B.R I.sel (I.tup a) (I.cst a) u 0 from (I.stp u a 0).rep (I.eCls0 l u a c)).1.1.deco =
      (show PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u 0 from (I.stp u I.mu0 0).rep c).1.1.deco :=
  ClsZero.stepZero_corresponding_representatives_same_deco hOk u a _ c

end Fields

section Cls
variable {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)

end Cls

section Bw

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)

end Bw

end GlobalTheory.Mem.Col2.TC.StepZero

end
