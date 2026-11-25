module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelMulArchimedeanMemNhds
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult
  MeasureTheory Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.BasisPolynomialParabolics

variable {D : D7}

abbrev Bas (V : HSp D) : Type := D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ

abbrev Pol (S T : HSp D) : Type := MvPolynomial (FVar D T.rank S.rank) ℂ

abbrev cmp (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (g : GA D V) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  infMat D.sp.cm.sig V.gram (θ τ) g

section Pair

variable (θ : InfFam D) {S T : HSp D} (BS : Bas S) (BT : Bas T) (e : D.what₂.Tau → ℚ)

def subst (g : GA D S) (h : GA D T) (x : FVar D T.rank S.rank) : Pol S T :=
  ∑ i, ∑ c, MvPolynomial.C (((BT x.1)⁻¹ * cmp θ T x.1 h * BT x.1) i x.2.1 * ((BS x.1)⁻¹ * cmp θ S x.1 g⁻¹ * BS x.1) x.2.2 c) *
    MvPolynomial.X (x.1, i, c)

variable (π : CoefA S) (π' : CoefA T)

end Pair

def fp (V : HSp D) (g : GA D V) : GfC V := ⟨GlobalTheory.LevelNbhd.finPartG V g, GlobalTheory.LevelNbhd.finPartG_mem_GfC V g⟩

end GlobalTheory.IndefiniteRowSideFullHecke.BasisPolynomialParabolics

end
