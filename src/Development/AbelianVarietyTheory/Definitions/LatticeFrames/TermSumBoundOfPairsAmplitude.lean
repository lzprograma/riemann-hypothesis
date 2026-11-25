module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DimFormC
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP

@[expose] public section

noncomputable section
open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.KappaOffDiagonal Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
namespace GlobalTheory.Core.Deg

def PairsDegOfType : Prop :=
  ∀ CH Ch Cp C : ℝ, 0 ≤ CH → 0 ≤ Ch → 0 ≤ Cp → 2 * (CH + 1) ≤ C → ∃ Cl₀ : ℝ,
    ∀ (C' Cl Cg cb Cw cT CT C0 : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Cl₀ ≤ Cl →
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → TypeAt large₂ Y u CH (Cp + 4) C Ch Cp →
      Formalism.L2.SG.RowsOther.PairsDegAmp (Y.tO u u) (PgC Y) (duC X Y u) D.R.k D.R.f

def TermSumBoundOfPairsAmplitude : Prop :=
  ∀ (C' Cl Cg cb Cw cT CT C0 : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
    Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → (Y.tO u u).AbsConv →
    Formalism.L2.SG.RowsOther.PairsDegAmp (Y.tO u u) (PgC Y) (duC X Y u) D.R.k D.R.f → VanishingGramTermsBound Y u

end GlobalTheory.Core.Deg
