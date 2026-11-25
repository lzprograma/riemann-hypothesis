module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.latticeCompletion_eq_of_local_agreement : ∀ {D : D7} (S : HSp D) (L N : GlobalTheory.FinPl.Lat S) (P : GlobalTheory.FinPl.Pl D → Prop), Submodule.IsLattice D.host.E L → Submodule.IsLattice D.host.E N → (∀ w, P w → GlobalTheory.FinPl.latV S L (· = w) = GlobalTheory.FinPl.latV S N (· = w)) → GlobalTheory.FinPl.latV S L P = GlobalTheory.FinPl.latV S N P := by
  intro D S L N P hL hN hP
  ext y
  rw [GlobalTheory.FinPlLoc.part_lat P S L y hL,
    GlobalTheory.FinPlLoc.part_lat P S N y hN]
  constructor <;> rintro ⟨hs, hl⟩ <;> refine ⟨hs, fun v hv e he => ?_⟩
  · rw [← hP v hv]
    exact hl v hv e he
  · rw [hP v hv]
    exact hl v hv e he
