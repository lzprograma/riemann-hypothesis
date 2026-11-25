module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHermPart
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InCell

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
open IsDedekindDomain NumberField
namespace GlobalTheory.CompanionTheory.MuC

theorem isClosed_hermS_val (D : D7) (p : ℕ) (e : AE D) :
    IsClosed ((hermS D p e : AddSubgroup (hermA D p)) : Set (hermA D p)) := by
  obtain ⟨_, _, _, _, _⟩ := Formalism.IndefR.Eqv.ae_facts D
  have hc : Continuous fun x : hermA D p => e • (x : Formalism.IndefR.Datum.Mx D p p) :=
    (continuous_const_smul e).comp continuous_subtype_val
  exact isClosed_eq hc continuous_subtype_val



theorem hermS_facts : ∀ (D : D7) (p : ℕ) (e : AE D), LocallyCompactSpace (hermS D p e) ∧ T2Space (hermS D p e) ∧
    SecondCountableTopology (hermS D p e) ∧ BorelSpace (hermS D p e) ∧ IsTopologicalAddGroup (hermS D p e) := by
  intro D p e
  obtain ⟨_, _, _, _, _⟩ := Formalism.IndefR.Eqv.ae_facts D
  have hS := isClosed_hermS_val D p e
  have hA : IsClosed ((hermA D p : AddSubgroup (Formalism.IndefR.Datum.Mx D p p)) : Set (Formalism.IndefR.Datum.Mx D p p)) :=
    GlobalTheory.CompanionTheory.HermVol.isClosed_hermA
  haveI : LocallyCompactSpace (Formalism.IndefR.Datum.Mx D p p) :=
    show LocallyCompactSpace (Fin p → Fin p → AE D) from inferInstance
  haveI : SecondCountableTopology (Formalism.IndefR.Datum.Mx D p p) :=
    show SecondCountableTopology (Fin p → Fin p → AE D) from inferInstance
  haveI : BorelSpace (Formalism.IndefR.Datum.Mx D p p) := by
    first
    | exact ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D p) := by
    first
    | exact Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : SecondCountableTopology (hermS D p e) := by
    first
    | exact Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : LocallyCompactSpace (hermA D p) := hA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  exact ⟨hS.isClosedEmbedding_subtypeVal.locallyCompactSpace, inferInstance, inferInstance, inferInstance,
    inferInstance⟩

end GlobalTheory.CompanionTheory.MuC
