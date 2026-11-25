module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.WeilBound.ThetaLifts.LatticeBasics.Hypotheses2

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil

instance firstCountable_GR (n : ℕ) : FirstCountableTopology (GR n) := by
  haveI : FirstCountableTopology (M2 n) :=
    inferInstanceAs (FirstCountableTopology (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ))
  haveI : FirstCountableTopology (M2 n)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.firstCountableTopology
  haveI : FirstCountableTopology (GL (Fin n ⊕ Fin n) ℂ) := Units.isEmbedding_embedProduct.firstCountableTopology
  exact Topology.IsEmbedding.subtypeVal.firstCountableTopology

end PositivityTheory.SiegelWeilFormula.Kdil

end
