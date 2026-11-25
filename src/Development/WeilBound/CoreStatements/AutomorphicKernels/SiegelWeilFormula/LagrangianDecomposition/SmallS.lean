module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SmallSC
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SubSplit
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramSkewHermitianSignature
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationDarbouxChangeIntertwine
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SubSplitOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxChangeRealisedCompAndReindex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F : Type} [Field F] [NumberField F]

theorem sliceL_mem (hF : SliceFacts) {κ' κ'' : Type} [Fintype κ'] [Fintype κ''] {Ψ : (κ' ⊕ κ'' → AF F) → ℂ}
    (hΨ : Ψ ∈ schA F (κ' ⊕ κ'')) : (fun x'' : κ'' → AF F => Ψ (Sum.elim 0 x'')) ∈ schA F κ'' := by
  have h1 := GlobalTheory.TowU.RealComp.reix_mem_schA (Equiv.sumComm κ'' κ') hΨ
  have h2 := (hF F κ'' κ').1 _ h1
  convert h2 using 1
  funext x''
  simp only [slice0, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.TowU.RealComp.reix_apply]
  congr 1
  funext i
  rcases i with i | i <;> rfl

end PositivityTheory.SiegelWeilFormula.Ald

end
