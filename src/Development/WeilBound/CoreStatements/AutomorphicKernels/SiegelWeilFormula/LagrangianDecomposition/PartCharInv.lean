module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SDarb
public import Development.AbelianVarietyTheory.Definitions.Divisors.DblActId

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

def PartCharInv : Prop := ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) →
  ∀ (κ' κ'' : Type) [Fintype κ'] [Fintype κ''] (l : ((κ' ⊕ κ'' → AF F) → ℂ) →ₗ[ℂ] ℂ),
    l ∈ (adeleClass F).adm (κ' ⊕ κ'') →
    (∀ (y : κ'' → AF F), ∀ Ψ ∈ schA F (κ' ⊕ κ''), l (fun x => ψ ((x ∘ Sum.inr) ⬝ᵥ y) * Ψ x) = l Ψ) →
    ∀ Ψ ∈ schA F (κ' ⊕ κ''), (∀ x' : κ' → AF F, Ψ (Sum.elim x' 0) = 0) → l Ψ = 0

end PositivityTheory.SiegelWeilFormula.Ald

end
