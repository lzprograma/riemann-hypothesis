module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Avac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open GlobalTheory.Doubling (absE)

def I0 {n : ℕ} (i₀ : Fin n) : Set (Fin n ⊕ Fin n) := {Sum.inl i₀, Sum.inr i₀}


variable (F E) in
structure IsQ {n : ℕ} (i₀ : Fin n) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (lam : (AE F E)ˣ) : Prop where
  off : ∀ a b, a ∉ I0 i₀ → b ∉ I0 i₀ → M a b = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) a b
  col : ∀ a, M a (Sum.inl i₀) = if a = Sum.inl i₀ then (lam : AE F E) else 0
  row : ∀ b, b ≠ Sum.inr i₀ → M (Sum.inr i₀) b = 0

end PositivityTheory.SiegelWeilFormula.Avac

end
