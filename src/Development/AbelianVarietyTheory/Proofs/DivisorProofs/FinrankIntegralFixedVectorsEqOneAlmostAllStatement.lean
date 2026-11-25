module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIntegralFixedVectorsEqOneAlmostAll

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.finrank_integral_fixed_vectors_eq_one_almost_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ σ : ∀ w : Pl E, SmIrr (UL n w), (∀ w, IsCompU π w (σ w)) → ∀ᶠ w in cofinite, Module.finrank ℂ (fixed (σ w).ρ (KL n w)) = 1 := by
  first | exact @GlobalTheory.BCT.SphLine.finrank_fixed_KL_eq_one
