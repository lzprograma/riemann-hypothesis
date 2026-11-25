module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramKernelSignNonsplitBaseChangeEq

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.gramKernelSign_nonsplit_baseChange_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (H A : Matrix (Fin n) (Fin n) E), (-1 : ℂ) ^ ordL (gramOn (cj w) (H.map (algebraMap E (w.adicCompletion E))) (LinearMap.ker (Matrix.toLin' (A.map (algebraMap E (w.adicCompletion E)))))).det = (-1) ^ ordL (algebraMap E (w.adicCompletion E) (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H (LinearMap.ker (Matrix.toLin' A))).det) := by
  first | exact @GlobalTheory.UnitaryClasses.BaseChangeSign.main
