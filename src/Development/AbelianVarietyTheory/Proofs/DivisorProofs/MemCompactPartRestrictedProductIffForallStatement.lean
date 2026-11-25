module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartRestrictedProductIffForall

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct


theorem _root_.GlobalTheory.T.mem_compactPart_restrictedProduct_iff_forall : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (T : Subgroup X) (Tv : ∀ v, Subgroup (Y v)), (∀ x, x ∈ T ↔ ∀ v, pf v x ∈ Tv v) → (∀ v, ∀ a ∈ Tv v, ∀ b ∈ Tv v, a * b = b * a) → ∀ x, x ∈ cptPart T ↔ ∀ v, pf v x ∈ cptPart (Tv v) := by
  first | exact @GlobalTheory.CptPartRestr.mem_cptPart_iff_forall
