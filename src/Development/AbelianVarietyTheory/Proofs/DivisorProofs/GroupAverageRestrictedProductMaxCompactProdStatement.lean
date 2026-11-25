module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupAverageRestrictedProductMaxCompactProd

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct


theorem _root_.GlobalTheory.T.groupAverage_restrictedProduct_maxCompact_prod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (u : ∀ v, K v → ℂ), (∀ v, (rStab (u v)).index ≠ 0) → (∀ᶠ v in cofinite, ∀ k, u v k = 1) → avg (fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => ∏ᶠ v, u v ⟨pf v k, Subgroup.mem_iInf.1 k.2 v⟩) = ∏ᶠ v, avg (u v) := by
  first | exact @GlobalTheory.AvgRestr.avg_restr_prod
