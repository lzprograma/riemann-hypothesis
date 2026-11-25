module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLocalIntegralPointsMemOpenSubgroupDefi

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.eventually_localIntegralPoints_mem_openSubgroup_definiteUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (L : Subgroup (finU (E := E) (n := n))), IsOpen (L : Set (finU (E := E) (n := n))) → ∀ᶠ w in cofinite, ∀ x : UA E n, x ∈ locU n w → cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ h : x ∈ finU (E := E) (n := n), (⟨x, h⟩ : finU (E := E) (n := n)) ∈ L := by
  first | exact @GlobalTheory.BCT.GlobLev.eventually_locU_mem
