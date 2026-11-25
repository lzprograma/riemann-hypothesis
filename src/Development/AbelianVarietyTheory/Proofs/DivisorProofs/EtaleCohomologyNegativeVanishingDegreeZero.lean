module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeZeroSectionClassProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem etale_cohomology_vanishing_negative_degree_zero : A9 := by
  intro R _ F
  refine ⟨?_, ?_⟩
  · intro E n hn
    have hz : ∀ α : Cochain ((chains R).obj E) (res R F) n, α = 0 := by
      intro α
      apply (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.1 α 0
      intro p s h U x
      have hs : s < 0 := by omega
      haveI := ((_root_.GlobalTheory.EtC.resSec R F U).2.2.2 s hs)
      exact Subsingleton.elim _ _
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := a.mk_surjective
    obtain ⟨b, rfl⟩ := b.mk_surjective
    have : a = b := Cocycle.ext (by rw [hz a.1, hz b.1])
    rw [this]
  · let f : ∀ X : Scheme.{0}, Sec F X →+ H R (sch.obj X) F 0 := fun X =>
      AddMonoidHom.mk' (secClass F (X := X)) (_root_.GlobalTheory.EtC.secClass_props R F X).2.2.1
    refine ⟨fun X => AddEquiv.ofBijective (f X) (_root_.GlobalTheory.EtC.secClass_props R F X).2.1, ?_, ?_⟩
    · intro Y X g s
      exact (_root_.GlobalTheory.EtC.secClass_props R F X).2.2.2.1 g s
    · intro X s
      obtain ⟨α, hα⟩ := (secClass F s).mk_surjective
      exact ⟨α, hα, ((_root_.GlobalTheory.EtC.secClass_props R F X).1 s α).2 hα⟩

end GlobalTheory.EtC
