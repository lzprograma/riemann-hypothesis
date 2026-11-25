module

public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RestrictGaloisConjugate
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.MemRangeResIff
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RangeRes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SemisimpleIsoOfTraceEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SemisimpleRestrictionToNormalSubgroup
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.EqOneOrEqOfKer
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Connected.Separation

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ImportsMore, PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.GaloisRepPatchingInfiniteFamily

-- ===== clump member: PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ImportsMore =====
-- clump-header: {"m": "PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ImportsMore", "h": "module\n\npublic import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SemisimpleRestrictionToNormalSubgroup\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.FieldTheory.Galois.Profinite\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Connected.Separation\npublic import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RestrictGaloisConjugate\npublic import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.MemRangeResIff\npublic import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.EqOneOrEqOfKer\npublic import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RangeRes\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic\npublic import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SemisimpleIsoOfTraceEq\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal

namespace GlobalTheory.CMPatch

theorem res_injective (F Ω E : Type) [Field F] [Field Ω] [Algebra F Ω] [Field E] [Algebra F E] [Algebra E Ω]
    [IsScalarTower F E Ω] : Function.Injective (res F Ω E) := by
  intro a b h
  ext x
  have := congrArg (fun σ : G F Ω => σ x) h
  simpa using this

theorem main : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (S : Set (QCM F Ω)), S.Infinite → ∀ r : ∀ Q : ↥S, G ↥Q.1.K Ω →* GL (Fin a) (Qbar l), (∀ Q, Continuous (r Q) ∧ IsSSRep (r Q) ∧ AttRes π ι ↥Q.1.K (r Q)) → ∃ ρ : G F Ω →* GL (Fin a) (Qbar l), Continuous ρ ∧ IsSSRep ρ ∧ ∀ᶠ Q : ↥S in Filter.cofinite, IsSSRep (ρ.comp (res F Ω ↥Q.1.K)) ∧ RepIso (r Q) (ρ.comp (res F Ω ↥Q.1.K)) := by
  intro F Ω _ _ _ _ _ _ l _ ι a π S hS r hr
  classical
  have : Infinite ↥S := hS.to_subtype
  have : Algebra.IsIntegral F Ω := (IsAlgClosure.isAlgebraic (R := F) (K := Ω)).isIntegral
  obtain ⟨η, hηinj, hη⟩ := _root_.GlobalTheory.RealGal.SignChar.main F Ω
  let e : ∀ Q : ↥S, G ↥Q.1.K Ω ≃* (η Q.1).ker := fun Q =>
    (MonoidHom.ofInjective (res_injective F Ω ↥Q.1.K)).trans (MulEquiv.subgroupCongr (hη Q.1).1.symm)
  have he : ∀ Q : ↥S, ∀ (s : G ↥Q.1.K Ω), ((e Q s : (η Q.1).ker) : G F Ω) = res F Ω ↥Q.1.K s := fun Q s => rfl
  have hes : ∀ Q : ↥S, ∀ (h : (η Q.1).ker), res F Ω ↥Q.1.K ((e Q).symm h) = h := by
    intro Q h; rw [← he, MulEquiv.apply_symm_apply]
  let r' : ∀ Q : ↥S, (η Q.1).ker →* GL (Fin a) (Qbar l) := fun Q => (r Q).comp (e Q).symm.toMonoidHom
  have hr' : ∀ Q : ↥S, ∀ (h : (η Q.1).ker), r' Q h = r Q ((e Q).symm h) := fun Q h => rfl
  have hcont : ∀ Q : ↥S, Continuous (r' Q) := by
    intro Q
    have : CompactSpace (G ↥Q.1.K Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[↥Q.1.K] Ω))
    have hc : Continuous (e Q) := (UpperTheory.V.Af.continuous_restrictScalarsHom F ↥Q.1.K Ω).subtype_mk _
    let hm := hc.homeoOfEquivCompactToT2 (f := (e Q).toEquiv)
    exact (hr Q).1.comp hm.symm.continuous
  have hss : ∀ Q : ↥S, IsSSRep (r' Q) := by
    intro Q
    refine UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a (r Q) (e Q).symm.toMonoidHom ?_ (hr Q).2.1
    rw [MonoidHom.range_eq_top.mpr (e Q).symm.surjective]
    infer_instance
  obtain ⟨ρ, hρc, hρs, hev⟩ := GlobalTheory.IndexTwoPatch.main (G F Ω) (Qbar l) a ↥S (fun Q => η Q.1)
    (hηinj.comp Subtype.val_injective) (fun Q => (hη Q.1).2) r' (fun Q => ⟨hcont Q, hss Q⟩)
    (by
      intro Q g h h' hh
      rw [hr', hr']
      exact _root_.GlobalTheory.RealGal.trace_conj_of_attRes F Ω ↥Q.1.K Q.1.two l ι a π (r Q) (hr Q).1 (hr Q).2.1 (hr Q).2.2 g
        ((e Q).symm h) ((e Q).symm h') (by rw [hes, hes]; exact hh))
    (by
      intro Q Q' h h' hh
      rw [hr', hr']
      exact _root_.GlobalTheory.RealGalCompat.trace_eq F Ω Q.1 Q'.1 l ι a π (r Q) (r Q') (hr Q).1 (hr Q').1 (hr Q).2.1 (hr Q').2.1
        (hr Q).2.2 (hr Q').2.2 _ _ (by rw [hes, hes]; exact hh))
  refine ⟨ρ, hρc, hρs, hev.mono fun Q hQ => ?_⟩
  have hres : IsSSRep (ρ.comp (res F Ω ↥Q.1.K)) := by
    refine UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a ρ (res F Ω ↥Q.1.K) ?_ hρs
    rw [← (hη Q.1).1]
    infer_instance
  refine ⟨hres, _root_.GlobalTheory.TraceConj.main (G ↥Q.1.K Ω) (Qbar l) a (r Q) (ρ.comp (res F Ω ↥Q.1.K)) (hr Q).2.1 hres fun s => ?_⟩
  have h1 := hQ (e Q s)
  rw [hr', MulEquiv.symm_apply_apply, he] at h1
  exact h1.symm

end GlobalTheory.CMPatch
end -- clump:auto
end -- clump:auto
-- ===== end clump member: PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ImportsMore =====

-- ===== clump member: PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.GaloisRepPatchingInfiniteFamily =====
-- clump-header: {"m": "PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.GaloisRepPatchingInfiniteFamily", "h": "module\n\npublic import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ImportsMore\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal

theorem _root_.GlobalTheory.T.galois_rep_patching_infinite_family : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (S : Set (QCM F Ω)), S.Infinite → ∀ r : ∀ Q : ↥S, G ↥Q.1.K Ω →* GL (Fin a) (Qbar l), (∀ Q, Continuous (r Q) ∧ IsSSRep (r Q) ∧ AttRes π ι ↥Q.1.K (r Q)) → ∃ ρ : G F Ω →* GL (Fin a) (Qbar l), Continuous ρ ∧ IsSSRep ρ ∧ ∀ᶠ Q : ↥S in Filter.cofinite, IsSSRep (ρ.comp (res F Ω ↥Q.1.K)) ∧ RepIso (r Q) (ρ.comp (res F Ω ↥Q.1.K)) := by
  first | exact @GlobalTheory.CMPatch.main
end -- clump:auto
end -- clump:auto
-- ===== end clump member: PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.GaloisRepPatchingInfiniteFamily =====
