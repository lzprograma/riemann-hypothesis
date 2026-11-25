module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisOpenSubgroupLocalUnits
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published

noncomputable section

namespace GlobalTheory.ArtinInvCont

theorem absoluteGaloisAbelianization_t2Space (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] :
    T2Space (GlobalTheory.HeckeGal.Gab E Ω) := by
  unfold GlobalTheory.HeckeGal.Gab TopologicalAbelianization
  haveI : IsClosed (((commutator (G E Ω)).topologicalClosure : Subgroup (G E Ω)) : Set (G E Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  infer_instance

theorem continuous_localIdele' (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    Continuous (Neutral.B1.localIdele E v) := by
  apply GlobalTheory.CompanionTheory.InertOpen.continuous_localIdele'

theorem isCompact_valOne (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    IsCompact {x : (w.adicCompletion E)ˣ | Valued.v (x : w.adicCompletion E) = 1} :=
  GlobalTheory.CompanionTheory.InertOpen.isCompact_setOf_isUnitAt w

theorem continuous_inv_on_ine : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω) (a : Weil h →* (w.adicCompletion E)ˣ), GlobalTheory.HeckeGal.IsGlobalArtin art → (∀ σ, ord (w.adicCompletion E) (a σ) = -deg σ) → (∀ σ : Weil h, art (Neutral.B1.localIdele E w (a σ)) = GlobalTheory.HeckeGal.toAb E Ω σ) → Continuous fun σ : Ine (F := E) A => a (ineIncl h σ) := by
  intro E Ω _ _ _ _ _ A w h art a ha hord hart
  haveI := absoluteGaloisAbelianization_t2Space E Ω
  let K : Set (w.adicCompletion E)ˣ := {x | Valued.v (x : w.adicCompletion E) = 1}
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_valOne E w)
  let f : K → GlobalTheory.HeckeGal.Gab E Ω := fun x => art (Neutral.B1.localIdele E w x.1)
  have hf : Continuous f :=
    (ha.quot.continuous.comp (continuous_localIdele' E w)).comp continuous_subtype_val
  have hinj : Function.Injective f := fun x y hxy =>
    Subtype.ext (GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' E Ω art ha w hxy)
  have hemb := hf.isClosedEmbedding hinj
  have hmem : ∀ σ : Ine (F := E) A, a (ineIncl h σ) ∈ K := by
    intro σ
    have hd : deg (ineIncl h σ) = 0 := by
      rw [deg_eq (a := 0) (b := 0) (actsAs_zero_iff.mpr σ.2)]
      simp
    have ho := hord (ineIncl h σ)
    rw [hd, neg_zero, GlobalTheory.SmGL.SphCompletion.ord_completion, neg_eq_zero] at ho
    show Valued.v ((a (ineIncl h σ) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1
    rw [← WithZero.exp_log (by simp : Valued.v ((a (ineIncl h σ) : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≠ 0),
      ho, WithZero.exp_zero]
  let g : Ine (F := E) A → K := fun σ => ⟨a (ineIncl h σ), hmem σ⟩
  have hg : Continuous g := by
    rw [hemb.isInducing.continuous_iff]
    have e : f ∘ g = fun σ : Ine (F := E) A => GlobalTheory.HeckeGal.toAb E Ω (σ : G E Ω) :=
      funext fun σ => hart (ineIncl h σ)
    rw [e]
    exact continuous_quot_mk.comp continuous_subtype_val
  exact continuous_subtype_val.comp hg

end GlobalTheory.ArtinInvCont
