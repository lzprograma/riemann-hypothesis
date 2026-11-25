module

import all Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatakeOfIsLocComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportOfPrincipalSeriesSubquotient
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Unlinked
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel

private theorem val_unif (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    valuation k (unif k : k) = uniformizer k := by
  apply _root_.val_unif <;> assumption

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.sphUnl :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.SphUnl := by
  intro K _ _ _ n hn π v B hB
  obtain ⟨⟨s₀, hs₀⟩, huniq, htor, hunr, -⟩ := suppFacts K n hn π v
  refine ⟨(htor s₀ hs₀).1.2 fun y hy => ?_, fun s hs => ?_⟩
  · obtain ⟨μ, hμ, rfl⟩ := hunr s₀ B hs₀ hB y hy
    rfl
  · obtain ⟨σ, hσ, -⟩ := id hs
    obtain ⟨α, hα, hS⟩ := GlobalTheory.LFun.SphComp.hasSatake_of_isLocComp π ((CG.hasSat_mk π v B).1 hB) hσ
    haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective
    have h := GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries (v.adicCompletion K) n (fun i => unrChar _ (α i))
      (fun i => isSmoothChar_of_isUnram (isUnram_unrChar _ (α i))) ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩ hS.2.2
    have key : ∀ ξ ∈ chars s, ξ (unif _) ∈ B := by
      rintro ξ ⟨hξ, hm⟩
      rw [huniq s _ hs ⟨σ, hσ, h⟩] at hm
      obtain ⟨i, hi, e⟩ := Multiset.mem_map.1 hm
      rw [← IrrGL.ofChar_inj.1 e, unrChar_uniformizer _ _ (val_unif _), ← hα]
      exact Multiset.mem_map_of_mem _ hi
    intro ξ hξ ξ' hξ' _ e
    refine UpperTheory.ConvolutionTheory.Sph.unlinked K n hn π v B hB _ (key ξ hξ) _ (key ξ' hξ') ?_
    rw [← e, MonoidHom.mul_apply, MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel_right]
