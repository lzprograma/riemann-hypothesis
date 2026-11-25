module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet
public import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasPhiExistsExtAndUnique
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ValuationFormPsiBalancedSymmetricPeriodForm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEqSmulOne
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt

namespace GlobalTheory.ShortPhi

theorem exists_shortBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (φ : ℝ), HasPhi y φ → ∀ (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ → ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q → ∃ r : ℕ, r ≤ Module.finrank ℚ E * Dw.q ∧ ShortBasis Q r ((|(discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) / (2 * Module.finrank ℚ E) * (r : ℝ) ^ 3 * φ) (2 * Real.sqrt r) := by
  intro E _ _ _ H Dw l Xo c T io y φ hφ C P ϖ hϖ Q hQ
  let := H.starRing
  let := io.toAlgebra
  obtain ⟨Q', β, hQ', h0, hβ, hβ2, -⟩ :=
    GlobalTheory.ValForm.main E H T.V C.I.G P ϖ hϖ (IsCMField.complexConj E : E → E) fun _ => rfl
  obtain rfl : Q = Q' := funext fun χ => QForm.QVal_unique hϖ P.D (hQ χ) (hQ' χ)
  have hφ' : HasPhi y (Formalism.MainNotions.ModuliIntegralCharts.phiC _ β) := ⟨C.I.G, C.I.t', C.I.m1, C.I.m2, P, ϖ, Q, β, hϖ, hQ, h0, hβ2, rfl⟩
  have hnn := hφ.nonneg
  obtain rfl : φ = Formalism.MainNotions.ModuliIntegralCharts.phiC _ β := (hasPhi_exists_ext_and_unique E H Dw l Xo c).2 T io y _ _ hφ hφ'
  obtain ⟨ρ, hρ, -, hq⟩ := GlobalTheory.ToricRank.rank_le_signature E H Dw l Xo T.V C.I.G P C.I.t' C.I.m2 y.1.x C.I.m1
    inferInstance
  have hrt : IsCMField.complexConj E (H.rt : E) = -(H.rt : E) := by
    rw [← H.bar_eq, HostModel.bar_rt]; simp
  have hw : (H.w0 : E) + IsCMField.complexConj E (H.w0 : E) = 1 := by
    have h2 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
      simpa only [map_mul, map_add (f := _), map_one, map_ofNat] using congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
    have h3 := congrArg (IsCMField.complexConj E) h2
    rw [map_mul, map_add (f := _), map_one, map_ofNat, hrt] at h3
    linear_combination (h2 + h3) / 2
  have hne : ∃ z : E, IsCMField.complexConj E z ≠ z := by
    by_contra! h
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h)
  have hpos := QForm.gram_posDef hϖ P.D hQ (Module.finBasis ℤ P.D.toPre.X)
  obtain ⟨b, h1, h2⟩ := gram_form_phi_holds E (IsCMField.complexConj E : E → E)
    (fun ψ z => IsCMField.complexEmbedding_complexConj E ψ z) hne H.w0 hw P.D.toPre.X β
    ⟨_, inferInstance, Module.finBasis ℤ P.D.toPre.X, by simpa only [hβ] using hpos⟩
  refine ⟨Module.finrank ℤ P.D.toPre.X, ?_, by positivity, b, fun j => ?_, fun j z => ?_⟩
  · rw [hρ]
    exact Nat.mul_le_mul (Nat.mul_div_le _ _) hq
  · have := h1 j
    rwa [hβ2, mul_div_cancel_left₀ _ two_ne_zero] at this
  · have := h2 j z
    rwa [hβ2, mul_div_cancel_left₀ _ two_ne_zero, hβ] at this

end GlobalTheory.ShortPhi
