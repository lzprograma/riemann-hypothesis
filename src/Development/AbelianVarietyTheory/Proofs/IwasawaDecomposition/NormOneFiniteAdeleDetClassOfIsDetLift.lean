module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H90USurjective
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Development.AbelianVarietyTheory.Definitions.Foundations.ValuedAlgebraMapEqOne
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetMulConjDet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H90RangeEqNormOneOfIsQuad
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1

namespace GlobalTheory.Mem.Col2.FullDt

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def detU : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H) →* U1 (host_cmData R H).sig :=
  (Matrix.GeneralLinearGroup.det.comp (Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)).subtype).codRestrict _ fun x =>
    Units.ext (DetLift.det_mul_conj_det _ _ x.2)

def u1Dt (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H) →* DtQ H SQ :=
  (normOneIdeleToFinerDeterminantClass H SQ (host_cmData R H).sig (fun x => bridge_star_holds R H x) (afIso H.F H.E)
    (afIso_tmul_one H.F H.E) (mem_rInt_iff H.F H.E)).comp (detU H)

theorem normOneFiniteAdeleDetClass_of_isDetLift (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) (a : GlobalTheory.Mem.Chr.Ideles H.E)
    (ha : IsDetLift (host_cmData R H) x.1 a) : u1Dt H SQ x = QuotientGroup.mk a := by
  have e : detU H x = ⟨h90 (host_cmData R H).sig (finAf H.F H.E a), by
      rw [ha]; exact (detU H x).2⟩ := Subtype.ext ha.symm
  show normOneIdeleToFinerDeterminantClass H SQ _ _ _ _ _ (detU H x) = _
  rw [e]
  exact normOneIdeleToFinerDeterminantClass_eq_mk H SQ _ _ _ _ _ _ _ _ (afIso_finAf H.F H.E a).symm

theorem exists_lift (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) : ∃ a : GlobalTheory.Mem.Chr.Ideles H.E, IsDetLift (host_cmData R H) x.1 a :=
  DetLift.exists_isDetLift R H 1 x.1 x.2

theorem exists_of_idele (a : GlobalTheory.Mem.Chr.Ideles H.E) : ∃ x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H), IsDetLift (host_cmData R H) x.1 a := by
  have hu : h90 (host_cmData R H).sig (finAf H.F H.E a) ∈ U1 (host_cmData R H).sig :=
    (DetClass.exists_detClass R H (host_cmData R H).sig (fun x => bridge_star_holds R H x) (afIso H.F H.E)
      (afIso_tmul_one H.F H.E) (mem_rInt_iff H.F H.E)).1.le ⟨_, rfl⟩
  refine ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 1) (h90 (host_cmData R H).sig (finAf H.F H.E a)), ?_⟩, ?_⟩
  · show Formalism.UG.cT _ _ * _ * _ = _
    have hz := congrArg Units.val (show (h90 (host_cmData R H).sig (finAf H.F H.E a)) * conjId (host_cmData R H).sig (h90 (host_cmData R H).sig (finAf H.F H.E a)) = 1 from hu)
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [Formalism.UG.cT, Matrix.mul_apply]
    exact (mul_comm _ _).trans hz
  · exact Units.ext (by simp)

theorem normOneFiniteAdeleDetClass_surjective (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) : Function.Surjective (u1Dt H SQ) := fun t => by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective t
  obtain ⟨x, hx⟩ := exists_of_idele H a
  exact ⟨x, normOneFiniteAdeleDetClass_of_isDetLift H SQ x a hx⟩

end GlobalTheory.Mem.Col2.FullDt

end
