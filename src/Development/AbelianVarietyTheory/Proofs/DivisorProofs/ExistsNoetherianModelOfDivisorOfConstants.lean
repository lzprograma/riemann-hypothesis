module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocIndEtaleIsDomainIsIntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianNormalLocalApprox
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomain
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RingHom.EssFiniteType
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open IsLocalRing Polynomial

namespace GlobalTheory.VertUnitsNoeth

open GlobalTheory.NormalApprox

theorem essFiniteType_loc {T : Type} [CommRing T] [IsDomain T] [IsIntegrallyClosed T] (S : Finset T) :
    Algebra.EssFiniteType ℤ (loc S) := by
  haveI : Module.Finite (gen S) (integralClosure (gen S) (FractionRing (gen S))) :=
    GlobalTheory.finite_integralClosure_of_essFiniteType_int (gen S)
  haveI : Algebra.EssFiniteType ℤ (gen S) := Algebra.EssFiniteType.of_finiteType ℤ _
  haveI : Algebra.EssFiniteType (gen S) (integralClosure (gen S) (FractionRing (gen S))) := by
    set_option synthInstance.maxHeartbeats 200000 in
      infer_instance
  set_option synthInstance.maxHeartbeats 200000 in
    haveI h1 : Algebra.EssFiniteType ℤ (integralClosure (gen S) (FractionRing (gen S))) :=
      Algebra.EssFiniteType.comp ℤ (gen S) _
  have h2 : (algebraMap ℤ (norm S)).EssFiniteType := by
    have e : algebraMap ℤ (norm S) =
        (normEquiv S).symm.toRingHom.comp (algebraMap ℤ (integralClosure (gen S) (FractionRing (gen S)))) :=
      RingHom.ext_int _ _
    rw [e]
    exact RingHom.EssFiniteType.comp (RingHom.essFiniteType_algebraMap.2 h1)
      (RingHom.FiniteType.essFiniteType (RingHom.FiniteType.of_surjective (normEquiv S).symm.toRingHom (normEquiv S).symm.surjective))
  haveI : Algebra.EssFiniteType ℤ (norm S) := RingHom.essFiniteType_algebraMap.1 h2
  haveI := loc_isLocalization S
  haveI : Algebra.EssFiniteType (norm S) (loc S) := Algebra.EssFiniteType.of_isLocalization _ (unitsIn S)
  exact Algebra.EssFiniteType.comp ℤ (norm S) (loc S)

end GlobalTheory.VertUnitsNoeth

namespace GlobalTheory.VertUnitsNoeth

open GlobalTheory.NormalApprox TensorProduct

end GlobalTheory.VertUnitsNoeth

namespace GlobalTheory.VertUnitsNoeth

open GlobalTheory.NormalApprox

theorem mem_originIdeal_iff' {T : Type} [CommRing T] [IsLocalRing T] (f : Polynomial T) :
    f ∈ GlobalTheory.KeyOriginCut.originIdeal T ↔ f.coeff 0 ∈ maximalIdeal T := by
  constructor
  · intro hf
    have hle : GlobalTheory.KeyOriginCut.originIdeal T ≤ (maximalIdeal T).comap (Polynomial.constantCoeff (R := T)) := by
      refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap]
        intro a ha
        simpa using ha
      · rw [Ideal.span_le]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        simp
    have := hle hf
    simpa [Polynomial.coeff_zero_eq_eval_zero] using this
  · intro hf
    have h1 : Polynomial.C (f.coeff 0) ∈ GlobalTheory.KeyOriginCut.originIdeal T :=
      Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)
    have h2 : f - Polynomial.C (f.coeff 0) ∈ GlobalTheory.KeyOriginCut.originIdeal T :=
      Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr (Polynomial.X_dvd_sub_C))
    simpa using Ideal.add_mem _ h1 h2

theorem comap_originIdeal' (A T : Type) [CommRing A] [IsLocalRing A] [CommRing T] [IsLocalRing T]
    (i : A →+* T) [IsLocalHom i] :
    (GlobalTheory.KeyOriginCut.originIdeal T).comap (Polynomial.mapRingHom i) = GlobalTheory.KeyOriginCut.originIdeal A := by
  ext f
  rw [Ideal.mem_comap, mem_originIdeal_iff', mem_originIdeal_iff', Polynomial.coe_mapRingHom,
    Polynomial.coeff_map, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    isUnit_map_iff]

theorem isIntegrallyClosed_of_absIntClosed' (T : Type) [CommRing T] [IsDomain T]
    (hT : GlobalTheory.LocAcyc.AbsIntClosed T) : IsIntegrallyClosed T := by
  apply _root_.GlobalTheory.LocIndEtale.isIntegrallyClosed_of_forall_monic_root <;> assumption

end GlobalTheory.VertUnitsNoeth
