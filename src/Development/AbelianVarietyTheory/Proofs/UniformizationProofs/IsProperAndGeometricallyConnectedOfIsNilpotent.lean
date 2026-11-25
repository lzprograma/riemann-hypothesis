module

import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeometricallyConnectedOfIsPullback
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.NilProper

theorem isSeparated_of_comp_surjective {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S)
    [Surjective j] [UniversallyClosed j] [IsSeparated (j ≫ f)] : IsSeparated f := by
  apply (config := { allowSynthFailures := true }) GlobalTheory.SemiAbelianDescent.isSeparated_of_comp <;> assumption

theorem surjective_specMap_mk (A : Type) [CommRing A] (J : Ideal A) (hJ : IsNilpotent J) :
    Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) := by
  obtain ⟨n, hn⟩ := hJ
  have hle : J ≤ nilradical A := fun x hx ↦ by
    rw [mem_nilradical]
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hx n
    rwa [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  exact ⟨(PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hle).2⟩

theorem isProper_and_geometricallyConnected_of_isNilpotent :
    ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (Y : Over (Spec (CommRingCat.of A))) [LocallyOfFiniteType Y.hom], (IsProper (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) → IsProper Y.hom) ∧ (GeometricallyConnected (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) → GeometricallyConnected Y.hom) := by
  intro A _ J hJ Y _
  have hsq : Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    surjective_specMap_mk A J hJ
  have hci : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨fun hP ↦ ?_, fun hG ↦ ?_⟩
  · have hcomp : IsProper (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
        ≫ Y.hom) := by
      rw [pullback.condition]
      infer_instance
    have : IsSeparated Y.hom :=
      isSeparated_of_comp_surjective (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) Y.hom
    have : UniversallyClosed Y.hom :=
      UniversallyClosed.of_comp_surjective (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) Y.hom
    exact { toIsSeparated := ‹_›, toUniversallyClosed := ‹_›, toLocallyOfFiniteType := ‹_› }
  · rw [geometricallyConnected_iff] at hG ⊢
    intro K _ y Z fst snd h
    obtain ⟨φ, rfl⟩ := Spec.map_surjective y
    have hker : ∀ x ∈ J, φ.hom x = 0 := by
      obtain ⟨n, hn⟩ := hJ
      intro x hx
      have hx' : x ^ n = 0 := by
        have := Ideal.pow_mem_pow hx n
        rwa [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
      exact (IsNilpotent.map ⟨n, hx'⟩ φ.hom).eq_zero
    let ψ := Ideal.Quotient.lift J φ.hom hker
    have hφ : φ = CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ CommRingCat.ofHom ψ := by
      ext x
      simp [ψ]
    rw [hφ, Spec.map_comp] at h
    let p : Z ⟶ pullback Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
      pullback.lift fst (snd ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [h.w, Category.assoc])
    apply hG (Spec.map (CommRingCat.ofHom ψ)) p snd
    have e : p ≫ pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) = fst :=
      pullback.lift_fst _ _ _
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [e]
    exact h

end GlobalTheory.NilProper
