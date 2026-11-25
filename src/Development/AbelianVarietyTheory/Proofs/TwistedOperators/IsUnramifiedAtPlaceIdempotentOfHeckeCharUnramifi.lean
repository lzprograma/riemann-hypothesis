module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Links Formalism.L2.Host GlobalTheory.WeilParts
open scoped TensorProduct

namespace GlobalTheory.UnramOver

theorem map_eq_one_of_supp {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) {e x : R}
    (hx : e * (x - 1) = x - 1) (he : f e = 0) : f x = 1 := by
  have h := congrArg f hx
  rw [map_mul, map_sub, map_one, he, zero_mul] at h
  exact sub_eq_zero.mp h.symm

theorem val_eq_one_of_unit {R K Γ : Type} [CommRing R] [CommRing K] [LinearOrderedCommMonoidWithZero Γ]
    (w : Valuation K Γ) (f : R →+* K) (x : Rˣ) (a : w (f x) ≤ 1) (b : w (f (x⁻¹ : Rˣ)) ≤ 1) : w (f x) = 1 := by

  have hprod : w (f x) * w (f (x⁻¹ : Rˣ)) = 1 := by
    rw [← Valuation.map_mul, ← map_mul f, Units.mul_inv, map_one f, Valuation.map_one]
  refine le_antisymm a ?_
  calc (1 : Γ) = w (f x) * w (f (x⁻¹ : Rˣ)) := hprod.symm
    _ ≤ w (f x) := mul_le_of_le_one_right' b

theorem unramAt_of_unrAt : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ →
    ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    (∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v → χ.UnrAt P) → UnramAt ε c := by
  classical
  intro D c χ hce v ε hε hunr x hsupp hxi hxii
  obtain ⟨ι, hι1, hint, happ⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hmain⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι hι1 hint
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι hι1 hint happ) c χ hce
  obtain ⟨α, rfl, -, hα0⟩ := hε

  have hinf0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E))
      (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul]
    exact TensorProduct.zero_tmul _ _
  have hfin : finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = α ⊗ₜ[D.host.F] (1 : D.host.E) := by
    show (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = _
    rw [Algebra.TensorProduct.map_tmul]
    rfl

  have hx1 : infPart D (x : AE D) = 1 := map_eq_one_of_supp (infPart D) hsupp hinf0

  have hval : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (x : AE D)) P) = 1 := fun P =>
    val_eq_one_of_unit Valued.v ((GlobalTheory.CharLocProd.evalAt P).comp (ι.toRingHom.comp (finPart D))) x
      ((hint _).1 hxi P) ((hint _).1 hxii P)

  have hoff : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) ≠ v →
      ι (finPart D (x : AE D)) P = 1 := by
    intro P hP
    refine map_eq_one_of_supp ((GlobalTheory.CharLocProd.evalAt P).comp (ι.toRingHom.comp (finPart D))) hsupp ?_
    show ι (finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α))) P = 0
    rw [hfin]
    have hα : α (P.under (𝓞 D.host.F)) = 0 := hα0 _ hP
    apply GlobalTheory.PlaceIdem.eq_zero_of_val
    intro n
    have h := happ α 0 P n (by rw [hα, map_zero, sub_zero, Valuation.map_zero]; exact zero_le')
    rwa [map_zero, map_zero, sub_zero] at h

  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
    (Units.map (ι.toRingHom.comp (finPart D)).toMonoidHom x)
  have hXP : ∀ P, ((Units.map (ι.toRingHom.comp (finPart D)).toMonoidHom x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E) P = ι (finPart D (x : AE D)) P := fun _ => rfl
  have hS2 : ∀ P ∈ S, Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) ∧
      Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) ≤
        P.valuation D.host.E (N : D.host.E) * P.valuation D.host.E (k P : D.host.E) := by
    intro P hP
    have h := hS P hP
    rw [hXP] at h
    exact ⟨h.1, h.2.1⟩
  have hS'2 : ∀ P, P ∉ S → Valued.v (ι (finPart D (x : AE D)) P) = 1 ∧ (N : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro P hP
    have h := hS' P hP
    rwa [hXP] at h

  obtain ⟨k', hk'1, hk'2⟩ : ∃ k' : HeightOneSpectrum (𝓞 D.host.E) → D.host.Eˣ,
      (∀ P, P.under (𝓞 D.host.F) = v → k' P = k P) ∧ (∀ P, P.under (𝓞 D.host.F) ≠ v → k' P = 1) :=
    ⟨fun P => if P.under (𝓞 D.host.F) = v then k P else 1, fun _ h => ite_eq_left h, fun _ h => ite_eq_right h⟩
  have hcx := hmain x hx1 S k' ?_ ?_
  · have hprod : ∏ P ∈ S, ((χ.locK P (k' P) : ℂˣ) : ℂ) = 1 := by
      apply Finset.prod_eq_one
      intro P hPS
      by_cases hP : P.under (𝓞 D.host.F) = v
      · rw [hk'1 P hP]
        have hu : χ.loc P (atFin P (k P)) = 1 := by
          apply hunr P hP
          show Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (k P : D.host.E)) = 1
          rw [GlobalTheory.CharLocProd.val_algebraMap, ← (hS2 P hPS).1]
          exact hval P
        show ((χ.loc P (atFin P (k P)) : ℂˣ) : ℂ) = 1
        rw [hu, Units.val_one]
      · rw [hk'2 P hP, map_one, Units.val_one]
    exact Circle.coe_eq_one.mp (hcx.trans hprod)
  · intro P hPS
    by_cases hP : P.under (𝓞 D.host.F) = v
    · rw [hk'1 P hP]
      exact hS2 P hPS
    · rw [hk'2 P hP, hoff P hP]
      refine ⟨?_, ?_⟩
      · rw [Units.val_one, Valuation.map_one, map_one]
      · rw [Units.val_one, map_one, sub_self, Valuation.map_zero]
        exact zero_le'
  · intro P hPS
    exact hS'2 P hPS

end GlobalTheory.UnramOver
