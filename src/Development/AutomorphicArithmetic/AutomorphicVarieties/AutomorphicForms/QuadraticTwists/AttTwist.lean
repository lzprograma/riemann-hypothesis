module

import all Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisNormCompatibilityOfFrobeniusRestriction
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusEigenvaluesTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion
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
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

private theorem ev_notMem {K : Type} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  apply _root_.ev_notMem <;> assumption

private theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

private theorem sat_twist {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} (P : CuspSub K n)
    {w : HeightOneSpectrum (𝓞 K)} {B : Multiset ℂˣ} (h : (CG.mk P).HasSat w B) {κ : HChar K} (hκ : κ.UnrAt w) :
    (CG.mk (P.twist κ)).HasSat w (B.map (· * κ.val w)) := by
  rw [CG.hasSat_mk] at h ⊢
  exact GlobalTheory.SphGal.hasSatGL_twist K n P κ w B hκ h

theorem UpperTheory.V.Af.Cq.attTwist :
    ∀ (K Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
        (R : G K Ω →* GL (Fin n) (Qbar l)) (P : CuspSub K n), AttC ι R P → ∀ (art : Ideles K →* Gab K Ω) (κ : HChar K) (m : (K →+* ℂ) → ℤ)
        (μ : G K Ω →* (Qbar l)ˣ), IsGlobalArtin art → IsLAdicOf art ι κ m μ → AttC ι (tw R μ) (P.twist κ) := by
  intro K Ω _ _ _ _ _ _ l _ ι n R P hA art κ m μ ha h
  refine ⟨(UpperTheory.galoisRep_irreducibility_criterion.1 _ (G K Ω) _ n R).2.2 μ hA.1, ?_⟩
  filter_upwards [hA.2, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified κ), ev_notMem (K := K) l]
    with w ⟨B, hB, hE⟩ hu hl
  refine ⟨_, sat_twist P hB hu, ?_⟩
  have hc : UpperTheory.V.Af.Bc.CharEig ι μ w (κ.val w : ℂ) := by
    refine fun A hA => ⟨(h.unr_iff ha (Or.inl hl) hA).2 hu, fun σ hσ => ?_⟩
    rw [map_inv, Units.val_inv_eq_inv_val, h.frob_unr ha (Or.inl hl) hu hA hσ, inv_inv, RingEquiv.apply_symm_apply]
  have h4 := UpperTheory.frobenius_eigenvalues_twist K Ω l ι n R μ w _ _ hE hc
  convert h4 using 1
  simp only [algSat_eq, Multiset.map_map]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_mul, mul_assoc]
