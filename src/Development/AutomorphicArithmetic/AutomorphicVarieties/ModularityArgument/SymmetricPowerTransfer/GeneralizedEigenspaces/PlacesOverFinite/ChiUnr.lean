module

import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOneOfNear
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.LinkedEndEOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Sd

namespace UpperTheory.V.Z.Sym.Pl

private theorem root_one {l : ℕ} [Fact l.Prime] {x : Qbar l} {n : ℕ} (hn : ¬ l ∣ n) (hx : x ^ n = 1)
    (h : ‖x - 1‖ < 1) : x = 1 := by
  apply _root_.UpperTheory.Reformulated.B.S7.eq_one_of_near <;> assumption

private theorem cyc_one (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (A : ValuationSubring Ω) (hA : ¬ A.valuation (l : Ω) < 1) {σ : G ℚ Ω} (hσ : σ ∈ Ine (F := ℚ) A) :
    cycZ ℚ Ω l σ = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  show cyclotomicCharacter Ω l σ.toRingEquiv = 1
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have e1 := cyclotomicCharacter.spec (L := Ω) l σ.toRingEquiv ζ hζ.pow_eq_one
  have hv : ¬ A.valuation ((l ^ n : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, map_pow, not_lt]
    exact one_le_pow₀ (not_lt.1 hA)
  have e2 := Chr.cls_spec (l ^ n) σ ζ hζ.pow_eq_one
  rw [show Chr.cls ℚ Ω (l ^ n) σ = 1 from (Chr.clsFacts ℚ Ω (l ^ n)).2.2.2.2 A hv hσ] at e2
  have e3 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (e1.symm.trans e2)
  rw [ZMod.val_injective _ e3]
  simp

theorem chiUnr : ChiUnr := by
  intro Ω _ _ _ l _ c N _ e ψ χ' j hord hcong M hM L _ _ _ A hA s hs
  have hv : ¬ A.valuation (l : Ω) < 1 ∧ ¬ A.valuation (N : Ω) < 1 := by
    obtain ⟨k, rfl⟩ := hM
    have hn : ∀ n : ℕ, A.valuation (n : Ω) ≤ 1 := fun n => (A.valuation_le_one_iff _).2 (natCast_mem A n)
    rw [Nat.cast_mul, Nat.cast_mul, map_mul, map_mul] at hA
    refine ⟨fun h => hA ?_, fun h => hA ?_⟩
    · exact mul_lt_one_of_lt_of_le (mul_lt_one_of_lt_of_le h (hn N)) (hn k)
    · exact mul_lt_one_of_lt_of_le (lt_of_le_of_lt (mul_le_of_le_one_left' (hn l)) h) (hn k)
  have hσ : galEmb ℚ L Ω s ∈ Ine (F := ℚ) A := ⟨hs.1, fun x hx => hs.2 x hx⟩
  set σ := galEmb ℚ L Ω s with hσdef
  have hz : cycZ ℚ Ω l σ = 1 := cyc_one Ω l A hv.1 hσ
  have hcyc : cycBar ℚ Ω l σ = 1 := by simp [cycBar, hz]
  have hchi : UpperTheory.V.Base.chiO ℚ Ω l c.O σ = 1 := by simp [UpperTheory.V.Base.chiO, hz]
  have hdir : Chr.dirG ℚ Ω ψ σ = 1 := by
    rw [Chr.dirG, MonoidHom.comp_apply,
      show Chr.cls ℚ Ω N σ = 1 from (Chr.clsFacts ℚ Ω N).2.2.2.2 A hv.2 hσ, map_one]
  have hP : Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1 := by
    rw [Chr.Psi, MonoidHom.mul_apply, MonoidHom.zpow_apply, hchi, hdir, one_zpow, one_mul]
  have h := hcong σ
  rw [MonoidHom.mul_apply, MonoidHom.pow_apply, hcyc, one_pow, one_mul, hP] at h
  have h' : ‖((χ' σ : (Qbar l)ˣ) : Qbar l) - 1‖ < 1 := h
  have ho : ((χ' σ : (Qbar l)ˣ) : Qbar l) ^ orderOf χ' = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, pow_orderOf_eq_one, MonoidHom.one_apply, Units.val_one]
  exact Units.ext (root_one hord ho h')

end UpperTheory.V.Z.Sym.Pl
