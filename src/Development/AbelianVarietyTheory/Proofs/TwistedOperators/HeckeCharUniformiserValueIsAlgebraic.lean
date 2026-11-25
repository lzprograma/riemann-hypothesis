module

public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.AlgValsFinMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.EvFLocalIdeleSelf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.OrdFEqOfClassOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.ValuedAtFin
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host
noncomputable section

namespace GlobalTheory

open PI.AlgValsFin.W ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1

theorem isAlgebraic_embedding_apply {L : Type} [Field L] [NumberField L] (φ : L →+* ℂ) (x : L) :
    IsAlgebraic ℚ (φ x) :=
  (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom φ.toRatAlgHom

theorem heckeChar_val_isAlgebraic : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (m : (L →+* ℂ) → ℤ),
    (∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ φ : L →+* ℂ, φ (k : L) ^ m φ) →
    ∀ w : HeightOneSpectrum (𝓞 L), IsAlgebraic ℚ ((χ.val w : ℂˣ) : ℂ) := by
  intro L _ _ χ m hm w
  classical

  obtain ⟨h, hpos, hk⟩ := (classPow : ClassPow L)
  obtain ⟨k, hk⟩ := hk w
  have hkw : ordF w k = (h : ℤ) := by rw [hk w, ite_eq_left rfl]
  have hout : ∀ v, v ∉ ({w} : Finset (HeightOneSpectrum (𝓞 L))) → ordF v k = 0 := by
    intro v hv
    rw [hk v, ite_eq_right (by simpa using hv)]
  obtain ⟨r, hr, hdec⟩ := (decomp : Decomp L) k {w} hout
  rw [Finset.prod_singleton] at hdec
  have hrel : χ.inf k * χ.loc w (atFin w k) * χ.1 r = 1 := by
    have e := χ.2.2 k
    rw [hdec, map_mul, map_mul] at e
    exact e
  obtain ⟨N, hN, hNt⟩ := torsUnits L χ

  have hinf : IsAlgebraic ℚ ((χ.inf k : ℂˣ) : ℂ) := by
    rw [hm k, ← mem_algebraicClosure_iff]
    refine prod_mem fun φ _ => zpow_mem ?_ _
    exact mem_algebraicClosure_iff.2 (isAlgebraic_embedding_apply φ _)

  have hloc : IsAlgebraic ℚ ((χ.loc w (atFin w k) : ℂˣ) : ℂ) := by
    have e : χ.loc w (atFin w k) ^ N = (χ.inf k ^ N)⁻¹ := by
      have e1 := congrArg (· ^ N) hrel
      simp only [mul_pow, hNt r hr, mul_one, one_pow] at e1
      exact eq_inv_of_mul_eq_one_right e1
    refine IsAlgebraic.of_pow hN ?_
    rw [← Units.val_pow_eq_pow_val, e, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      ← mem_algebraicClosure_iff]
    exact inv_mem (pow_mem (mem_algebraicClosure_iff.2 hinf) _)

  set y : (w.adicCompletion L)ˣ := atFin w (unif w) ^ h * (atFin w k)⁻¹ with hy
  have hyv : Valued.v ((y : (w.adicCompletion L)ˣ) : w.adicCompletion L) = 1 := by
    have h1 : Valued.v ((atFin w (unif w) : (w.adicCompletion L)ˣ) : w.adicCompletion L) =
        WithZero.exp (-1) := unif_spec w
    rw [hy, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, map_pow, h1,
      valued_atFin, hkw, ← WithZero.exp_nsmul, ← WithZero.exp_neg, ← WithZero.exp_add]
    simp
  have hyU : localIdele L w y ∈ UFin L := by
    refine ⟨rfl, fun v => ?_⟩
    by_cases hv : v = w
    · subst hv
      rw [localIdele_snd_self]
      exact hyv
    · rw [(localIdele_isSupportedAt L w y).2 v hv, map_one]
  have hyN : χ.loc w y ^ N = 1 := hNt _ hyU
  have hyval : χ.loc w y = χ.val w ^ h * (χ.loc w (atFin w k))⁻¹ := by
    rw [hy, map_mul, map_pow, map_inv]
    rfl
  have hpow : χ.val w ^ (h * N) = χ.loc w (atFin w k) ^ N := by
    rw [hyval, mul_pow, ← pow_mul, inv_pow, mul_inv_eq_one] at hyN
    exact hyN
  refine IsAlgebraic.of_pow (Nat.mul_pos hpos hN) ?_
  rw [← Units.val_pow_eq_pow_val, hpow, Units.val_pow_eq_pow_val, ← mem_algebraicClosure_iff]
  exact pow_mem (mem_algebraicClosure_iff.2 hloc) _

end GlobalTheory
