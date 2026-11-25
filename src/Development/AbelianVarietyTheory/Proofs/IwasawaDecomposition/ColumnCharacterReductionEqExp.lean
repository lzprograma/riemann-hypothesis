module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitCompletelyPlaceStructure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGLocIdGChiTied
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.LocalRingCardinality.SpanPowerMembership.Adelic
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.Mem.TypePrimes.Red

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem absNorm_and_unram {p : ℕ} (hp : p.Prime) (hs : GlobalTheory.St.G.SplitsIn E p) (v : HeightOneSpectrum (𝓞 F))
    (h : (p : 𝓞 F) ∈ v.asIdeal) : Ideal.absNorm v.asIdeal = p ∧ (p : 𝓞 F) ∉ v.asIdeal ^ 2 := by
  have := v.isPrime
  have hM : v.asIdeal.IsMaximal := v.isMaximal
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hZ : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp'.irreducible
  obtain ⟨⟨w, hwp, hwl⟩⟩ : Nonempty (v.asIdeal.primesOver (𝓞 E)) := inferInstance
  have key := GlobalTheory.St.G.SplitPrime.ram_inertia_tower (F := F) (E := E) p hp hs v.asIdeal h w
  have hL : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := (Ideal.liesOver_span_iff v.isPrime.ne_top hp').2 (by simpa using h)
  have hu : Ideal.under ℤ v.asIdeal = Ideal.span {(p : ℤ)} := hL.over.symm
  constructor
  · rw [Ideal.absNorm_eq_pow_inertiaDeg' v.asIdeal hp, Ideal.inertiaDeg'_eq_inertiaDeg, key.1.2, pow_one]
  · intro h2
    have e : (Ideal.span {(p : ℤ)}).ramificationIdx' v.asIdeal = v.asIdeal.ramificationIdx ℤ := by
      rw [← hu]; exact Ideal.ramificationIdx'_eq_ramificationIdx _ _ (by rw [hu, Ne, Ideal.span_singleton_eq_bot]; exact hp'.ne_zero)
    have h3 := Ideal.ramificationIdx_ne_one_iff (p := Ideal.span {(p : ℤ)}) (P := v.asIdeal) (by simpa [Ideal.map_span] using h)
    exact (h3.2 (by simpa [Ideal.map_span] using h2)) (e.trans key.1.1)

end Place


section Host

theorem exists_hostXi0_inverse_integer {R : Ranks} (H : Host R) : ∃ t : 𝓞 H.E, H.xi0 * (t : H.E) = 1 := by
  have hd : (H.d : H.E) ≠ 0 := Nat.cast_ne_zero.2 H.hyp.2.1.ne_zero
  have hsq := H.sqrtMinusD_sq
  have hb0 : H.sqrtMinusD ≠ 0 := by
    intro h0
    rw [h0] at hsq
    exact hd (by simpa using hsq.symm)
  have hN0 : ((Ideal.absNorm H.ccK : ℕ) : H.E) ≠ 0 :=
    Nat.cast_ne_zero.2 fun e => H.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
  have hi : IsIntegral ℤ H.sqrtMinusD := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [hsq]
    simpa using (isIntegral_algebraMap (R := ℤ) (A := H.E) (x := -(H.d : ℤ)))
  have hiN : IsIntegral ℤ ((Ideal.absNorm H.ccK : ℕ) : H.E) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := H.E) (x := ((Ideal.absNorm H.ccK : ℕ) : ℤ)))
  refine ⟨⟨-(((Ideal.absNorm H.ccK : ℕ) : H.E) * H.sqrtMinusD), (hiN.mul hi).neg⟩, ?_⟩
  show H.xi0 * (-(((Ideal.absNorm H.ccK : ℕ) : H.E) * H.sqrtMinusD)) = 1
  rw [Host.xi0]
  field_simp

end Host

end GlobalTheory.Mem.TypePrimes.Red
