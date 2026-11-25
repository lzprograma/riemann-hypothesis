module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdelesStatement
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct

namespace GlobalTheory.CharOrderFin

theorem locK_pow_eq_one {L : Type} [Field L] [NumberField L] {χ : HChar L} {n : ℕ}
    (h : χ.OrderDvd n) (P : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : χ.locK P k ^ n = 1 := by
  have h1 : (χ.1 : _ →* ℂˣ) ^ n = 1 := by
    have := congrArg Subtype.val h
    simpa using this
  have h2 : ∀ y, χ.1 y ^ n = 1 := fun y => by
    have := DFunLike.congr_fun h1 y
    simpa [MonoidHom.pow_apply] using this
  exact h2 _

theorem char_pow_eq_one_of_orderDvd : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E),
    ChrEq c χ → ∀ n : ℕ, χ.OrderDvd n → ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → c x ^ n = 1 := by
  intro D c χ hc n hn x hx
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := GlobalTheory.T.exists_finitePlaceIdempotent_baseChangeAdeles D ι h1 h2 h3
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 h4 c χ hc
  let y : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ :=
    ⟨ι (finPart D (x : AE D)), ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)),
      by rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one],
      by rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]⟩
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN y
  have h5 := hprod x hx S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'
  apply Circle.ext
  have h6 : ((c x ^ n : Circle) : ℂ) = ((c x : Circle) : ℂ) ^ n :=
    map_pow Circle.coeHom (c x) n
  rw [h6, h5, ← Finset.prod_pow, Circle.coe_one]
  refine Finset.prod_eq_one fun P _ => ?_
  rw [← Units.val_pow_eq_pow_val, locK_pow_eq_one hn, Units.val_one]

end GlobalTheory.CharOrderFin
