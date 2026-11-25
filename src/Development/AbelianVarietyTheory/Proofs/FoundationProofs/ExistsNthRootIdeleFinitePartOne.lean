module

public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RealAdelesCmFieldEquivComplexCmType
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
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct

namespace GlobalTheory.IdeleDiv

theorem exists_infAdele_pow_eq (D : D7) (n : ℕ) (hn : 0 < n)
    (z : InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E) :
    ∃ w : InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E, w ^ n = z := by
  obtain ⟨⟨θ, hθ⟩, H⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  obtain ⟨-, -, hb⟩ := H θ hθ
  choose r hr using fun τ : {τ : D.host.E →+* ℂ // τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD} =>
    IsAlgClosed.exists_pow_nat_eq (θ τ.1 z) hn
  obtain ⟨w, hw⟩ := hb.2 r
  refine ⟨w, hb.1 ?_⟩
  funext τ
  have h1 : θ τ.1 w = r τ := congrFun hw τ
  change θ τ.1 (w ^ n) = θ τ.1 z
  rw [map_pow, h1, hr]

theorem exists_pow_eq_of_finPart_eq_one : ∀ (D : D7) (n : ℕ), 0 < n → ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → ∃ y : (AE D)ˣ, y ^ n = x := by
  intro D n hn x hx
  obtain ⟨e, he, -, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  obtain ⟨w, hw⟩ := exists_infAdele_pow_eq D n hn (e (x : AE D)).1
  have h2 : (e (x : AE D)).2 = 1 := (he _).2.trans hx
  have hy : (e.symm (w, 1)) ^ n = (x : AE D) := by
    apply e.injective
    rw [map_pow, RingEquiv.apply_symm_apply]
    exact Prod.ext hw (by rw [h2]; exact one_pow n)
  have hu : IsUnit (e.symm (w, 1)) := (isUnit_pow_iff hn.ne').1 (hy ▸ x.isUnit)
  obtain ⟨y, hy'⟩ := hu
  refine ⟨y, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, hy']
  exact hy

end GlobalTheory.IdeleDiv
