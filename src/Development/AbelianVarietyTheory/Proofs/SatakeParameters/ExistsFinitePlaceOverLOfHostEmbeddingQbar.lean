module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA
public import Formalism.SharedLemmas.NormLeOneOfIntegral

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc

namespace GlobalTheory.PlaceOfEmb

theorem norm_le_one_of_isIntegral' {K : Type} [NormedField K] [IsUltrametricDist K] {x : K}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  apply _root_.Formalism.SharedLemmas.norm_le_one_of_isIntegral <;> assumption

variable {E : Type} [Field E] [NumberField E] {C : Type} [NormedField C] [IsUltrametricDist C]

theorem norm_map_le_one (τ : E →+* C) (x : 𝓞 E) : ‖τ (x : E)‖ ≤ 1 :=
  norm_le_one_of_isIntegral' ((x.isIntegral_coe).map (τ.toIntAlgHom))

def ballIdeal (τ : E →+* C) : Ideal (𝓞 E) where
  carrier := {x | ‖τ (x : E)‖ < 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change ‖τ (a : E)‖ < 1 at ha
    change ‖τ (b : E)‖ < 1 at hb
    change ‖τ ((a : E) + (b : E))‖ < 1
    rw [map_add (f := _)]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  smul_mem' := by
    intro c x hx
    change ‖τ (x : E)‖ < 1 at hx
    change ‖τ ((c : E) * (x : E))‖ < 1
    rw [map_mul, norm_mul]
    calc ‖τ (c : E)‖ * ‖τ (x : E)‖ ≤ 1 * ‖τ (x : E)‖ :=
          mul_le_mul_of_nonneg_right (norm_map_le_one τ c) (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hx

theorem mem_ballIdeal (τ : E →+* C) (x : 𝓞 E) : x ∈ ballIdeal τ ↔ ‖τ (x : E)‖ < 1 := Iff.rfl

theorem ballIdeal_isPrime (τ : E →+* C) : (ballIdeal τ).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_ballIdeal]; simp
  · intro a b hab
    change ‖τ ((a : E) * (b : E))‖ < 1 at hab
    rw [map_mul, norm_mul] at hab
    by_contra! h
    rw [mem_ballIdeal, mem_ballIdeal] at h
    have ha : ‖τ (a : E)‖ = 1 := le_antisymm (norm_map_le_one τ a) (not_lt.1 h.1)
    have hb : ‖τ (b : E)‖ = 1 := le_antisymm (norm_map_le_one τ b) (not_lt.1 h.2)
    rw [ha, hb] at hab; norm_num at hab

end GlobalTheory.PlaceOfEmb

open GlobalTheory.PlaceOfEmb in
theorem GlobalTheory.PlaceOfEmb.exists_place_of_emb : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (τ : D.host.E →+* Qbar l), ∃ w : PlE D.host, w ∈ placesOver D.host.E l ∧ ∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal := by
  intro D l _ τ
  have hl : ((l : 𝓞 D.host.E)) ∈ ballIdeal τ := by
    rw [mem_ballIdeal]
    simp only [map_natCast]
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hne : ballIdeal τ ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hl
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) hl
  refine ⟨⟨ballIdeal τ, ballIdeal_isPrime τ, hne⟩, hl, fun x => Iff.rfl⟩
