module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.KaB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

private theorem comap_lt_one {K L : Type} [Field K] [Field L] (B : ValuationSubring L) (f : K →+* L) (x : K) :
    (B.comap f).valuation x < 1 ↔ B.valuation (f x) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or,
    ← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]
  simp [map_inv₀]

theorem UpperTheory.V.Z.Kato.Sym.mvPt :
    UpperTheory.V.Z.Kato.Sym.MvPt := by
  classical
  intro Ω _ _ _ ε X m hm τ s hA σ hσ u v P hP
  obtain ⟨-, -, -, -, -, hU, -, -⟩ := admB Ω ε X
  have ka1 := (kaB Ω ε X m hm P.a u hP.hu.1 hP.ha).2.2.2.2.1 σ τ s hA hσ
  have ka2 := (kaB Ω ε X m hm P.b v hP.hv.1 hP.hb).2.2.2.2.1 σ τ s hA hσ
  refine ⟨(hU τ s hA).1 u hP.hu, (hU τ s hA).1 v hP.hv, ?_, ?_, ?_, ?_, ?_⟩
  · show σ P.a ^ m = _
    rw [← map_pow, hP.ha, hσ]
  · show σ P.b ^ m = _
    rw [← map_pow, hP.hb, hσ]
  · intro g h hg hh
    show ka X m (σ P.a) g * ka X m (σ P.b) h =
      cyc m s ^ 2 * P.η (σ⁻¹ * h * σ) - cyc m s ^ 2 * P.η (σ⁻¹ * (g * h) * σ) + cyc m s ^ 2 * P.η (σ⁻¹ * g * σ)
    have e : σ⁻¹ * (g * h) * σ = (σ⁻¹ * g * σ) * (σ⁻¹ * h * σ) := by group
    have c := hP.cob _ _ (ka1 g hg).1 (ka1 h hh).1
    rw [(ka1 g hg).2, (ka2 h hh).2, e]
    linear_combination (cyc m s) ^ 2 * c
  · obtain ⟨B, hB⟩ := hP.lc
    refine ⟨B.image σ, fun h h' hh hh' e => ?_⟩
    show cyc m s ^ 2 * P.η (σ⁻¹ * h * σ) = cyc m s ^ 2 * P.η (σ⁻¹ * h' * σ)
    rw [hB _ _ (ka1 h hh).1 (ka1 h' hh').1]
    intro b hb
    show σ⁻¹ (h (σ b)) = σ⁻¹ (h' (σ b))
    rw [e _ (Finset.mem_image_of_mem _ hb)]
  · intro B h hB hh hz
    show cyc m s ^ 2 * P.η (σ⁻¹ * h * σ) = 0
    rw [hP.unr (B.comap (σ : Kb X →+* Kb X)) _ ?_ (ka1 h hh).1 ?_, mul_zero]
    · have e : (B.comap (σ : Kb X →+* Kb X)).comap (io X) = (B.comap (io X)).comap (τ : X.K →+* X.K) := by
        ext f
        simp only [ValuationSubring.mem_comap, RingHom.coe_coe]
        rw [hσ]
      rw [e]
      exact (hA.2 _).1 hB
    · intro z h1
      rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_comap, ← ValuationSubring.valuation_le_one_iff] at h1
      rw [comap_lt_one]
      have := hz _ h1
      have e : (σ : Kb X →+* Kb X) ((σ⁻¹ * h * σ) z - z) = h ((σ : Kb X →+* Kb X) z) - (σ : Kb X →+* Kb X) z := by
        rw [map_sub]
        congr 1
        exact σ.apply_symm_apply _
      rw [e]
      exact this
