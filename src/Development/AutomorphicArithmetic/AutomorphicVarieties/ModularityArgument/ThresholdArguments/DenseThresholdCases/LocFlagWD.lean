module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocCharDR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PstExact
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

@[expose] public section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W UpperTheory.V.Hi
theorem UpperTheory.V.Loc.flag_weil_deligne_of_literal_automorphy_n :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → FlagWD := by
  intro hN L Ω _ _ _ _ _ l _ _ ι n w hw A h a ha r hr hh ω ψ hψ ⟨M, hM⟩ HT P hD O _ _ _ Bw hj
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  obtain ⟨d, hJ, -⟩ := hD O Bw hj
  have hc := fun i => (_root_.UpperTheory.V.Loc.hecke_char_de_rham_of_local_artin_above_l hN h hw ι a ha (ω i) (hh i) (ψ i) (hψ i)).1 O Bw hj
  obtain ⟨F₁, F₂⟩ := UpperTheory.V.Loc.PstExact.flag T ι Bw h hj r (fun i => GlobalTheory.TripleGal.rk1 (ψ i)) M
    (fun g => (hM g).1) (fun g i => ((hM g).2 i).trans (by simp [GlobalTheory.TripleGal.rk1]))
  refine ⟨d, fun τ LL' τ' hτ => ?_, fun s => ?_⟩
  · have e := F₁ τ _ _ (hJ τ LL' τ' hτ) fun i => (hc i).2.1 τ LL' τ' hτ
    have e' : (Finset.univ.val.map fun j => hh j τ) = HT τ := by
      rw [e, Finset.sum, ← Multiset.sum_map_singleton (Finset.univ.val.map fun j => hh j τ), Multiset.map_map]
      rfl
    beta_reduce
    rw [e']
    exact hJ τ LL' τ' hτ
  · rw [(F₂ (hN.aut.berger.isPstAt T Bw r (Units.continuous_val.comp hr) d)).2 s]
    exact Finset.prod_congr rfl fun i _ => (hc i).2.2 s
end
