module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.MatchIndOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedAtValueHeckeCharCompIdeleNorm
import Formalism.DoubleCosetMeasures.Statement
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GroundTheory.Global.SemiLocal
open scoped Classical

namespace UpperTheory.V.Z.Gam

theorem normLoc : NormLoc := by
  intro K L _ _ _ _ _ χ
  let ξ : HChar L := ⟨χ.1.comp (GroundTheory.Global.ideleNorm K L), χ.2.1.comp GroundTheory.Global.continuous_ideleNorm, fun k =>
    (congrArg χ.1 (GroundTheory.Global.ideleNorm_diagonal (K := K) k)).trans (χ.2.2 _)⟩
  refine ⟨ξ, ?_⟩
  rintro v ⟨w, hw⟩
  have hN : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ fdeg (⟨w, hw⟩ : PlacesOver L v) :=
    Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal v.asIdeal v.isPrime v.ne_bot
  obtain rfl : v = w.under (𝓞 K) := HeightOneSpectrum.ext hw.over
  refine ⟨MonoidHom.ext fun x => ?_, GlobalTheory.NormValGen.unrAt_val_of_comp_norm K L χ ξ (fun _ => rfl) w _ ?_, hN⟩
  exact congrArg χ.1 (GroundTheory.Global.ideleNorm_finiteEmbedding (K := K) w x)
  simpa only [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hN

end UpperTheory.V.Z.Gam
