module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsPowGrpSplitTorus
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsMonHomOfComm
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPowGrpBaseChange
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PowExt
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.QuasiCompactGeomConnectedPow
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothIsMultiplicative
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj

namespace GlobalTheory.PowGrp

theorem nonempty_torusExtension_of_isPowGrp : ∀ (K : Type) [Field K] (G' G : Over (Spec (CommRingCat.of K))) [GrpObj G'] [GrpObj G] (j : ℕ), IsPowGrp G' G j → Nonempty (TorusExtension G) → Nonempty (TorusExtension G') := by
  intro K _ G' G _ _ j p hT
  obtain ⟨T⟩ := hT
  cases T with
  | mk X B hB q hqm0 hqf0 hqs0 hqc0 i him0 hker =>
    have pB := ReciprocityTheory.ChartRestriction.G.Out.powIsPowGrp B j
    have pT := GlobalTheory.SplitTorusPow.isPowGrp (Spec (CommRingCat.of K)) (AddEquiv.refl (Fin j → X))
    obtain ⟨q', hq, hqm, hqf, hqs, hqc, -⟩ := GlobalTheory.PowMap.main _ G' G _ B j p pB q
    obtain ⟨i', hi, him, -⟩ := GlobalTheory.PowMap.main _ _ _ G' G j pT p i
    exact ⟨{ X := Fin j → X
             addCommGroup := inferInstance
             free := inferInstance
             finite := inferInstance
             B := ReciprocityTheory.ChartRestriction.G.Out.powObj B j
             grpB := inferInstance
             isAbelian := (GlobalTheory.PowGrp.powers _ _ _ j pB).2.2.2.1 hB
             q := q'
             q_hom := hqm hqm0
             q_flat := hqf hqf0
             q_surjective := hqs hqs0
             q_quasiCompact := hqc hqc0
             i := i'
             i_hom := him him0
             isKernel := GlobalTheory.PowKernel.main _ _ _ G' G _ _ j pT p pB i q i' q' hi hq hker }⟩

theorem isSemiAbelian_pow : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j), IsSemiAbelian G → IsSemiAbelian G' := by
  intro S G' G _ _ _ _ j p' hG
  obtain ⟨_, hs, hsep, hqc, hgc, hf⟩ := hG
  have hpow := GlobalTheory.PowGrp.powers S G' G j p'
  have hqg := GlobalTheory.PowGrp.quasiCompact_geomConnected_pow S G' G j p'
  refine ⟨inferInstance, hpow.1 hs, hpow.2.1 hsep, hqg.1 hqc, hqg.2 hs hgc, ?_⟩
  intro Ω _ _ x
  obtain ⟨px, -⟩ := GlobalTheory.isPowGrp_baseChange S _ x G' G j p'
  exact nonempty_torusExtension_of_isPowGrp Ω _ _ j px (hf Ω x)

end GlobalTheory.PowGrp
