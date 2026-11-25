module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar

namespace GlobalTheory.VolIndex

open GlobalTheory.Mass GlobalTheory.Mass.Levels

theorem latLev_le_range {D : D7} (V : HSp D) : latLev V ≤ (Lev.finE V).range := by
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj D.sp.cm.sig V.gram
  rintro _ ⟨_, ⟨b, -, rfl⟩, rfl⟩
  obtain ⟨g, rfl⟩ := hπ.surjective b
  refine ⟨g, ?_⟩
  change Lev.finE V g =
    ((swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram (π g) : UA D.sp.cm V.gram) : GL (Fin V.rank) (Lev.EAf D))
  rw [coe_swapPts, hπ g]
  rfl

theorem vol_eq_index_mul_mass : ∀ (D : D7) (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), V.SigOK → V.IsPosDef → K ≤ GlobalTheory.Mass.Levels.latLev V → K.relIndex (GlobalTheory.Mass.Levels.latLev V) ≠ 0 → IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) → IsMeasDef V K ν 𝓕 → (ν 𝓕).toReal = (K.relIndex (GlobalTheory.Mass.Levels.latLev V) : ℝ) * GlobalTheory.Mass.unitaryMass D.sp.cm.sig V.gram (GlobalTheory.Mass.Levels.latStab V) := by
  intro D V K ν 𝓕 hW hs hK hi ho hν
  have hd : Formalism.UG.IsTotDef D.sp.cm.sig V.gram := GlobalTheory.DefiniteQuotient.isTotDef_of_posDef V fun τ => by
    have := hW (Formalism.BasicNotions.TH.tauE D τ)
    rw [hs] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj D.sp.cm.sig V.gram
  obtain ⟨hc, hL⟩ := latStab_compact_open V
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := hν.1.1
  have h1 : ν (K.comap (Lev.finE V)) = 1 := measure_comap_finE hν.1
  have hidx : (K.comap (Lev.finE V)).relIndex ((latLev V).comap (Lev.finE V)) = K.relIndex (latLev V) := by
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self (latLev_le_range V)]
  have : ((K.comap (Lev.finE V)).subgroupOf ((latLev V).comap (Lev.finE V))).FiniteIndex := ⟨hidx.trans_ne hi⟩
  have h2 := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure (K.comap (Lev.finE V)) ((latLev V).comap (Lev.finE V))
    (Subgroup.comap_mono hK) ho.measurableSet ν
  rw [hidx, h1, mul_one] at h2
  have hn0 : ((K.relIndex (latLev V) : ℕ) : ENNReal) ≠ 0 := Nat.cast_ne_zero.2 hi
  have hnt : ((K.relIndex (latLev V) : ℕ) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcm := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  have h3 := hπ.measure_toReal hcm.1 (hcm.2 V) hd hc hL (((K.relIndex (latLev V) : ℕ) : ENNReal)⁻¹ • ν)
    (by
      rw [← toLev_latLev, comap_toLev V _ hπ, Measure.smul_apply, ← h2, smul_eq_mul]
      exact ENNReal.inv_mul_cancel hn0 hnt)
    (hν.2.mono (Measure.smul_absolutelyContinuous))
  rw [← h3, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    mul_inv_cancel_left₀ (Nat.cast_ne_zero.2 hi)]

end GlobalTheory.VolIndex
