module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeA

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertUnitaryCosetSymmetryHeckeEven, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertUnitaryCosetSymmetryHeckeEvenStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertUnitaryCosetSymmetryHeckeEven =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertUnitaryCosetSymmetryHeckeEven", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm\nimport Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan\nimport Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeA\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

noncomputable section

namespace GlobalTheory.ChainOnto.InertSym

theorem cosets_eq {G : Type} [Group G] (K : Subgroup G) {g g' : G} {a b : G} (ha : a ∈ K) (hb : b ∈ K)
    (e : g' = a * g * b) (c : G ⧸ K) :
    (∃ k ∈ K, c = ((k * g' : G) : G ⧸ K)) ↔ (∃ k ∈ K, c = ((k * g : G) : G ⧸ K)) := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * a, mul_mem hk ha, ?_⟩
    rw [e, show k * (a * g * b) = (k * a * g) * b by group, QuotientGroup.mk_mul_of_mem _ hb]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * a⁻¹, mul_mem hk (inv_mem ha), ?_⟩
    rw [e, show k * a⁻¹ * (a * g * b) = (k * g) * b by group, QuotientGroup.mk_mul_of_mem _ hb]

theorem cosetSym_of_inv {G : Type} [Group G] (K : Subgroup G)
    (h : ∀ g : G, ∃ a ∈ K, ∃ b ∈ K, g⁻¹ = a * g * b) : CosetSym K := by
  intro g
  obtain ⟨a, ha, b, hb, e⟩ := h g
  exact (Nat.card_congr (Equiv.subtypeEquivRight fun c => cosets_eq K ha hb e c)).symm

theorem inv_mem_KU {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (n : ℕ) (g : GU σ n) :
    ∃ a ∈ KU σ n, ∃ b ∈ KU σ n, g⁻¹ = a * g * b := by
  have hint : ∀ i j, Formalism.UG.antiJ L n i j ∈ Formalism.UG.intL L := by
    intro i j; unfold Formalism.UG.antiJ; split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨J, hJ, hJe⟩ := Formalism.UG.P.cartan_exists_glint (Formalism.UG.intL L) _ _
    (GlobalTheory.UnitarySwap.antiJ_mul_self (L := L) (n := n)) hint hint
  obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := (GlobalTheory.UnitarySwap.inv_mem_doubleCoset_and_comm).1 L ϖ σ q n J hU hJ (by
    intro i j
    rw [hJe]
    simp only [Formalism.UG.antiJ, add_comm i.val j.val]
    split_ifs <;> simp) (g : GL (Fin n) L) (by rw [hJe]; exact g.2)
  rw [hJe] at hk₁ hk₂
  exact ⟨⟨k₁, hk₁.1⟩, hk₁, ⟨k₂, hk₂.1⟩, hk₂, Subtype.ext e⟩

end GlobalTheory.ChainOnto.InertSym

namespace GlobalTheory.ChainOnto

theorem inert_cosetSym_heckeEven : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ n : ℕ, IsCommensurated (KU σ n) ∧ CosetSym (KU σ n) ∧ ∀ φ ∈ Hecke ℂ (KU σ n), ∀ g, φ g⁻¹ = φ g := by
  intro L _ _ _ ϖ σ q hU n
  refine ⟨Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n, InertSym.cosetSym_of_inv _ (InertSym.inv_mem_KU hU n), ?_⟩
  intro φ hφ g
  obtain ⟨a, ha, b, hb, e⟩ := InertSym.inv_mem_KU hU n g
  rw [e]
  exact hφ.1 ⟨a, ha⟩ ⟨b, hb⟩ g

end GlobalTheory.ChainOnto

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertUnitaryCosetSymmetryHeckeEven =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertUnitaryCosetSymmetryHeckeEvenStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertUnitaryCosetSymmetryHeckeEvenStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertUnitaryCosetSymmetryHeckeEven\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertUnitaryCosetSymmetryHeckeEvenStatement =====
