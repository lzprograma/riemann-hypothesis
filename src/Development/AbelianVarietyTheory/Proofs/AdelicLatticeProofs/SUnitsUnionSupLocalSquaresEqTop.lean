module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitValuationEqOfAdm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareMulOfNonsquareUnits
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem sUnits_union_sup_finSq_eq_top :
    ∀ (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))] (S T : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → Disjoint S T → (∀ A : Finset (HeightOneSpectrum (𝓞 F)), ∃ u ∈ sUnits F S, ∀ v ∈ T, (IsSquare (algebraMap F (v.adicCompletion F) (u : F)) ↔ v ∉ A)) → sUnits F (S ∪ T) ⊔ finSq F T = ⊤ := by
  intro F _ _ _ S T hS hST hA
  classical
  have hval : ∀ (v : HeightOneSpectrum (𝓞 F)) (z : F),
      Valued.v (algebraMap F (v.adicCompletion F) z) = v.valuation F z :=
    fun v z => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z
  have hTS : ∀ v ∈ T, v ∉ S := fun v hv h => Finset.disjoint_left.1 hST h hv
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, ha⟩ := exists_unit_valuation_eq_of_adm F S T
    (fun v => if v ∈ T then -WithZero.log (v.valuation F (x : F)) else 0) hS
    (fun v hv => by simp [hv])
  have haU : a ∈ sUnits F (S ∪ T) := by
    rw [mem_sUnits]
    intro v hv
    rw [Finset.mem_union, not_or] at hv
    rw [ha v hv.1]
    simp [hv.2]
  have hy : ∀ v ∈ T, v.valuation F ((a * x : Fˣ) : F) = 1 := by
    intro v hv
    have hx0 : v.valuation F (x : F) ≠ 0 := by simp
    rw [Units.val_mul, map_mul, ha v (hTS v hv), ite_eq_left hv, WithZero.exp_neg,
      WithZero.exp_log hx0, inv_mul_cancel₀ hx0]
  obtain ⟨u, hu, huA⟩ := hA (T.filter fun v =>
    ¬ IsSquare (algebraMap F (v.adicCompletion F) ((a * x : Fˣ) : F)))
  have huU : u ∈ sUnits F (S ∪ T) := by
    rw [mem_sUnits] at hu ⊢
    intro v hv
    exact hu v fun h => hv (Finset.mem_union_left _ h)
  have hsq : u * (a * x) ∈ finSq F T := by
    simp only [finSq, Subgroup.mem_iInf]
    intro v hv
    rw [mem_sqSub, Units.val_mul, map_mul]
    have h := huA v hv
    rw [Finset.mem_filter] at h
    by_cases hs : IsSquare (algebraMap F (v.adicCompletion F) ((a * x : Fˣ) : F))
    · exact (h.2 fun hh => hh.2 hs).mul hs
    · refine isSquare_mul_of_nonsquare_units F v ?_ _ _ ?_ ?_ (fun hh => h.1 hh ⟨hv, hs⟩) hs
      · rw [← map_ofNat (algebraMap F (v.adicCompletion F)) 2, hval]
        exact (hS v (hTS v hv)).1
      · rw [hval]
        exact (mem_sUnits F S u).1 hu v (hTS v hv)
      · rw [hval]
        exact hy v hv
  have hx : x = (u * a)⁻¹ * (u * (a * x)) := by group
  rw [hx]
  exact Subgroup.mul_mem_sup (inv_mem (mul_mem huU haU)) hsq

end GlobalTheory.QNorm
