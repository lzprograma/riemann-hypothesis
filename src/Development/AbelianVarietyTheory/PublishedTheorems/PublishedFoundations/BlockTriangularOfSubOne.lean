module

public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ONLeaves
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix

namespace GlobalTheory.FiniteGL

section Radical

variable (k : Type) [Field k] {N : ℕ}

def IsStrictBlock {k : Type} [Field k] (b : Fin N → ℕ) (X : Matrix (Fin N) (Fin N) k) : Prop :=
  ∀ i j, b j ≤ b i → X i j = 0

variable {k}

theorem IsStrictBlock.mul_blockTriangular {b : Fin N → ℕ} {X Y : Matrix (Fin N) (Fin N) k}
    (hX : IsStrictBlock b X) (hY : Y.BlockTriangular b) : IsStrictBlock b (X * Y) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : b l ≤ b i
  · rw [hX i l hl, zero_mul]
  · rw [hY (lt_of_le_of_lt hij (not_le.mp hl)), mul_zero]

theorem blockTriangular_of_sub_one {b : Fin N → ℕ} {X : Matrix (Fin N) (Fin N) k}
    (hX : IsStrictBlock b (X - 1)) : X.BlockTriangular b := by
  intro i j hij
  have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
  have h := hX i j hij.le
  rwa [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at h

variable (k)

def unipRadical (b : Fin N → ℕ) : Subgroup (GL (Fin N) k) where
  carrier := {u | IsStrictBlock b ((u : Matrix (Fin N) (Fin N) k) - 1)}
  one_mem' := by
    intro i j _
    simp
  mul_mem' := by
    intro u v hu hv i j hij
    have e : ((u * v : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) - 1 =
        ((u : Matrix (Fin N) (Fin N) k) - 1) * (v : Matrix (Fin N) (Fin N) k) +
          ((v : Matrix (Fin N) (Fin N) k) - 1) := by
      rw [Units.val_mul]; noncomm_ring
    rw [e, Matrix.add_apply, (IsStrictBlock.mul_blockTriangular hu (blockTriangular_of_sub_one hv)) i j hij,
      hv i j hij, add_zero]
  inv_mem' := by
    intro u hu i j hij
    letI := u.invertible
    have hi : ((u⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).BlockTriangular b := by
      rw [Matrix.coe_units_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular (blockTriangular_of_sub_one hu)
    have e : ((u⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) - 1 =
        -(((u : Matrix (Fin N) (Fin N) k) - 1) * ((u⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)) := by
      rw [sub_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul, neg_sub]
    rw [e, Matrix.neg_apply, (IsStrictBlock.mul_blockTriangular hu hi) i j hij, neg_zero]

variable {k}

theorem mem_unipRadical {b : Fin N → ℕ} {u : GL (Fin N) k} :
    u ∈ unipRadical k b ↔ ∀ i j, b j ≤ b i → ((u : Matrix (Fin N) (Fin N) k) - 1) i j = 0 := Iff.rfl

def IsCuspidal {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∀ b : Fin N → ℕ, Monotone b → (∃ i j, b i ≠ b j) →
    ∀ v : V, (∀ u ∈ unipRadical k b, ρ u v = v) → v = 0

def twoBlocks (N a : ℕ) : Fin N → ℕ := fun i => if (i : ℕ) < a then 0 else 1

theorem isCuspidal_iff_twoBlocks {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V) :
    IsCuspidal ρ ↔ ∀ a : ℕ, 0 < a → a < N →
      ∀ v : V, (∀ u ∈ unipRadical k (twoBlocks N a), ρ u v = v) → v = 0 := by
  constructor
  · intro h a ha0 haN v hv
    refine h (twoBlocks N a) ?_ ⟨⟨0, by omega⟩, ⟨a, haN⟩, ?_⟩ v hv
    · intro i j hij
      have hij' : (i : ℕ) ≤ j := hij
      simp only [twoBlocks]
      split_ifs <;> omega
    · simp [twoBlocks, ha0]
  · intro h b hb hne v hv
    classical
    obtain ⟨i₁, j₁, h₁⟩ := hne
    have hN : 0 < N := i₁.pos
    let i0 : Fin N := ⟨0, hN⟩
    have hmin : ∀ i : Fin N, b i0 ≤ b i := fun i => hb (Fin.mk_le_of_le_val (Nat.zero_le _))
    have hex : ∃ m, ∃ hm : m < N, b i0 < b ⟨m, hm⟩ := by
      by_cases hi : b i0 < b i₁
      · exact ⟨i₁, i₁.isLt, hi⟩
      · refine ⟨j₁, j₁.isLt, lt_of_le_of_ne (hmin j₁) fun he => h₁ ?_⟩
        have := hmin i₁
        change b i0 = b j₁ at he
        omega
    obtain ⟨a, haN, key⟩ : ∃ a, a < N ∧ ∀ i : Fin N, (i : ℕ) < a ↔ ¬ b i0 < b i := by
      refine ⟨Nat.find hex, (Nat.find_spec hex).1, fun i => ⟨fun hi hlt => ?_, fun hi => ?_⟩⟩
      · exact Nat.find_min hex hi ⟨i.isLt, hlt⟩
      · by_contra hge
        obtain ⟨_, hlt⟩ := Nat.find_spec hex
        exact hi (lt_of_lt_of_le hlt (hb (Fin.mk_le_of_le_val (not_lt.mp hge))))
    refine h a ((key i0).mpr (lt_irrefl _)) haN v fun u hu => hv u ?_
    rw [mem_unipRadical] at hu ⊢
    intro i j hij
    apply hu i j
    simp only [twoBlocks]
    by_cases hi : (i : ℕ) < a
    · have hj : (j : ℕ) < a := (key j).mpr fun hlt => (key i).mp hi (lt_of_lt_of_le hlt hij)
      simp [hi, hj]
    · simp only [hi, ite_false]
      split_ifs <;> omega

end Radical

section Examples

def lineRep {G : Type} [Group G] (χ : G →* ℂ) : Representation ℂ G (Fin 1 → ℂ) :=
  (Algebra.lsmul ℂ ℂ (Fin 1 → ℂ)).toMonoidHom.comp χ

theorem lineRep_apply {G : Type} [Group G] (χ : G →* ℂ) (g : G) (v : Fin 1 → ℂ) : lineRep χ g v = χ g • v := rfl

theorem lineRep_isIrreducible {G : Type} [Group G] (χ : G →* ℂ) : (lineRep χ).IsIrreducible := by
  have hs : IsSimpleOrder (Submodule ℂ (Fin 1 → ℂ)) :=
    is_simple_module_of_finrank_eq_one (K := ℂ) (by simp)
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun W => ?_ }
  · exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  · rcases hs.eq_bot_or_eq_top W.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)

end Examples

end GlobalTheory.FiniteGL
