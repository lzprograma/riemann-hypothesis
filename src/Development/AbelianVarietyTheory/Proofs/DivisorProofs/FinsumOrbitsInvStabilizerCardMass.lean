module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumFiberwiseOfFiniteSupportComplex
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.GroupTheory.Index

@[expose] public section

namespace GlobalTheory

open MulAction Function

theorem finsum_orbits_stabilizer_mass {K Z : Type} [Group K] [Finite K] [MulAction K Z]
    (f : Z → ℂ) (hf : ∀ (k : K) (z : Z), f (k • z) = f z) (hs : (Function.support f).Finite) :
    ∑ᶠ o : MulAction.orbitRel.Quotient K Z,
        ((Nat.card (MulAction.stabilizer K (Quotient.out o)) : ℕ) : ℂ)⁻¹ * f (Quotient.out o) =
      ((Nat.card K : ℕ) : ℂ)⁻¹ * ∑ᶠ z, f z := by
  classical
  let ρ : Z → orbitRel.Quotient K Z := fun z => Quotient.mk'' z

  have hmem : ∀ (o : orbitRel.Quotient K Z) (a : Z), ρ a = o ↔ a ∈ orbit K (Quotient.out o) :=
    fun o a => by
      rw [← orbitRel.Quotient.orbit_eq_orbit_out o Quotient.out_eq',
        orbitRel.Quotient.mem_orbit]
  have hfib : ∀ o : orbitRel.Quotient K Z,
      (∑ᶠ a : {a // ρ a = o}, f a.1) = (Nat.card (orbit K (Quotient.out o)) : ℂ) * f (Quotient.out o) := by
    intro o
    let e : {a // ρ a = o} ≃ orbit K (Quotient.out o) := Equiv.subtypeEquivRight (hmem o)
    have : Finite (orbit K (Quotient.out o)) := (Set.finite_range fun k : K => k • Quotient.out o).to_subtype
    have : Finite {a // ρ a = o} := Finite.of_equiv _ e.symm
    let : Fintype {a // ρ a = o} := Fintype.ofFinite _
    have hc : ∀ a : {a // ρ a = o}, f a.1 = f (Quotient.out o) := by
      intro a
      obtain ⟨k, hk⟩ := (hmem o a.1).1 a.2
      rw [← hk]; exact hf _ _
    rw [finsum_eq_sum_of_fintype, Finset.sum_congr rfl (fun a _ => hc a), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, Nat.card_congr e]
  have hcard : ∀ z : Z, Nat.card (orbit K z) * Nat.card (stabilizer K z) = Nat.card K := by
    intro z
    let : Fintype K := Fintype.ofFinite K
    rw [← (stabilizer K z).index_mul_card, MulAction.index_stabilizer, Nat.card_coe_set_eq]
  rw [finsum_fiberwise_of_finite_support ρ f hs]
  simp_rw [hfib]
  rw [mul_finsum]
  apply finsum_congr
  intro o
  have h := hcard (Quotient.out o)
  have : Finite (orbit K (Quotient.out o)) := (Set.finite_range fun k : K => k • Quotient.out o).to_subtype
  have : Nonempty (orbit K (Quotient.out o)) := ⟨⟨_, mem_orbit_self _⟩⟩
  have h1 : (Nat.card (orbit K (Quotient.out o)) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := orbit K (Quotient.out o))).ne'
  have h2 : (Nat.card (stabilizer K (Quotient.out o)) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := stabilizer K (Quotient.out o))).ne'
  rw [← h]; push_cast
  field_simp

end GlobalTheory
