module

public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem eisensteinTameWeightSecond_eq_character_sum :
    ∀ (N : ℕ) (s : ℂ), 0 < N → ∀ B : ℤ,
      tw2 N s B = ((N.totient : ℂ))⁻¹ * ∑ ν : DirichletCharacter ℂ N, (1 - s * ν (-1)) * ch ν B := by
  intro N s hN B
  have : NeZero N := ⟨hN.ne'⟩
  have : NeZero ((Monoid.exponent (ZMod N)ˣ : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  have hφ : ((N.totient : ℂ)) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hN).ne'
  have h1 := DirichletCharacter.sum_characters_eq ℂ (B : ZMod N)
  have h2 := DirichletCharacter.sum_characters_eq ℂ (-(B : ZMod N))
  have h3 : ∑ ν : DirichletCharacter ℂ N, ν (-1) * ν (B : ZMod N)
      = ∑ ν : DirichletCharacter ℂ N, ν (-(B : ZMod N)) := by
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [← map_mul, neg_one_mul]
  have h4 : (-(B : ZMod N) = 1) ↔ ((B : ZMod N) = -1) := neg_eq_iff_eq_neg
  have hsum : ∑ ν : DirichletCharacter ℂ N, (1 - s * ν (-1)) * ch ν B
      = ∑ ν : DirichletCharacter ℂ N, ν (B : ZMod N)
        - s * ∑ ν : DirichletCharacter ℂ N, ν (-1) * ν (B : ZMod N) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    simp only [ch]
    ring
  rw [hsum, h3, h1, h2]
  simp only [tw2, h4]
  field_simp
  split_ifs <;> ring

end GlobalTheory.EisM
