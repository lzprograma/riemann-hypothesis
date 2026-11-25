module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Linter.HaveILetI
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct

namespace GlobalTheory

def valCentreOn {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (S : Subalgebra O A)
    (u : AddValuation A (WithTop ℤ)) (h0 : ∀ a ∈ S, 0 ≤ u a) : Ideal S where
  carrier := {a | 0 < u (a : A)}
  add_mem' := fun {a b} ha hb => by
    have := u.map_add (a : A) (b : A)
    exact lt_of_lt_of_le (lt_min ha hb) this
  zero_mem' := by
    change 0 < u ((0 : S) : A)
    simp
  smul_mem' := fun c a ha => by
    change 0 < u ((c : A) * (a : A))
    rw [u.map_mul]
    exact lt_of_lt_of_le ha (le_add_of_nonneg_left (h0 _ c.2))

theorem mem_valCentreOn {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (S : Subalgebra O A)
    (u : AddValuation A (WithTop ℤ)) (h0 : ∀ a ∈ S, 0 ≤ u a) (a : S) :
    a ∈ valCentreOn S u h0 ↔ 0 < u (a : A) := Iff.rfl

theorem valCentreOn_isPrime {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (S : Subalgebra O A) (u : AddValuation A (WithTop ℤ)) (h0 : ∀ a ∈ S, 0 ≤ u a) :
    (valCentreOn S u h0).IsPrime := by
  refine ⟨?_, fun {a b} hab => ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_valCentreOn]
    simp
  · rw [mem_valCentreOn] at hab
    rw [mem_valCentreOn, mem_valCentreOn]
    by_contra hc
    rw [not_or, not_lt, not_lt] at hc
    rw [MulMemClass.coe_mul, u.map_mul] at hab
    exact absurd hab (not_lt.2 (add_nonpos hc.1 hc.2))

theorem addVal_eq_of_associated_loc {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [Algebra O A] (ζ : Pts O A) (u : AddValuation A (WithTop ℤ))
    (hz : ∀ s : As O A, s ∉ ζ.asIdeal → u (s : A) = 0) (a b : As O A)
    (hab : Associated (algebraMap (As O A) (Loc ζ) a) (algebraMap (As O A) (Loc ζ) b)) :
    u (a : A) = u (b : A) := by
  obtain ⟨w, hw⟩ := hab
  obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.surj ζ.asIdeal.primeCompl (w : Loc ζ)
  have ht : IsUnit (algebraMap (As O A) (Loc ζ) t) := IsLocalization.map_units _ t
  have hs : s ∉ ζ.asIdeal := by
    have h1 : IsUnit (algebraMap (As O A) (Loc ζ) s) := by
      have := w.isUnit.mul ht
      simpa only [hst] using this
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Loc ζ) ζ.asIdeal s).1 h1
  have h2 : algebraMap (As O A) (Loc ζ) (a * s) = algebraMap (As O A) (Loc ζ) (b * t) := by
    rw [map_mul, map_mul, ← hw, mul_assoc]
    exact congrArg _ hst.symm
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists ζ.asIdeal.primeCompl (Loc ζ)).1 h2
  have h3 := congrArg (fun x : As O A => u (x : A)) hc
  simp only [MulMemClass.coe_mul, AddValuation.map_mul] at h3
  rw [hz _ c.2, hz _ hs, hz _ t.2] at h3
  simpa using h3

end GlobalTheory
