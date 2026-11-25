module

public import Development.EtaleCohomology.EtaleSheaves.LeafOneSpecPf
public import Mathlib.RingTheory.Etale.StandardEtale

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial GlobalTheory.EtC

namespace LateralTheory.E.LeafPrimCoverPf

theorem cyc_cond (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    ∃ p₁ p₂ : A[X], derivative (cyclotomic q A) * p₁ + cyclotomic q A * p₂ = 1 := by
  obtain ⟨h, hh⟩ : cyclotomic q A ∣ X ^ q - 1 := cyclotomic.dvd_X_pow_sub_one q A
  have hd := congrArg derivative hh
  simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, derivative_mul] at hd
  obtain ⟨u, hu⟩ := hq.exists_left_inv
  refine ⟨C u * (h * X), C u * (derivative h * X - C (q : A) * h), ?_⟩
  have hq0 : 0 < q := Nat.pos_of_neZero q
  have e1 : (X : A[X]) ^ q = X ^ (q - 1) * X := by
    rw [← pow_succ, Nat.sub_add_cancel hq0]
  have hc : (C (q : A) : A[X]) = (q : A[X]) := map_natCast C q
  have hcu : C u * C (q : A) = 1 := by rw [← C_mul, hu, C_1]
  rw [e1] at hh
  linear_combination (-(C u * X)) * hd + (C u * C (q:A)) * hh + hcu

def cycPair (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) : StandardEtalePair A where
  f := cyclotomic q A
  monic_f := cyclotomic.monic q A
  g := 1
  cond := by
    obtain ⟨p₁, p₂, h⟩ := cyc_cond A q hq
    exact ⟨p₁, p₂, 0, by simpa using h⟩

theorem etale_adjoin (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    Algebra.Etale A (AdjoinRoot (cyclotomic q A)) := by
  let P := cycPair A q hq
  let e1 : P.Ring ≃ₐ[A] Localization.Away (AdjoinRoot.mk P.f P.g) := P.equivAwayAdjoinRoot
  have hu : IsUnit (AdjoinRoot.mk P.f P.g) := by
    rw [show P.g = 1 from rfl, map_one]; exact isUnit_one
  let e2 : AdjoinRoot P.f ≃ₐ[A] Localization.Away (AdjoinRoot.mk P.f P.g) :=
    (IsLocalization.atUnit (AdjoinRoot P.f) (Localization.Away (AdjoinRoot.mk P.f P.g)) (AdjoinRoot.mk P.f P.g) hu).restrictScalars A
  exact Algebra.Etale.of_equiv (e1.trans e2.symm)

end LateralTheory.E.LeafPrimCoverPf
