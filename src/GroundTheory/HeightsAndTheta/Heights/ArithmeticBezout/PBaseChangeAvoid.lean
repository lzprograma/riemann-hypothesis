module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ConeBall
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights
open MvPolynomial

theorem BaseChangeAvoid.comap_eq_of_mem_minimalPrimes {K L : Type*} [Field K] [Field L] {n : ℕ}
    (σ : K →+* L) (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    {W : Ideal (MvPolynomial (Fin n) L)} (hW : W ∈ (I.map (MvPolynomial.map σ)).minimalPrimes) :
    W.comap (MvPolynomial.map σ) = I := by
  let : Algebra K L := σ.toAlgebra
  let : Algebra (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L) := algebraMvPolynomial
  have : Module.Flat (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L) :=
    Module.Flat.isBaseChange K _ L _ Algebra.IsPushout.out
  obtain ⟨⟨hWp, hIW⟩, hmin⟩ := hW
  obtain ⟨P, hPW, hP, hPI⟩ := Ideal.exists_ideal_le_liesOver_of_le (q := W.under _) W
    (Ideal.map_le_iff_le_comap.mp hIW)
  obtain rfl := hPW.antisymm (hmin ⟨hP, Ideal.map_le_iff_le_comap.mpr hPI.over.le⟩ hPW)
  exact hPI.over.symm

theorem BaseChangeAvoid.proof : BaseChangeAvoid.Statement := by
  rintro K _ _ n I u σ ⟨hI, _, _⟩ hu W hW h
  apply hu
  rw [← BaseChangeAvoid.comap_eq_of_mem_minimalPrimes σ I (W := W)
    ((Set.Finite.mem_toFinset _).mp (Finsupp.support_onFinset_subset hW)), Ideal.mem_comap]
  simpa [linForm, map_sum] using h

end GroundTheory.Heights₂.Heights
