module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableAlt

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et

section Semistable

variable (O : Type) [CommRing O] (ϖ : O) (m r : ℕ)

abbrev ssModel : Type :=
  MvPolynomial (Fin m) O ⧸ Ideal.span (Set.singleton ((∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) -
      MvPolynomial.C ϖ))

end Semistable

end GlobalTheory.Et

end
