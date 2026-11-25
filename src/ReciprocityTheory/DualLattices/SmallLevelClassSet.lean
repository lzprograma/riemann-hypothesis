module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.Tactic.Continuity
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

open Polynomial Matrix
open scoped TensorProduct

namespace ReciprocityTheory.PGsh

def stdJ (D : Type*) [CommRing D] (g : ℕ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D :=
  Matrix.fromBlocks 0 (-1) 1 0

abbrev extModR (R K V : Type*) [CommRing R] [Field K] [Algebra R K] [AddCommGroup V]
    [Module K V] : Module R (ExteriorAlgebra K V) :=
  Module.compHom _ (algebraMap R K)

attribute [local instance] extModR

def TruncatedPolynomialStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k H : Type) [Field k] [CharP k p] [CommRing H] [HopfAlgebra k H]
    [FiniteDimensional k H] (d : ℕ) (x : Fin d → H),
    (∀ f ∈ RingHom.ker (Bialgebra.counitAlgHom k H), f ^ p = 0) →
    (∀ i, x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H)) →
    (∀ y ∈ RingHom.ker (Bialgebra.counitAlgHom k H), ∃ l : Fin d → k,
      y - ∑ i, l i • x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H) ^ 2) →
    (∀ l : Fin d → k, ∑ i, l i • x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H) ^ 2 → l = 0) →
    Function.Surjective (MvPolynomial.aeval (R := k) x) ∧
      RingHom.ker (MvPolynomial.aeval (R := k) x) =
        Ideal.span (Set.range fun i => (MvPolynomial.X i : MvPolynomial (Fin d) k) ^ p)

end ReciprocityTheory.PGsh
