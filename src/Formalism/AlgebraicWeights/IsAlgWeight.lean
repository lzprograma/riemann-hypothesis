module

public import Formalism.SatakeDualWeyl.Statement
public import ReciprocityTheory.Automorphisms.Unitary
public import Formalism.ConjugateSelfDual.StatementRest

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Polynomial Filter

namespace Formalism.AUTREP

section Eig

variable {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M]

def eig (T : Subalgebra k (Module.End k M)) (x : T →ₐ[k] k) : Submodule k M :=
  ⨅ t : T, LinearMap.ker ((t : Module.End k M) - algebraMap k (Module.End k M) (x t))

def mult (T : Subalgebra k (Module.End k M)) (x : T →ₐ[k] k) : ℕ := Module.finrank k (eig T x)

end Eig

section Unitary

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

local notation3 "L⁺" => maximalRealSubfield L

open ReciprocityTheory.Aut

abbrev GAf : Type := ↥(GA L n)

def princAt (v : HeightOneSpectrum (𝓞 L⁺)) (c : ℕ) : Subgroup (GL (Fin n) (v.adicCompletion L⁺)) :=
  Formalism.UG.princ (v.adicCompletionIntegers L⁺).subtype (IsLocalRing.maximalIdeal (v.adicCompletionIntegers L⁺) ^ c)

variable {L n}

variable (L n)

def IsAlgWeight {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) : Prop :=
  FiniteDimensional ℂ W ∧
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Module.Basis ι ℂ W)
    (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ),
    ∀ (γ : GQ L n) (γ₀ : GL (Fin n) L),
      (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) →
      LinearMap.toMatrix b b (ρ γ) = fun i j => MvPolynomial.eval (fun p => p.1 ((γ₀ : Matrix _ _ L) p.2.1 p.2.2)) (P i j)

abbrev Forms {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W)
    (U : Subgroup (GAf L n)) : Submodule ℂ (GAf L n → W) :=
  Formalism.UG.AMF ℂ (GQ L n) U ρ

def tSet (s : SplitPlace L) (ϖ : s.v.adicCompletion L⁺) (j : ℕ) : Set (GAf L n) :=
  {x | TrivOutside (L := L) {s.v} x ∧ ∃ a ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers L⁺).toSubring,
    ∃ b ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers L⁺).toSubring,
      ((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) _) =
        (a : Matrix (Fin n) (Fin n) _) * Formalism.UG.diagJ n ϖ j * (b : Matrix (Fin n) (Fin n) _)}



def IsUnif (v : HeightOneSpectrum (𝓞 L⁺)) (ϖ : v.adicCompletion L⁺) : Prop :=
  Valued.v ϖ = WithZero.exp (-1 : ℤ)

end Unitary

section GeneralLinearIntegers

variable {L : Type} [Field L] [NumberField L]

structure Part (S : Formalism.ConjugateSelfDual.SpectrumFamily) (L : Type) [Field L] [NumberField L] where
  a : ℕ
  π : (S L a).Rep
  d : ℕ
  t : ℤ
  ν : (S L 1).Rep

end GeneralLinearIntegers


end Formalism.AUTREP
