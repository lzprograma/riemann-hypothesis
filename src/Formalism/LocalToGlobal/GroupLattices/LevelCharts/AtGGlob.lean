module

import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LocalValuationLogNormsExistence
public import Formalism.SatakeDualWeyl.StatementC
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

noncomputable section

open Matrix NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.G

section Places

variable (F : Type) [Field F] [NumberField F]

theorem finite_placesOver (g : ℕ) (hg : g ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | ((g : ℕ) : 𝓞 F) ∈ v.asIdeal}.Finite := by
  apply _root_.GlobalTheory.CompanionTheory.Ar.Br.Dd.finite_over <;> assumption


open Classical in
def placesOver (g : ℕ) : Finset (HeightOneSpectrum (𝓞 F)) := by
  classical
  exact if h : {v : HeightOneSpectrum (𝓞 F) | ((g : ℕ) : 𝓞 F) ∈ v.asIdeal}.Finite then
    h.toFinset else ∅

theorem mem_placesOver (g : ℕ) (hg : g ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    v ∈ placesOver F g ↔ ((g : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  rw [placesOver, dite_eq_left (finite_placesOver F g hg)]
  simp

end Places

section Prod

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

def prodChar {Z : Type} [CommGroup Z] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F)))
    (lam : ∀ v, v ∈ S → (Uloc v →* Z)) (Up : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (h : ∀ v ∈ S, Up ≤ (Uloc v).comap (bc (prV (E := E) v))) : Up →* Z :=
  ∏ v ∈ S.attach, (lam v.1 v.2).comp
    (((bc (prV (E := E) v.1)).subgroupComap (Uloc v.1)).comp (Subgroup.inclusion (h v.1 v.2)))

end Prod

end Formalism.L2.G
