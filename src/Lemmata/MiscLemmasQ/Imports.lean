module

public import Mathlib.Algebra.DualNumber

@[expose] public section

namespace Bl.ThirdBlockLemmaB

noncomputable def goal1 {S : Type} [CommRing S] {A A' : Type} [CommRing A]
    [Algebra S A] [CommRing A'] [Algebra S A'] (φ : A →ₐ[S] A') :
    DualNumber A →ₐ[S] DualNumber A' :=
  DualNumber.lift ⟨((TrivSqZeroExt.inlAlgHom S A' A').comp φ, DualNumber.eps),
    DualNumber.eps_mul_eps, fun _ => DualNumber.commute_eps_left _⟩

end Bl.ThirdBlockLemmaB
