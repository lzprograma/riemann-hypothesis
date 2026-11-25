module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSequenceEtaleTateTwistStatement

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Deg2

abbrev T (q : ℕ) : Shv ℤ := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)

def kap (q : ℕ) [NeZero q] : T q ⟶ Gm := (_root_.GlobalTheory.EtC.kummer_sequence q).choose

theorem kap_spec (q : ℕ) [NeZero q] : Mono (kap q) ∧ kap q ≫ ((q : ℤ) • 𝟙 Gm) = 0 ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map (kap q) (show Sec (T q) U from twGen 1 ζ) = unitSec u) ∧ (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map (kap q) a = b) ∧ ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b :=
  (_root_.GlobalTheory.EtC.kummer_sequence q).choose_spec

end UpperTheory.Deg2
