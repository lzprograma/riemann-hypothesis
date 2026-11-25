module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.CupProductRingLaws

def LeafTwPairExists : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ),
  ∃ μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q (i + j))), IsTwPair μ

def IsOneCocycle (q : ℕ) (E : Spc) (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0) : Prop :=
  ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev (R := ZMod q) α.1 0 0 (by simp) U x = resGen 0 ζ

def LeafOneSpec : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E →
  (∃ α, IsOneCocycle q E α) ∧ ∀ α, IsOneCocycle q E α → one q E = CohomologyClass.mk α

end LateralTheory.E.CupProductRingLaws
