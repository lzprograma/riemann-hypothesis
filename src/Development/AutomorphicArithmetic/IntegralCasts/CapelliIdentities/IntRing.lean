module

public import Mathlib.NumberTheory.Padics.Complex
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BallRing
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable def UpperTheory.Reformulated.B.CapelliIdentity₂.intRing :
    (p : ℕ) → [Fact (Nat.Prime p)] → Subring ℂ_[p] :=
  fun p _ => UpperTheory.Reformulated.B.ClosedUnitBallSubring.ballRing ℂ_[p]
