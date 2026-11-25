module

import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitWedge

public import Mathlib.LinearAlgebra.ExteriorPower.Basic

@[expose] public section

namespace GlobalTheory.CompanionTheory.Exterior

theorem ιMulti_ne_zero_of_linearIndependent :
    ∀ (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ) (e : Fin n → V),
      LinearIndependent Ω e → exteriorPower.ιMulti Ω n e ≠ 0 := @_root_.GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame.wedge_ne_zero

end GlobalTheory.CompanionTheory.Exterior
