module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitWedge

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Lat

theorem wedge_matrix_mul_family (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ)
    (e : Fin n → V) (P : Matrix (Fin n) (Fin n) Ω) :
    exteriorPower.ιMulti Ω n (fun i => ∑ j, P i j • e j) = P.det • exteriorPower.ιMulti Ω n e := by
  apply _root_.GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame.wedge_rows <;> assumption

end GlobalTheory.CompanionTheory.Ar.Lat
