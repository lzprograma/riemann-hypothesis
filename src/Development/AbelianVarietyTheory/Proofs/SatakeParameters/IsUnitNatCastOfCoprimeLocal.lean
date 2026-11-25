module

public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MemMoveLevUloc
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel
import Formalism.LocalToGlobal.InertKernelTheory.StatementInt
import Formalism.LocalToGlobal.KernelLattices.TopLawQ
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.LtCNeZero
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix

namespace GlobalTheory.TwV

theorem isUnit_natCast_of_coprime_local {R : Type*} [CommRing R] [IsLocalRing R] {p s : ℕ} (hp : ¬ IsUnit (p : R))
    (hs : Nat.Coprime s p) : IsUnit (s : R) := by
  have hc : IsCoprime (s : R) (p : R) := Nat.Coprime.cast hs
  obtain ⟨a, b, hab⟩ := hc
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := a * (s : R)) (b := b * (p : R)) (by rw [hab]; exact isUnit_one) with h | h
  · exact isUnit_of_mul_isUnit_right h
  · exact absurd (isUnit_of_mul_isUnit_right h) hp

theorem natCast_isUnit_localRing : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (v : X.Pl) (s : ℕ), Nat.Coprime s p → IsUnit (s : X.G.P.W v) :=
  fun X v _ hs => isUnit_natCast_of_coprime_local (X.G.P.setting v).p_unif.not_isUnit hs

end GlobalTheory.TwV
