module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordLattice
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AutConjTranslatesDetCharacterMarkings
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.DetUnit

variable {D : D7}

theorem part_mem_intAE {e d : AE D} (he : e * e = e) (hd : finPart D d ∈ intAE D) :
    finPart D (e * d + (1 - e)) ∈ intAE D := by
  have h1 : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he])
  have h2 : finPart D (1 - e) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul]; congr 1; linear_combination he)
  rw [RingHom.map_add (f := _), RingHom.map_mul]
  exact add_mem (GlobalTheory.SplitHeckeLabel.mul_mem_intA h1 hd) h2

end GlobalTheory.Mem.DetUnit
