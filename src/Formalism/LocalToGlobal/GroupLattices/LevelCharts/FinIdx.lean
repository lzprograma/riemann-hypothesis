module

import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharEqOfSplitOfTied
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeComb
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.G

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem finite_setOf_mem_asIdeal {x : 𝓞 F} (hx : x ≠ 0) : {v : HeightOneSpectrum (𝓞 F) | x ∈ v.asIdeal}.Finite := by
  apply _root_.GlobalTheory.HeckeSplit.finite_setOf_mem_asIdeal <;> assumption

end Formalism.L2.G
