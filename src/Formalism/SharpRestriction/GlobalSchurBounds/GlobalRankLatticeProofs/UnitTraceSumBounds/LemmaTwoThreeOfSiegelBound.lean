module

import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmInverseHalfDifferentMulRelativeDifferent
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.DirichletDensity.DirichletDensityProofs.QuadDiscr
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace Formalism.MainNotions.Ext

open Polynomial Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.UnusedSlot33.HK

variable {R : Ranks} (H : Host R)

theorem exists_gen_K : ∃ x : H.K, x ^ 2 = ((-(H.d : ℤ) : ℤ) : H.K) ∧ IntermediateField.adjoin ℚ {x} = ⊤ := by
  have hb2 : H.sqd ^ 2 = ((-(H.d : ℤ) : ℤ) : H.E) := by
    push_cast
    exact H.sqd_sq
  obtain ⟨x, hxdef⟩ : ∃ x : H.K, (x : H.E) = H.sqd :=
    ⟨⟨H.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩, rfl⟩
  refine ⟨x, ?_, gen_top H x hxdef⟩
  apply Subtype.ext
  push_cast
  rw [hxdef, hb2]
  push_cast
  rfl

theorem finrank_K : Module.finrank ℚ H.K = 2 := by
  apply _root_.GlobalTheory.Mem.PerField.finrank_K <;> assumption

theorem no_real_K : IsEmpty (H.K →+* ℝ) := by
  refine ⟨fun σ => ?_⟩
  obtain ⟨x, hx, -⟩ := exists_gen_K H
  have h := congrArg σ hx
  rw [map_pow, map_intCast] at h
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  have h2 := sq_nonneg (σ x)
  rw [h] at h2
  push_cast at h2
  linarith

end Formalism.MainNotions.Ext
