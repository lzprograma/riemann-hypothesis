module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.DpDual

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.DenseP

variable {n : ℕ}

theorem isUnit_det_of_inG {g : M2 n} (hg : InG g) : IsUnit g.det :=
  _root_.PositivityTheory.Rg.Sw.LVs.isUnit_det_of_InG hg

def mkGR (g : M2 n) (hg : InG g) : GR n :=
  ⟨⟨g, g⁻¹, Matrix.mul_nonsing_inv g (isUnit_det_of_inG hg), Matrix.nonsing_inv_mul g (isUnit_det_of_inG hg)⟩, hg⟩

def IsNElt (g : GR n) : Prop := ∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR g = nU b

def IsMElt (g : GR n) : Prop :=
  ∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR g = fromBlocks a 0 0 (a⁻¹)ᴴ

def IsWElt (g : GR n) : Prop := mR g = JJ n

def GenSt : Prop :=
  ∀ n : ℕ, ∀ g : GR n, g ∈ Subgroup.closure {h : GR n | IsNElt h ∨ IsMElt h ∨ IsWElt h}

end PositivityTheory.Rg.Sw.Glob.DenseP
