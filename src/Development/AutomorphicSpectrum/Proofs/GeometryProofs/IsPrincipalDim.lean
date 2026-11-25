module

import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfProper
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Mathlib.Tactic.Linter.HaveILetI
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SabModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isPrincipal_dim {K : Type} [Field K] {t : SAB H (Sp K)} (_h : IsPrincipal t) :
    ∃ d, SmoothOfRelativeDimension d t.G.hom := by
  apply _root_.GlobalTheory.HeckePoint.exists_dim <;> assumption

def pol {K : Type} [Field K] (t : SAB H (Sp K)) (h : IsPrincipal t) : Out.PolAV (Sp K) where
  A := t.G
  isAb := ⟨inferInstance, t.semi.smooth, h.1, t.semi.geomConnected⟩
  g := (isPrincipal_dim h).choose
  smoothDim := (isPrincipal_dim h).choose_spec
  L := t.PP.L
  isLB := t.PP.isLB
  rigid := ⟨t.PP.rig, t.PP.rigGen⟩
  sym := fun _ => by
    obtain ⟨-, ws, gs', -⟩ := t.sym
    exact ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩
  ample := h.2.1
  ktriv := h.2.2

end GlobalTheory.CompanionTheory.Ar.SabModel
