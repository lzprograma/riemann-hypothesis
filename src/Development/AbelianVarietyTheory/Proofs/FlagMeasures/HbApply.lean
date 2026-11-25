module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace GlobalTheory.RowsOrb

variable {D : D7} (X : HidaSetting D)

def Wb : Submodule D.host.E (VS D).V where
  carrier := {v | ∀ a, (VS D).hT (X.eX a) v = 0 ∧ (VS D).hT (X.fY a) v = 0}
  add_mem' := by
    intro x y hx hy a
    exact ⟨by rw [map_add (f := _), (hx a).1, (hy a).1, add_zero], by rw [map_add (f := _), (hx a).2, (hy a).2, add_zero]⟩
  zero_mem' := fun a => ⟨map_zero _, map_zero _⟩
  smul_mem' := by
    intro c x hx a
    exact ⟨by rw [map_smul, (hx a).1, smul_zero], by rw [map_smul, (hx a).2, smul_zero]⟩

theorem mem_Wb (v : (VS D).V) : v ∈ Wb X ↔ ∀ a, (VS D).hT (X.eX a) v = 0 ∧ (VS D).hT (X.fY a) v = 0 := Iff.rfl

def hb : Wb X →ₗ⋆[D.host.E] Wb X →ₗ[D.host.E] D.host.E := GlobalTheory.Mass.hRes (VS D).hT (Wb X)

def zb (u : D.what₂.Word) : Wb X := ⟨X.zu u, fun a => X.zu_orth u a⟩

def Ub (u : D.what₂.Word) : Submodule D.host.E (Wb X) :=
  GlobalTheory.Mass.perp (hb X) (Submodule.span D.host.E {zb X u})

def hU (u : D.what₂.Word) : Ub X u →ₗ⋆[D.host.E] Ub X u →ₗ[D.host.E] D.host.E := GlobalTheory.Mass.hRes (hb X) (Ub X u)

def Lmap (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Submodule (𝓞 D.host.E) (Wb X) :=
  GlobalTheory.Mass.latIn (Wb X) (Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X)

abbrev Gz (u : D.what₂.Word) : Subgroup (Formalism.HermitianLatticesTheory.isom (hb X)) :=
  MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom (hb X)) (zb X u)

theorem hb_apply (x y : Wb X) : hb X x y = (VS D).hT (x : (VS D).V) (y : (VS D).V) := rfl

theorem zb_coe (u : D.what₂.Word) : ((zb X u : Wb X) : (VS D).V) = X.zu u := rfl

theorem hU_apply (u : D.what₂.Word) (x y : Ub X u) :
    hU X u x y = (VS D).hT ((x : Wb X) : (VS D).V) ((y : Wb X) : (VS D).V) := rfl

theorem mem_Ub (u : D.what₂.Word) (x : Wb X) : x ∈ Ub X u ↔ (VS D).hT (X.zu u) (x : (VS D).V) = 0 := by
  unfold Ub GlobalTheory.Mass.perp
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro H
    exact H (zb X u) (Submodule.mem_span_singleton_self _)
  · intro H y hy
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply]
    change _ • (VS D).hT (X.zu u) (x : (VS D).V) = 0
    rw [H, smul_zero]

theorem mem_Lmap (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (w : Wb X) :
    w ∈ Lmap X u Λ ↔ (w : (VS D).V) ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X := Iff.rfl

end GlobalTheory.RowsOrb
