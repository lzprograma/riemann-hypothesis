module

public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.IdemIntegral

theorem toEAf_mem_of_finPart_mem {D : D7} {w : AE D} (hw : finPart D w ∈ intAE D) :
    toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  show (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) (finPart D w) ∈ _
  generalize finPart D w = z at hw
  induction hw using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    rw [Algebra.TensorProduct.comm_tmul]
    exact GlobalTheory.PlaceDatum.tmul_mem_int ⟨x, rfl⟩ ha
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem finPart_incA_mem {D : D7} (r : 𝓞 D.host.E) : finPart D (incA D (r : D.host.E)) ∈ intAE D := by
  have : finPart D (incA D (r : D.host.E)) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (r : D.host.E) := rfl
  rw [this]
  exact AddSubgroup.subset_closure ⟨1, fun v => by simp, r, rfl⟩

theorem mem_of_idemAt {D : D7} {e : AE D} {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e PP)
    {a : D.host.E} (ha : Formalism.L2.Col.IntAt PP a) :
    toEAf D (e * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨r, s, hs, hsa⟩ := ha
  have hs0 : s ≠ 0 := fun h => hs (h ▸ zero_mem _)
  have hsE : (s : D.host.E) ≠ 0 := by exact_mod_cast hs0
  have ha : a = ((s : D.host.E))⁻¹ * (r : D.host.E) := by
    change (s : D.host.E) * a = (r : D.host.E) at hsa
    rw [← hsa, ← mul_assoc, inv_mul_cancel₀ hsE, one_mul]
  have h1 : finPart D (e * incA D ((s : D.host.E))⁻¹) ∈ intAE D := by
    by_contra h
    exact hs ((he.2 s hs0).2 h)
  rw [ha, (incA D).map_mul, ← mul_assoc, (toEAf D).map_mul]
  exact mul_mem (toEAf_mem_of_finPart_mem h1) (toEAf_mem_of_finPart_mem (finPart_incA_mem r))

end GlobalTheory.IdemIntegral

end
