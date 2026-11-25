module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLatBack

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatBackSeamLat, Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicLatAtRep

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatBackSeamLat =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatBackSeamLat", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLatBack\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField

namespace GlobalTheory.LatticeBackSeam

theorem latBack_seam_lat : ∀ {D : Formalism.BasicNotions.D7} {X : Formalism.L2.Col.Fields} (s : Formalism.L2.Ker.Seam D X) {n : ℕ}
    (N : Submodule (NumberField.RingOfIntegers (Formalism.L2.Col.Fields.E X)) (Formalism.L2.Col.Sp (Formalism.L2.Col.Fields.E X) n)),
    GlobalTheory.TwU.latBack s (Formalism.L2.Ker.Seam.lat s N) = N := by
  intro D X s n N
  ext y
  rw [GlobalTheory.TwU.mem_latBack]
  constructor
  · intro hy
    have key : ∀ v ∈ Formalism.L2.Ker.Seam.lat s N, ∃ x ∈ N, (fun l => s.iE (x l)) = v := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨x, hx, rfl⟩ := hv
        exact ⟨x, hx, rfl⟩
      | zero => exact ⟨0, N.zero_mem, by funext l; simp⟩
      | add v w _ _ hv hw =>
        obtain ⟨x, hx, rfl⟩ := hv
        obtain ⟨x', hx', rfl⟩ := hw
        exact ⟨x + x', N.add_mem hx hx', by funext l; simp⟩
      | smul r v _ hv =>
        obtain ⟨x, hx, rfl⟩ := hv
        refine ⟨(RingOfIntegers.mapRingEquiv s.iE).symm r • x, N.smul_mem _ hx, ?_⟩
        funext l
        simp [Algebra.smul_def, RingOfIntegers.mapRingEquiv_symm_apply]
    obtain ⟨x, hx, hxy⟩ := key _ hy
    have hxe : x = y := funext fun l => s.iE.injective (congrFun hxy l)
    rw [← hxe]
    exact hx
  · intro hy
    exact Submodule.subset_span ⟨y, hy, rfl⟩

end GlobalTheory.LatticeBackSeam
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatBackSeamLat =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicLatAtRep =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicLatAtRep", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLatBack\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatBackSeamLat\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct
open Classical

noncomputable section
namespace GlobalTheory.TwU

alias latBack_seam_lat := _root_.GlobalTheory.LatticeBackSeam.latBack_seam_lat

end GlobalTheory.TwU
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicLatAtRep =====
