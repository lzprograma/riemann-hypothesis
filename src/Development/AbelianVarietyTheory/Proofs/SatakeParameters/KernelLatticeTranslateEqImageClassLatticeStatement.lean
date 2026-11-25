module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeTranslateEqImageClassLattice, Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeTranslateEqImageClassLatticeStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeTranslateEqImageClassLattice =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeTranslateEqImageClassLattice", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie\nimport Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV

namespace GlobalTheory.TwV

theorem latK_lev_rat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i ≤ D.R.m) c (x : UA D i hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi), ∀ (κ : ((St i hi).K ((St i hi).chOf c)).lev.U), x.1 = ratA D.host.F γ * ((St i hi).y c).1 * κ.1 → latK D.sp (gramN D i hi) a x.1 ((St i hi).K ((St i hi).chOf c)).lev.Lb = SDLat.smulLat (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) γ)).toLinearMap) (t.seam.lat ((t.rd u μ).N i c))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ hT' i hi c x γ hγ κ hx
  have hκ : Formalism.MainNotions.G.KAat.HatStab ((St i hi).K ((St i hi).chOf c)).lev.Lb κ.1 := by
    have h1 := (((St i hi).K ((St i hi).chOf c)).lev.U_eq κ.1).1 κ.2
    have h2 := (GlobalTheory.LatticeStabLocal.mem_levelAfL_iff _ _ (sigD D) _ (gramN D i hi) ((St i hi).K ((St i hi).chOf c)).lev.Lb
      ((St i hi).K ((St i hi).chOf c)).lev.Lb_fin κ.1).2 ⟨h1.1, fun v => ((St i hi).K ((St i hi).chOf c)).lev.Uloc_lev v (h1.2 v)⟩
    exact fun z => ((inv_mem h2).2 z).symm
  rw [hx, Formalism.MainNotions.G.KAat.latK_tr _ _ _ _ _ γ hγ hκ, hT'.latK_eq i hi c, ← Submodule.map_comp]
  unfold SDLat.smulLat
  congr 1
  ext v
  simp [Matrix.toLin'_toMatrix']

end GlobalTheory.TwV
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeTranslateEqImageClassLattice =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeTranslateEqImageClassLatticeStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeTranslateEqImageClassLatticeStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeTranslateEqImageClassLattice\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.kernelLattice_translate_eq_image_classLattice : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i ≤ D.R.m) c (x : UA D i hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi), ∀ (κ : ((St i hi).K ((St i hi).chOf c)).lev.U), x.1 = ratA D.host.F γ * ((St i hi).y c).1 * κ.1 → latK D.sp (gramN D i hi) a x.1 ((St i hi).K ((St i hi).chOf c)).lev.Lb = SDLat.smulLat (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) γ)).toLinearMap) (t.seam.lat ((t.rd u μ).N i c))) := by
  first | exact @GlobalTheory.TwV.latK_lev_rat
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeTranslateEqImageClassLatticeStatement =====
