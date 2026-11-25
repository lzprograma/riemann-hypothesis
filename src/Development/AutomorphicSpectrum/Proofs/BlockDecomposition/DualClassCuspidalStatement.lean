module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassCuspidal

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

theorem _root_.GlobalTheory.T.dual_class_cuspidal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)), x.IsCusp → (dualCl x).IsCusp ∧ (dualCl x).1 = x.1 := by
  first | exact @GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp
