module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EllA
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.CountableRationalPointsDoubled
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ProjectedBlockUpperSum
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C5.JC

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ}

def ext0 (L : LD d) (x : Fin L.n → AE F E) (i : Fin d.n) : AE F E :=
  ∑ k, (if L.em k = i then (1 : AE F E) else 0) * x k

variable {L : LD d}

def cv (σ : E →ₐ[F] E) {ι : Type} (x : ι → AE F E) : ι → AE F E := fun r => cA σ (x r)

variable {R : RD d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

theorem inFrame_rat_mem {n : ℕ} {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) {x : G2 σ Y} (hx : x ∈ rat2 σ Y)
    (i j : Fin n ⊕ Fin n) : inFrame b x i j ∈ (inclR (F := F) (E := E) (AF F)).range := by
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 hx)
  have hm : mat2 x = (g.1).map (inclR (F := F) (AF F)) := by
    show (x : GL (Fin n ⊕ Fin n) (AE F E)).1 = _
    rw [← hg]; rfl
  have e : inFrame b x = ((b⁻¹).1 * g.1 * b.1).map (inclR (F := F) (AF F)) := by
    rw [inFrame, hm, Matrix.map_mul, Matrix.map_mul]; rfl
  rw [e, Matrix.map_apply]
  exact ⟨_, rfl⟩

end PositivityTheory.SiegelWeilFormula.Act.C5.JC

end
