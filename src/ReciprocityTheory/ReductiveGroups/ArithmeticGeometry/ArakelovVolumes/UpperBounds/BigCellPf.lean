module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf Topology

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bigCell_of (hLU : LUStatement (E := E)) : BigCellStatement (E := E) := by
  intro r X x0 hx0 la P hP hvan x hx
  obtain ⟨Δ, zOf, bOf, -, hdense, -, -, hdec, -⟩ := hLU r X x0 hx0
  suffices hopen : IsOpen X.dom by
    by_contra hne
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
      (show IsOpen (X.dom ∩ P ⁻¹' {0}ᶜ) from
        hP.1.continuousOn.isOpen_inter_preimage hopen isOpen_compl_singleton) x ⟨hx, hne⟩
    obtain ⟨y, hy, hΔ⟩ := hdense x hx ε hε
    obtain ⟨hyX, hPy⟩ := hball hy
    obtain ⟨hz, hb, heq⟩ := hdec y hyX hΔ
    exact hPy (show P y = 0 by rw [heq, hP.2 _ hz _ hb, hvan _ hz, mul_zero])
  change IsOpen (GG X.Ψ X.Gm X.p0)
  rw [show GG X.Ψ X.Gm X.p0 = ⋂ τ : X.Ψ, ({x | (mat x τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) by
        ext x
        simp only [GG, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]]
  refine isOpen_iInter_of_finite fun τ => ?_
  have hm : Continuous fun x : Frame X.Ψ r => mat x τ := continuous_apply τ
  refine (isOpen_ne_fun hm.matrix_det continuous_const).inter (isOpen_iInter_of_finite fun i => ?_)
  refine isOpen_lt continuous_const (continuous_const.mul ?_)
  unfold dmin lminor
  refine Complex.continuous_re.comp ((?_ : Continuous fun x : Frame X.Ψ r =>
    gram τ.1 X.Gm (mat x τ)).matrix_submatrix _ _).matrix_det
  refine continuous_matrix fun a b => ?_
  simp only [gram, hermC, col, Matrix.of_apply]
  fun_prop

end ReciprocityTheory.ChartRestriction.G.AR.Up
