module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXCastAdd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ToLocEqMapToMatrix
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

theorem GlobalTheory.denseGL_completion : ∀ {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k), DenseRange ι → ∀ {A : Type} [Fintype A] [DecidableEq A] {M : ℕ} (e : A ≃ Fin M) (y : GL A k) (V : Set (GL A k)), IsOpen V → y ∈ V → ∃ x : Sp E M ≃ₗ[E] Sp E M, locHom ι e x ∈ V := by
  intro E k _ _ _ _ _ ι hι A _ _ M e y V hV hy
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  let φ : Matrix A A k → Matrix A A k × (Matrix A A k)ᵐᵒᵖ := fun m => (m, MulOpposite.op m⁻¹)
  have hφ : ∀ g : GL A k, φ g.val = Units.embedProduct _ g := by
    intro g
    refine Prod.ext rfl ?_
    simp [φ, Matrix.coe_units_inv]
  obtain ⟨W, hW, rfl⟩ := (Units.isInducing_embedProduct (M := Matrix A A k)).isOpen_iff.1 hV
  have hdet : y.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero
  have hinv : ContinuousAt (fun m : Matrix A A k => m⁻¹) y.val :=
    continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hdet)
  have hφc : ContinuousAt φ y.val :=
    ContinuousAt.prodMk continuousAt_id (MulOpposite.continuous_op.continuousAt.comp hinv)
  have hU : φ ⁻¹' W ∩ {m : Matrix A A k | m.det ≠ 0} ∈ nhds y.val := by
    refine Filter.inter_mem (hφc.preimage_mem_nhds (hW.mem_nhds ?_)) ?_
    · rw [hφ]; exact hy
    · exact (isOpen_compl_singleton.preimage (continuous_id.matrix_det)).mem_nhds hdet
  have hD : DenseRange (fun m : Matrix A A E => m.map ι) :=
    DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => hι))
  obtain ⟨_, ⟨m', rfl⟩, hm'W, hm'd⟩ := Dense.inter_nhds_nonempty hD hU
  have hm'u : IsUnit m'.det := by
    refine isUnit_iff_ne_zero.2 ?_
    intro h0
    apply hm'd
    show (m'.map ι).det = 0
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  let n : Matrix (Fin M) (Fin M) E := m'.submatrix e.symm e.symm
  have hn : IsUnit n.det := by
    simpa [n, Matrix.det_submatrix_equiv_self] using hm'u
  refine ⟨Matrix.toLinearEquiv' n (Matrix.invertibleOfIsUnitDet n hn), ?_⟩
  show Units.embedProduct _ _ ∈ W
  rw [← hφ, locHom_val, GlobalTheory.SymBridge.toLoc_eq_map_toMatrix']
  have h2 : LinearMap.toMatrix' (Matrix.toLinearEquiv' n (Matrix.invertibleOfIsUnitDet n hn)).toLinearMap = n := by
    exact LinearMap.toMatrix'_toLin' n
  rw [h2]
  have h3 : n.submatrix e e = m' := by
    ext i j; simp [n]
  rw [h3]
  exact hm'W
