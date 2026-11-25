module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Ring.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsAlt

@[expose] public section

theorem UpperTheory.Reformulated.B.EqOneOfPowNear.eq_one_of_pow_near :
    ∀ (z : ℂ),
    (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  first
  | exact _root_.GlobalTheory.KeyLemmaTwo.main
  | (apply _root_.GlobalTheory.KeyLemmaTwo.main <;> assumption)
