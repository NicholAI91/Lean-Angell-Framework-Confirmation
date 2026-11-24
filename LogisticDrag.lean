import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

noncomputable def f (α p x : ℝ) : ℝ := x * (1 - x) - α * x ^ p

theorem zero_boundary (α p : ℝ) (hp : 1 < p) : f α p 0 = 0 := by
  have h : (0 : ℝ) ^ p = 0 := Real.zero_rpow (by linarith)
  unfold f
  rw [h]
  ring

theorem carrying_capacity (α p : ℝ) : f α p 1 = -α := by
  unfold f
  rw [Real.one_rpow]
  ring

theorem equilibrium_manifold (α p x : ℝ) (hx : 0 < x) (h : f α p x = 0) :
    α = (1 - x) / x ^ (p - 1) := by
  unfold f at h
  have hpos : x ^ (p - 1) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  have hsplit : x ^ p = x * x ^ (p - 1) := by
    calc x ^ p = x ^ ((1 : ℝ) + (p - 1)) := by congr 1; ring
      _ = x ^ (1 : ℝ) * x ^ (p - 1) := Real.rpow_add hx _ _
      _ = x * x ^ (p - 1) := by rw [Real.rpow_one]
  rw [hsplit] at h
  have hfac : x * (1 - x - α * x ^ (p - 1)) = 0 := by
    calc x * (1 - x - α * x ^ (p - 1)) = x * (1 - x) - α * (x * x ^ (p - 1)) := by ring
      _ = 0 := h
  cases mul_eq_zero.mp hfac with
  | inl hx0 => linarith
  | inr hsub =>
    have hα : α * x ^ (p - 1) = 1 - x := by linarith
    exact eq_div_of_mul_eq hpos hα

theorem golden_anchor (φ : ℝ) (hφ : φ ^ 2 = φ + 1) (hpos : 1 < φ) :
    (1 - 1 / φ) / (1 / φ) ^ ((2 : ℝ) - 1) = 1 / φ := by
  have hφ0 : φ ≠ 0 := by linarith
  have h1 : ((2 : ℝ) - 1) = (1 : ℝ) := by norm_num
  rw [h1, Real.rpow_one]
  have hstep1 : (1 - 1 / φ) / (1 / φ) = φ - 1 := by
    field_simp
    ring
  have hstep2 : φ - 1 = 1 / φ := by
    apply (eq_div_iff hφ0).mpr
    calc (φ - 1) * φ = φ ^ 2 - φ := by ring
      _ = (φ + 1) - φ := by rw [hφ]
      _ = 1 := by ring
  calc (1 - 1 / φ) / (1 / φ) = φ - 1 := hstep1
    _ = 1 / φ := hstep2
