import Mathlib.Tactic
import Analysis.Misc.UnitsSystem

open UnitsSystem
variable [UnitsSystem]

/-! Многие алгебраические тождества со {name}`Scalar` можно установить, сначала приведя выражение к
{name}`Formal` с помощью {syntax tactic}`simp [←toFormal_inj]` и протолкнув приведения внутрь, а
затем воспользовавшись {tactic}`ring`. Ниже приведено несколько примеров.

В качестве альтернативы можно «работать в координатах», используя {syntax tactic}`simp [←val_inj]`
вместо {syntax tactic}`simp [←toFormal_inj]`.
-/

/-- {given -show (type := "Dimensions")}`d₁, d₂, d₃` Здесь нужен {name}`Scalar.cast`, поскольку
  {lean}`(d₁+d₂)+d₃` не является определённо равным {lean}`d₁+(d₂+d₃)`. -/
theorem UnitsSystem.Scalar.hMul_assoc {d₁ d₂ d₃ : Dimensions} (a : Scalar d₁) (b : Scalar d₂) (c : Scalar d₃) : 
  a * (b * c) = ((a * b) * c).cast := by
  simp [←toFormal_inj]; ring

theorem UnitsSystem.Scalar.left_distrib {d₁ d₂ : Dimensions} (a : Scalar d₁) (b c : Scalar d₂) : 
  a * (b + c) = (a * b) + (a * c) := by
  simp [←toFormal_inj]; ring

theorem UnitsSystem.Scalar.right_distrib {d₁ d₂ : Dimensions} (a b : Scalar d₁) (c : Scalar d₂) : 
  (a + b) * c = (a * c) + (b * c) := by
  simp [←toFormal_inj]; ring

/-- Здесь нужен {name}`Scalar.cast`, поскольку {lean}`2 • d` не является определённо равным {lean}`d+d`. -/
theorem UnitsSystem.Scalar.sq_add {d : Dimensions} (a b : Scalar d) : (a+b)**2 = a**2 + (2 • a * b).cast + b**2 := by
  simp [←toFormal_inj]; ring

/-- Альтернативное доказательство, основанное на работе в координатах -/
theorem UnitsSystem.Scalar.sq_add' {d : Dimensions} (a b : Scalar d) : (a+b)**2 = a**2 + (2 • a * b).cast + b**2 := by
  simp [←val_inj]; ring
