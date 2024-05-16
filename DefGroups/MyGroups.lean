import Mathlib

class MyGroup (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α

  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ g : α, mul g one = g
  one_mul : ∀ g : α, mul one g = g
  inv_left_mul : ∀ g : α, mul (inv g) g = one

instance hasMulMyGroup {α : Type*} [MyGroup α] : Mul α where
  mul := MyGroup.mul

instance hasOneMyGroup {α : Type*} [MyGroup α] : One α where
  one := MyGroup.one

instance hasInvMyGroup {α : Type*} [MyGroup α] : Inv α where
  inv := MyGroup.inv

namespace MyGroup

theorem one_mul' {α : Type*} [G : MyGroup α] : ∀ g : α, 1 * g = g := by
  exact one_mul

theorem mul_one' {α : Type*} [G : MyGroup α] : ∀ g : α, g * 1 = g := by
  exact mul_one

theorem mul_assoc' {α : Type*} [G : MyGroup α] : ∀ x y z : α, (x * y) * z = x * (y * z) := by
  exact mul_assoc

theorem inv_left_mul' {α : Type*} [G : MyGroup α] : ∀ g : α, g⁻¹ * g = 1 := by
  exact inv_left_mul

theorem inv_inv_one {α : Type*} [G : MyGroup α] : ∀ g : α, (g⁻¹)⁻¹ = g := by
  intro g
  have h : g⁻¹⁻¹ * g⁻¹ = 1 := by exact inv_left_mul g⁻¹
  calc
    _ = g⁻¹⁻¹ * 1 := by simp [mul_one']
    _ = g⁻¹⁻¹ * (g⁻¹ * g) := by simp [inv_left_mul']
    _ = (g⁻¹⁻¹ * g⁻¹) * g := by simp [mul_assoc']
    _ = 1 * g := by rw [h]
    _ = g := by simp [one_mul']

theorem inv_right_mul {α : Type*} [G : MyGroup α] : ∀ g : α, g * g⁻¹ = 1 := by
  intro g
  nth_rewrite 1 [←inv_inv_one g]
  exact inv_left_mul g⁻¹

theorem inv_unique {α : Type*} [G : MyGroup α] : ∀ a b : α, a * b = 1 → b = a⁻¹ := by
  intro a b h
  calc
    _ = 1 * b := by simp [one_mul']
    _ = (a⁻¹ * a) * b := by simp [inv_left_mul']
    _ = a⁻¹ * (a * b) := by simp [mul_assoc']
    _ = a⁻¹ * 1 := by rw [h]
    _ = a⁻¹ := by simp [mul_one']

theorem mul_inv_dist {α : Type*} [G : MyGroup α] : ∀ a b : α, (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  intro a b
  have h : (a * b) * (b⁻¹ * a⁻¹) = 1 := by
    calc
      _ = a * (b * b⁻¹) * a⁻¹ := by simp [mul_assoc']
      _ = a * 1 * a⁻¹ := by simp [inv_right_mul]
      _ = a * a⁻¹ := by simp [mul_one']
      _ = 1 := by simp [inv_right_mul]
  apply inv_unique at h
  symm
  exact h


end MyGroup
