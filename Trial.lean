class MyGroup (G : Type) where
  mul : G → G → G
  one : G
  inv : G → G

  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  mul_unit_left : ∀ a : G, mul one a = a
  mul_unit_right : ∀ a : G, mul a one = a
  mul_inverse_left : ∀ a : G, mul (inv a) a = one
  mul_inverse_right : ∀ a : G, mul a (inv a) = one


theorem right_cancel {a b c : G} (h : mul a b = mul c a) : b = c := by
