variable {p q: Prop}
-- theorem t1: p -> q -> p :=
--   fun hp: p =>
--   fun hq: q =>
--   show p from hp
theorem t1 (hp: p) (hq: q) : p := hp
#print t1

axiom unsound: False
theorem ex: 1=0 :=
  False.elim unsound

theorem t1' {p q: Prop} (hp: p) (hq: q) : p := hp
#print t1'

theorem t1'' : ∀ {p q: Prop}, p -> q -> p :=
  fun {p q: Prop} (hp: p) (hq: q) => hp

namespace s3
variable {p q : Prop}
theorem t1 : p → q → p := fun (hp : p) (hq : q) => hp
end s3

namespace s4
variable {p q : Prop}
variable (hp: p)

-- this failed to compile
-- theorem t1 : q → p := fun (hq : q) => hp
end s4

namespace s5
theorem t1 (p q : Prop) (hp : p) (hq : q) : p := hp
#print t1

variable (p q r s : Prop)

#check t1 p q                -- p → q → p
#check t1 r s                -- r → s → r
#check t1 (r → s) (s → r)    -- (r → s) → (s → r) → r → s

variable (h : r → s)
#check t1 (r → s) (s → r) h  -- (s → r) → r → s
end s5

namespace s6
variable (p q r s : Prop)

-- subscript s\1 = s₁
theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)
end s6
