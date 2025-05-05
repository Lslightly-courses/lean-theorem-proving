variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro (
    fun h =>
      ⟨fun w => (h w).left, fun w => (h w).right⟩
  ) (
    fun ⟨l, r⟩ =>
      fun w =>
        ⟨l w, r w⟩
  )
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun h1 =>
    fun h2 =>
      fun w =>
        (h1 w) (h2 w)
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h =>
    h.elim
    (
      fun hpx =>
        fun w =>
          Or.inl (hpx w)
    )
    (
      fun hqx =>
        fun w =>
          Or.inr (hqx w)
    )

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
  fun a =>
    Iff.intro (
      fun h =>
        h a
    ) (
      fun hr =>
        fun _ =>
          hr
    )
open Classical
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro (
    fun h =>
      byCases (
        fun hr => Or.inr hr
      ) (
        fun hnr: ¬ r =>
          have hap: ∀ x, p x :=
            fun x =>
              have hpxr : p x ∨ r := h x
              hpxr.elim
                (
                  fun hpx => hpx
                )
                (
                  fun hr => absurd hr hnr
                )
          Or.inl hap
      )
  ) (
    fun h =>
      h.elim (
        fun hapx =>
          fun x =>
            Or.inl (hapx x)
      ) (
        fun hr =>
          fun _ =>
            Or.inr hr
      )
  )
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro (
    fun h =>
      fun hr =>
        fun x =>
          h x hr
  ) (
    fun hr_apx =>
      fun x =>
        fun hr =>
          (hr_apx hr) x
  )


variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  let hb := h barber
  let hbmp := Iff.mp hb
  let hbmpr := Iff.mpr hb
  let s := shaves barber barber
  byCases (
    fun hs: s =>
      hbmp hs hs
  ) (
    fun hns: ¬ s =>
      hns (hbmpr hns)
  )

def even (n : Nat) : Prop :=
  (Nat.mod n 2) = 0

def prime (n : Nat) : Prop :=
  n != 0 ∧ ∀ (x: Nat), (x < n && 2 <= x) -> Nat.mod n x ≠ 0

def infinitely_many_primes : Prop :=
  ∀ (n1: Nat), prime n1 → ∃ (n2: Nat) , prime n2 ∧ n2 > n1

def Fermat_prime (n : Nat) : Prop :=
  prime (2^(2^n)+1)

def infinitely_many_Fermat_primes : Prop :=
  ∀ (n1: Nat) , Fermat_prime n1 -> ∃ n2: Nat, Fermat_prime n2 ∧ n2 > n1

def goldbach_conjecture : Prop :=
  ∀ x: Nat, x >= 6 ∧ even x → ∃ n1 n2: Nat, ¬ even n1 ∧ ¬ even n2 ∧ prime n1 ∧ prime n2 ∧ n1 + n2 = x

def Goldbach's_weak_conjecture : Prop :=
  ∀ x: Nat, ¬ even x ∧ x > 5 → ∃ x1 x2 x3: Nat , prime x1 ∧ prime x2 ∧ prime x3 ∧ x1+x2+x3=x

def Fermat's_last_theorem : Prop :=
  ∀ n: Nat, n > 2 → ¬ ∃ x y z : Nat, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ x^n + y^n = z^n
