inductive boolean: Type where
inductive integer: Type where
inductive void: Type
inductive pointer (T: Type): Type
inductive array (T: Type) (N: integer): Type
inductive func (T₁: Type) (T₂: Type): Type

axiom truth: boolean
axiom num: integer
axiom mod (E₁: integer) (E₂: integer): integer
axiom index {T: Type} {N: integer} (E₁: array T N) (E₂: integer) : T
axiom deref {T: Type} (E: pointer T): T
axiom funcall {T₁ T₂: Type} (E₁: T₁ → T₂) (E₂: T₁): T₂
axiom assign {T: Type} (id: T) (E: T) : void
axiom ifStmt (E: boolean) (S: void): void
axiom whileStmt (E: boolean) (S: void): void
axiom seqStmt (S₁ S₂: void): void
