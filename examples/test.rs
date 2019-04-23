enum Nat {
    Z,
    S(Box<Nat>),
}

fn relation(X : Type) -> Type {
    X * X
}

fn partial_function(X : Type, R : relation X) -> Type {
    (x : X) -> (y1 : X) -> (y2 : X) -> R x y1 -> R x y2 -> (y1 = y2)
}

enum Leq (m : Nat) (n : Nat) {
    ZN : Leq 0 n,
    SS : Leq m n -> Leq (succ m) (succ n),
}

enum TotalRelation {
    Unit,
}

enum EmptyRelation {}