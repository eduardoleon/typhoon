structure PackedPrefixTree :> PREFIX_TREE =
struct
  datatype 'a tree
    = Pure of 'a
    | Two of int * 'a tree * 'a tree
    | ThreeA of int * 'a tree * 'a tree * 'a tree
    | ThreeB of int * 'a tree * 'a tree * 'a tree
    | Four of int * 'a tree * 'a tree * 'a tree * 'a tree
  
  datatype 'a step = L of int * 'a tree | R of int * 'a tree
  
  type 'a leaf = 'a step list
  type 'a node = int * 'a tree * 'a tree * 'a step list
  
  val pure = Pure
  val empty = nil
  val index = #1
  val above = #4
  fun below (n, a, b, _) = (n, a, b, nil)
  
  fun part (m, Two (n, a, b)) = if n = m + 1 then SOME (a, b) else NONE
    | part _ = NONE
  
  fun many (n, ab, cd) =
    case (part (n, ab), part (n, cd)) of
        (NONE, NONE) => Two (n, ab, cd)
      | (NONE, SOME (c, d)) => ThreeA (n, ab, c, d)
      | (SOME (a, b), NONE) => ThreeB (n, a, b, cd)
      | (SOME (a, b), SOME (c, d)) => Four (n, a, b, c, d)
  
  fun find (m, a, sss as L (n, b) :: ss) = if m < n then find (m, many (n, a, b), ss) else (a, sss)
    | find (m, b, sss as R (n, a) :: ss) = if m < n then find (m, many (n, a, b), ss) else (b, sss)
    | find (_, xs, nil) = (xs, nil)
  
  fun insleft (n, xs, ss) =
    let val (xs, ss) = find (n, xs, ss)
    in L (n, xs) :: ss end
  
  fun insright (n, xs, ss) =
    let val (xs, ss) = find (n, xs, ss)
    in R (n, xs) :: ss end
  
  fun update (a, L (n, b) :: ss) = update (many (n, a, b), ss)
    | update (b, R (n, a) :: ss) = update (many (n, a, b), ss)
    | update (xs, nil) = xs
  
  fun delete (L (_, xs) :: ss) = SOME (update (xs, ss))
    | delete (R (_, xs) :: ss) = SOME (update (xs, ss))
    | delete nil = NONE
  
  datatype 'a focus = Leaf of 'a * 'a leaf | Node of 'a node
  
  fun focus (Pure x, ss) = Leaf (x, ss)
    | focus (Two (n, a, b), ss) = Node (n, a, b, ss)
    | focus (ThreeA (n, a, b, c), ss) = Node (n, a, Two (n + 1, b, c), ss)
    | focus (ThreeB (n, a, b, c), ss) = Node (n, Two (n + 1, a, b), c, ss)
    | focus (Four (n, a, b, c, d), ss) = Node (n, Two (n + 1, a, b), Two (n + 1, c, d), ss)
  
  fun root xs = focus (xs, nil)
  fun left (n, a, b, ss) = focus (a, L (n, b) :: ss)
  fun right (n, a, b, ss) = focus (b, R (n, a) :: ss)
  
  fun loop (xs, nil) = xs
    | loop (xs, Pure x :: ss) = loop (x :: xs, ss)
    | loop (xs, Two (_, a, b) :: ss) = loop (xs, b :: a :: ss)
    | loop (xs, ThreeA (_, a, b, c) :: ss) = loop (xs, c :: b :: a :: ss)
    | loop (xs, ThreeB (_, a, b, c) :: ss) = loop (xs, c :: b :: a :: ss)
    | loop (xs, Four (_, a, b, c, d) :: ss) = loop (xs, d :: c :: b :: a :: ss)
  
  fun toAsc (SOME xs) = loop (nil, xs :: nil)
    | toAsc NONE = nil
  
  fun loop (xs, nil) = xs
    | loop (xs, Pure x :: ss) = loop (x :: xs, ss)
    | loop (xs, Two (_, a, b) :: ss) = loop (xs, a :: b :: ss)
    | loop (xs, ThreeA (_, a, b, c) :: ss) = loop (xs, a :: b :: c :: ss)
    | loop (xs, ThreeB (_, a, b, c) :: ss) = loop (xs, a :: b :: c :: ss)
    | loop (xs, Four (_, a, b, c, d) :: ss) = loop (xs, a :: b :: c :: d :: ss)
  
  fun toDesc (SOME xs) = loop (nil, xs :: nil)
    | toDesc NONE = nil
end
